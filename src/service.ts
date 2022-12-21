import type { WinstonLogger } from "./typings/winston";
import {
  Client,
  RequestParams,
  ApiResponse,
} from "@opensearch-project/opensearch";
import * as AJV from "ajv";
import {
  Settings,
  Mappings,
  SearchBody,
  UpdateBody,
  Query,
  Sort,
  Aggregations,
  SearchResponse,
} from "./es-types";
import { getValidatorForMapping } from "./validation";

export interface Document {
  id: string;
}

export interface Config {
  alias: string;
  index: string;
  dtype: string;
  mappings: Mappings;
  settings: Settings;
}

export interface SimpleQuery {
  ids: Document["id"][];
}

export interface Params {
  string: string;
  nested: string[];
  filter: Query[];
  grants: Query[];
  facets: Aggregations;
  rerank: Sort[];
  window: { from: number; size: number };
}

export interface Result<T> {
  summary: { total: number };
  results: T[];
  buckets: { [key: string]: unknown };
}

export class ValidationError extends Error {
  public context: unknown;

  public constructor(message: string, context: unknown) {
    super(message);
    this.context = context;
  }
}

export class BulkError extends Error {
  public errors: unknown[];

  public constructor(message: string, errors: unknown[]) {
    super(message);
    this.errors = errors;
  }
}

export class DeleteByQueryError extends Error {
  public query: SimpleQuery;

  public constructor(message: string, query: SimpleQuery) {
    super(message);
    this.query = query;
  }
}

export interface Provider<D extends Document> {
  search(params: Params): Promise<Result<D>>;
}

export class SearchService<D extends Document> implements Provider<D> {
  private esClient: Client;
  private esConfig: Config;
  private validate?: AJV.ValidateFunction;
  private logger: WinstonLogger;

  public constructor({
    esClient,
    esConfig,
    logger,
    shouldPreValidate,
  }: {
    esClient: Client;
    esConfig: Config;
    logger: WinstonLogger;
    shouldPreValidate?: boolean;
  }) {
    this.esClient = esClient;
    this.esConfig = esConfig;
    this.validate = shouldPreValidate
      ? getValidatorForMapping(esConfig.mappings)
      : undefined;
    this.logger = logger;
  }

  private getAction(
    item: Record<string, Record<string, unknown>>
  ): Record<string, unknown> {
    if (item.create) {
      return item.create;
    }
    if (item.delete) {
      return item.delete;
    }
    if (item.index) {
      return item.index;
    }
    if (item.update) {
      return item.update;
    }
    return {};
  }

  public async bulk(
    body: Record<string, unknown>[],
    refresh: "wait_for" | false = false
  ): Promise<void> {
    const response = await this.esClient.bulk({
      index: this.esConfig.alias,
      body,
      refresh,
    });
    if (response.body.errors) {
      // eslint-disable-next-line
      const errors = response.body.items
        // eslint-disable-next-line
        .filter((item: any) => !!this.getAction(item).error)
        // eslint-disable-next-line
        .map((item: any) => this.getAction(item).error);
      throw new BulkError("Error on bulk request", errors);
    }
  }

  public async get(id: D["id"]): Promise<D> {
    const response = await this.esClient.get({
      id,
      index: this.esConfig.alias,
    });
    return response.body._source as D;
  }

  public async index(
    doc: D,
    refresh: "wait_for" | "false" = "false"
  ): Promise<void> {
    try {
      if (this.validate && !this.validate(doc)) {
        throw new ValidationError(
          "Document did not pass mapping pre-validation",
          { doc, mapping: this.esConfig.mappings, errors: this.validate.errors }
        );
      }
      await this.esClient.update({
        id: `${doc.id}`,
        index: this.esConfig.alias,
        body: { doc, doc_as_upsert: true },
        retry_on_conflict: 10,
        refresh,
      } as RequestParams.Update<UpdateBody<D>>);
    } catch (error) {
      this.logger.error(`Error on indexing document ${doc.id}`, error);
    }
  }

  public async delete(
    docId: Document["id"],
    routing?: string,
    refresh: "wait_for" | boolean = false
  ): Promise<void> {
    try {
      await this.esClient.delete({
        id: `${docId}`,
        index: this.esConfig.alias,
        type: this.esConfig.dtype,
        routing,
        refresh,
      } as RequestParams.Delete);
    } catch (error) {
      this.logger.error(`Error on deleting document ${docId}`, error);
    }
  }

  public async deleteByQuery(query: SimpleQuery): Promise<void> {
    try {
      await this.esClient.deleteByQuery({
        index: this.esConfig.alias,
        body: { query: { terms: { id: query.ids } } },
      } as RequestParams.DeleteByQuery<SearchBody>);
    } catch (error) {
      const message = `Error on deleting documents by query ${JSON.stringify(
        query
      )}`;
      this.logger.error(message, error);
      throw new DeleteByQueryError(message, query);
    }
  }

  private checkIfIsBooleanQuery(query: string): boolean {
    return query.includes(":");
  }

  private getshould(string: string, nested: string[]): Query | Query[] {
    if (!string) return { match_all: {} };

    const isBooleanQuery = this.checkIfIsBooleanQuery(string);
    if (isBooleanQuery) {
      return {
        bool: {
          should: [
            { query_string: { query: string } },
            ...nested.map((path) => ({
              nested: { path, query: { query_string: { query: string } } },
            })),
          ],
        },
      };
    }

    return [
      {
        match_phrase_prefix: { name: string },
      },
      {
        match: { "code.text": string },
      },
      {
        nested: {
          path: "positions",
          query: { match: { "positions.code.text": string } },
        },
      },
    ];
  }

  public async search(params: Params): Promise<Result<D>> {
    const { string, nested, filter, grants, facets, rerank, window } = params;
    try {
      const searchBody: SearchBody = {
        query: {
          bool: {
            should: this.getshould(string, nested),
            minimum_should_match: 1,
            filter: {
              bool: {
                must: filter,
                should: grants,
                minimum_should_match: grants.length > 0 ? 1 : 0,
              },
            },
          },
        },
        sort: rerank,
        aggs: facets,
      };

      const response: ApiResponse<SearchResponse<D>> =
        await this.esClient.search({
          index: this.esConfig.alias,
          type: this.esConfig.dtype,
          body: searchBody,
          from: window.from,
          size: window.size,
        } as RequestParams.Search<SearchBody>);

      return {
        summary: { total: response.body.hits.total.value },
        results: response.body.hits.hits.map((hit): D => hit._source),
        buckets: response.body.aggregations || {},
      };
    } catch (error) {
      this.logger.error("Unexpected search error", error);
      return { summary: { total: 0 }, results: [], buckets: {} };
    }
  }

  public async count(body: RequestParams.Count["body"]): Promise<number> {
    try {
      const response = await this.esClient.count({
        index: this.esConfig.alias,
        type: this.esConfig.dtype,
        body,
      } as RequestParams.Count);
      return response.body.count as number;
    } catch (error) {
      if (
        error instanceof Error &&
        error.message === "search_phase_execution_exception"
      )
        return 0;
      throw error;
    }
  }
}
