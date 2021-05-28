import type { WinstonLogger } from "./typings/winston";
import { Client, RequestParams } from "@elastic/elasticsearch";

import {
  Config,
  Document,
  Params,
  Result,
  Provider,
  SearchService,
  SimpleQuery,
} from "./service";
import { Mappings, Settings } from "./es-types";
import { QueryBuilder } from "./query";
import { IndexManager } from "./migration";

export { Document };

export class SearchEngine<E, D extends Document> implements Provider<D> {
  private esClient: Client;
  private esConfig: Config;
  private serialize: (entity: E) => D;
  private searchService: SearchService<D>;

  public constructor({
    esClient,
    domain,
    namespace,
    settings,
    mappings,
    serialize,
    logger,
    shouldPreValidate,
  }: {
    esClient: Client;
    domain: string;
    namespace?: string;
    settings?: Settings;
    mappings?: Mappings;
    serialize: (entity: E) => D;
    logger: WinstonLogger;
    shouldPreValidate?: boolean;
  }) {
    const actualPrefix = namespace ? `${namespace}_` : "";
    const esConfig = {
      alias: `${actualPrefix}${domain}`,
      index: `${actualPrefix}${domain}_index`,
      dtype: "_doc",
      settings: settings || {},
      mappings: mappings || {},
    };

    this.esClient = esClient;
    this.esConfig = esConfig;
    this.serialize = serialize;
    this.searchService = new SearchService({
      esClient,
      esConfig,
      logger,
      shouldPreValidate,
    });
  }

  public getQueryBuilder(): QueryBuilder<D> {
    return new QueryBuilder({ docsProvider: this });
  }

  public getIndexManager(triggerUpdate = false): IndexManager {
    return new IndexManager({
      esClient: this.esClient,
      esConfig: this.esConfig,
      triggerUpdate,
    });
  }

  public async bulk(
    body: Record<string, unknown>[],
    refresh: "wait_for" | false
  ): Promise<void> {
    await this.searchService.bulk(body, refresh);
  }

  public index(entity: E, refresh?: "wait_for"): Promise<void> {
    return this.searchService.index(this.serialize(entity), refresh);
  }

  public delete(docId: Document["id"], routing?: string): Promise<void> {
    return this.searchService.delete(docId, routing);
  }

  public deleteByQuery(query: SimpleQuery): Promise<void> {
    return this.searchService.deleteByQuery(query);
  }

  public search(params: Params): Promise<Result<D>> {
    return this.searchService.search(params);
  }

  public count(body: RequestParams.Count["body"]): Promise<number> {
    return this.searchService.count(body);
  }
}
