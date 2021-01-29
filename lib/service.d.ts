import type { WinstonLogger } from "./typings/winston";
import { Client, RequestParams } from "@elastic/elasticsearch";
import { Settings, Mappings, Query, Sort, Aggregations } from "./es-types";
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
    window: {
        from: number;
        size: number;
    };
}
export interface Result<T> {
    summary: {
        total: number;
    };
    results: T[];
    buckets: {
        [key: string]: unknown;
    };
}
export declare class ValidationError extends Error {
    context: unknown;
    constructor(message: string, context: unknown);
}
export declare class BulkError extends Error {
    errors: unknown[];
    constructor(message: string, errors: unknown[]);
}
export declare class DeleteByQueryError extends Error {
    query: SimpleQuery;
    constructor(message: string, query: SimpleQuery);
}
export interface Provider<D extends Document> {
    search(params: Params): Promise<Result<D>>;
}
export declare class SearchService<D extends Document> implements Provider<D> {
    private esClient;
    private esConfig;
    private validate;
    private logger;
    constructor({ esClient, esConfig, logger, }: {
        esClient: Client;
        esConfig: Config;
        logger: WinstonLogger;
    });
    private getAction;
    bulk(body: Record<string, unknown>[], refresh?: "wait_for" | false): Promise<void>;
    get(id: D["id"]): Promise<D>;
    index(doc: D, refresh?: "wait_for" | "false"): Promise<void>;
    delete(docId: Document["id"], routing?: string): Promise<void>;
    deleteByQuery(query: SimpleQuery): Promise<void>;
    private checkIfIsBooleanQuery;
    private getshould;
    search(params: Params): Promise<Result<D>>;
    count(body: RequestParams.Count["body"]): Promise<number>;
}
