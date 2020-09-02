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
        [key: string]: any;
    };
}
export declare class ValidationError extends Error {
    context: object;
    constructor(message: string, context: object);
}
export declare class BulkError extends Error {
    errors: object[];
    constructor(message: string, errors: object[]);
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
        logger: any;
    });
    private getAction;
    bulk(body: any, refresh?: "wait_for" | false): Promise<void>;
    get(id: D["id"]): Promise<D>;
    index(doc: D, refresh?: "wait_for" | "false"): Promise<void>;
    delete(docId: Document["id"], routing?: string): Promise<void>;
    private checkIfIsBooleanQuery;
    private getshould;
    search(params: Params): Promise<Result<D>>;
    count(body: RequestParams.Count["body"]): Promise<number>;
}
