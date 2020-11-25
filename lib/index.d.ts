import type { WinstonLogger } from "./typings/winston";
import { Client, RequestParams } from "@elastic/elasticsearch";
import { Document, Params, Result, Provider, SimpleQuery } from "./service";
import { Mappings, Settings } from "./es-types";
import { QueryBuilder } from "./query";
import { IndexManager } from "./migration";
export { Document };
export declare class SearchEngine<E, D extends Document> implements Provider<D> {
    private esClient;
    private esConfig;
    private serialize;
    private searchService;
    constructor({ esClient, domain, namespace, settings, mappings, serialize, logger, }: {
        esClient: Client;
        domain: string;
        namespace?: string;
        settings?: Settings;
        mappings?: Mappings;
        serialize: (entity: E) => D;
        logger: WinstonLogger;
    });
    getQueryBuilder(): QueryBuilder<D>;
    getIndexManager(triggerUpdate?: boolean): IndexManager;
    bulk(body: Record<string, unknown>[], refresh: "wait_for" | false): Promise<void>;
    index(entity: E): Promise<void>;
    delete(docId: Document["id"], routing?: string): Promise<void>;
    deleteByQuery(query: SimpleQuery): Promise<void>;
    search(params: Params): Promise<Result<D>>;
    count(body: RequestParams.Count["body"]): Promise<number>;
}
