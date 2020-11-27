import { Client } from "@elastic/elasticsearch";
import type { WinstonLogger } from "../typings/winston";
interface ElasticsearchConfig {
    elasticHost: string;
    elasticPort: number;
    elasticProtocol: string;
}
interface DatabaseInput {
    elasticConfig: ElasticsearchConfig;
    logger: WinstonLogger;
}
export declare const createElasticsearch: ({ elasticConfig, logger, }: DatabaseInput) => Client;
export {};
