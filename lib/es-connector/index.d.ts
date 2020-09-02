import { Client } from "@elastic/elasticsearch";
import { Logger } from "winston";
interface ElasticsearchConfig {
    elasticHost: string;
    elasticPort: number;
    elasticProtocol: string;
}
interface DatabaseInput {
    elasticConfig: ElasticsearchConfig;
    logger: Logger;
}
export declare const createElasticsearch: ({ elasticConfig, logger, }: DatabaseInput) => Client | null;
export {};
