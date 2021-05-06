import awsSdk from "aws-sdk";
import { Client } from "@elastic/elasticsearch";
import type { WinstonLogger } from "../typings/winston";
import { AwsSignedConnection, UnsignedConnection } from "./aws";

interface ElasticsearchConfig {
  elasticHost: string;
  elasticPort: number;
  elasticProtocol: string;
}

interface DatabaseInput {
  elasticConfig: ElasticsearchConfig;
  logger: WinstonLogger;
}

export const createElasticsearch = ({
  elasticConfig,
  logger,
}: DatabaseInput): Client => {
  const host = elasticConfig.elasticHost || "localhost";
  const port = elasticConfig.elasticPort || 9200;
  const protocol = elasticConfig.elasticProtocol || "http";
  
  const client = new Client({
    Connection: awsSdk.config.credentials
      ? AwsSignedConnection
      : UnsignedConnection,
    node: `${protocol}://${host}:${port}`,
  });
  client.on("response", (_error, result) => {
    logger.silly(JSON.stringify(result, null, 2));
    if (result && result.warnings) {
      logger.warn(result.warnings);
    }
  });
  return client;
};
