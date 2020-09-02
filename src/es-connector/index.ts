import awsSdk from "aws-sdk";
import { Client } from "@elastic/elasticsearch";
import { Logger } from "winston";
import { AwsSignedConnection, UnsignedConnection } from "./aws";

let client: Client;

interface ElasticsearchConfig {
  elasticHost: string;
  elasticPort: number;
  elasticProtocol: string;
}

interface DatabaseInput {
  elasticConfig: ElasticsearchConfig;
  logger: Logger;
}

export const createElasticsearch = ({
  elasticConfig,
  logger,
}: DatabaseInput): Client | null => {
  if (!client) {
    const host = elasticConfig.elasticHost || "localhost";
    const port = elasticConfig.elasticPort || 9200;
    const protocol = elasticConfig.elasticProtocol || "http";

    client = new Client({
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
  }
  return client;
};
