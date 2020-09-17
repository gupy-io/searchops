import { Client } from "@elastic/elasticsearch";
import type { Logger } from "winston";
import { random } from "faker";

import { Config } from "../service";

export function getRandomSnakeCase(): string {
  const word = random.word().replace(/\W/g, "_").toLowerCase();
  return `${word}_${new Date().valueOf()}`;
}

export function getTestClient(logger?: Logger): Client {
  const elasticHost = process.env.ELASTIC_HOST ?? "localhost";
  const elasticPort = process.env.ELASTIC_PORT ?? "9200";
  const esClient: Client = new Client({
    node: `http://${elasticHost}:${elasticPort}`,
  });
  if (logger) {
    esClient.on("response", (error, result): void => {
      if (error) logger.error(JSON.stringify(result, null, 2));
      else logger.debug(JSON.stringify(result, null, 2));
    });
  }
  return esClient;
}

export function getRandomConfig(): Config {
  return {
    index: getRandomSnakeCase(),
    alias: getRandomSnakeCase(),
    dtype: "_doc",
    settings: {
      number_of_shards: "1",
      number_of_replicas: "1",
      refresh_interval: "1ms",
    },
    mappings: {},
  };
}

export type RecursivePartial<T> = {
  [P in keyof T]?: RecursivePartial<T[P]>;
};
