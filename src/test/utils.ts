import { Client } from "@elastic/elasticsearch";
import { random } from "faker";

import { Config } from "../service";

export function getRandomSnakeCase(): string {
  return random.word().replace(/\W/g, "_").toLowerCase();
}

export function getTestClient(): Client {
  const elasticHost = process.env.ELASTIC_HOST ?? "localhost";
  const elasticPort = process.env.ELASTIC_PORT ?? "9200";
  const esClient: Client = new Client({
    node: `http://${elasticHost}:${elasticPort}`,
  });
  esClient.on("response", (error, result): void => {
    if (error) console.log(JSON.stringify(result, null, 2));
  });
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

export function collectDeepMembers(object: any, structure: any): object {
  if (typeof structure !== "object") return object;
  return Object.keys(structure).reduce(
    (sub, key) => ({
      ...sub,
      [key]: collectDeepMembers(object[key], structure[key]),
    }),
    {}
  );
}
