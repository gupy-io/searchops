import { Client } from '@elastic/elasticsearch';
import { random } from 'faker';

import { logger } from '../../logging';
import { config } from '../../private-api-config';
import { Config } from '../service';


export function getRandomSnakeCase(): string {
  return random.word().replace(/\W/g, '_').toLowerCase();
}

export function getTestClient(): Client {
  const { elasticHost, elasticPort } = config;
  const esClient: Client = new Client({ node: `http://${elasticHost}:${elasticPort}` });
  esClient.on('response', (error, result): void => {
    if (error) logger.error(JSON.stringify(result, null, 2));
    else logger.silly(JSON.stringify(result, null, 2));
  });
  return esClient;
}

export function getRandomConfig(): Config {
  return {
    index: getRandomSnakeCase(),
    alias: getRandomSnakeCase(),
    dtype: '_doc',
    settings: { number_of_shards: '1', number_of_replicas: '1', refresh_interval: '1ms' },
    mappings: {},
  };
}

export function collectDeepMembers(object: object, structure: object): object {
  if (typeof structure !== 'object') return object;
  return Object.keys(structure).reduce((sub, key) => ({
    ...sub, [key]: collectDeepMembers(object[key], structure[key]),
  }), {});
}
