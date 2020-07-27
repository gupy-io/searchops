/* eslint-disable @typescript-eslint/camelcase */
// Elasticsearch types follow the snake_case JSON convention
// Document is in _source, plus other metadata fields with _

import { Client, events } from '@elastic/elasticsearch';
import { expect } from 'chai';
import faker from 'faker';
import sinon from 'sinon';

import { logger } from '../logging';
import { environment } from '../private-api-config/environmentVariables';

import { Config } from './service';
import { IndexManager } from './migration';

const randomSnakeCase = (): string => faker.random.word().replace(/\W/g, '_').toLowerCase();

describe('Elasticsearch Index Migration @integration tests', () => {
  const sandbox = sinon.createSandbox();

  const { elasticHost, elasticPort } = environment;
  const esClient: Client = new Client({ node: `http://${elasticHost}:${elasticPort}` });
  esClient.on(events.RESPONSE, (error, result): void => {
    if (error) logger.error(JSON.stringify(result, null, 2));
    else logger.silly(JSON.stringify(result, null, 2));
  });

  const esConfig: Config = {
    index: randomSnakeCase(),
    alias: randomSnakeCase(),
    dtype: randomSnakeCase(),
    settings: { number_of_shards: '1', number_of_replicas: '1', refresh_interval: '1ms' },
    mappings: { properties: { code: { type: 'text' } } },
  };

  const manager = new IndexManager({ esClient, esConfig });

  beforeEach(() => {
    sandbox.spy(esClient, 'reindex');
    sandbox.spy(esClient, 'updateByQuery');
    sandbox.spy(esClient.indices, 'create');
    sandbox.spy(esClient.indices, 'delete');
    sandbox.spy(esClient.indices, 'putMapping');
    sandbox.spy(esClient.indices, 'putSettings');
    sandbox.spy(esClient.indices, 'updateAliases');
  });
  afterEach(async () => {
    await manager.deleteIndex();
    sandbox.restore();
  });

  context('when aliased index does not exist', () => {
    beforeEach(async () => {
      expect(await manager.existsIndex()).to.be.false;
      expect(await manager.existsAlias()).to.be.false;
    });
    it('should create aliased index with settings and mappings', async () => {
      await manager.migrate();

      expect(await manager.existsIndex()).to.be.true;
      expect(await manager.existsAlias()).to.be.true;
      expect(await manager.getSettings()).to.deep.include(esConfig.settings);
      expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
    });
  });

  context('when aliased index already exists', () => {
    let initialVersion: string;

    beforeEach(async () => {
      await manager.migrate();
      initialVersion = await manager.getVersion();
      await esClient.index({
        index: esConfig.index,
        body: { code: '123/456' },
        refresh: 'wait_for',
      });
    });

    context('when settings and mappings are still the same', () => {
      beforeEach(async () => {
        expect(await manager.getSettings()).to.deep.include(esConfig.settings);
        expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
        sandbox.resetHistory();
      });
      it('should perform no maintenance', async () => {
        await manager.migrate();

        expect(await manager.getVersion()).to.equal(initialVersion);
        expect(esClient.reindex).to.not.have.been.called;
        expect(esClient.updateByQuery).to.not.have.been.called;
        expect(esClient.indices.create).to.not.have.been.called;
        expect(esClient.indices.delete).to.not.have.been.called;
        expect(esClient.indices.putMapping).to.not.have.been.called;
        expect(esClient.indices.putSettings).to.not.have.been.called;
        expect(esClient.indices.updateAliases).to.not.have.been.called;
      });
    });

    context('when dynamic mappings have changed', () => {
      const subSandbox = sinon.createSandbox();
      beforeEach(() => {
        subSandbox.replace(esConfig, 'mappings', {
          properties: {
            ...esConfig.mappings.properties,
            code: { type: 'text', fields: { keyword: { type: 'keyword' } } },
          },
        });
      });
      afterEach(() => {
        subSandbox.restore();
      });
      it('should update mappings without recreating index', async () => {
        await manager.migrate();
        expect(await manager.getVersion()).to.equal(initialVersion);
        expect(await manager.getSettings()).to.deep.include(esConfig.settings);
        expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
      });
    });

    context('when dynamic settings have changed', () => {
      const subSandbox = sinon.createSandbox();
      beforeEach(() => {
        subSandbox.replace(esConfig, 'settings', {
          ...esConfig.settings,
          refresh_interval: '2ms',
        });
      });
      afterEach(() => {
        subSandbox.restore();
      });
      it('should update settings without recreating index', async () => {
        await manager.migrate();
        expect(await manager.getVersion()).to.equal(initialVersion);
        expect(await manager.getSettings()).to.deep.include(esConfig.settings);
        expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
      });
    });
  });
});
