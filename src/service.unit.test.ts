import sinon from 'sinon';
import { expect } from 'chai';
import { Client } from '@elastic/elasticsearch';
import { SearchService, Config } from './service';

describe('SearchService', () => {
  context('bulk', () => {
    const bulk = sinon.fake.returns({ body: { errors: false } });
    const esConfig = {
      alias: 'abc',
      mappings: {},
    };

    it('delegates to esClient', async () => {
      const searchService = new SearchService({
        esClient: ({ bulk } as unknown) as Client,
        esConfig: (esConfig as unknown) as Config,
      });
      const document = 'document';
      await searchService.bulk(document);
      expect(bulk.called).to.be.true;
      expect(bulk.calledWith({
        index: esConfig.alias,
        body: document,
        refresh: 'false',
      })).to.be.true;
    });

    it('can ask for ES to wait document to be available', async () => {
      const searchService = new SearchService({
        esClient: ({ bulk } as unknown) as Client,
        esConfig: (esConfig as unknown) as Config,
      });
      const document = 'document';
      await searchService.bulk(document, 'wait_for');
      expect(bulk.called).to.be.true;
      expect(bulk.calledWith({
        index: esConfig.alias,
        body: document,
        refresh: 'wait_for',
      })).to.be.true;
    });

    it('throws if esClient.bulk informs error', async () => {
      const searchService = new SearchService({
        esClient: ({ bulk: () => ({
          body: {
            errors: true,
            items: [
              { create: { error: { type: 'a' } } },
              { delete: { error: { type: 'b' } } },
              { index: { error: { type: 'c' } } },
              { update: { error: { type: 'd' } } },
              { somethingElse: { error: { type: 'e' } } },
              { update: { } },
            ],
          },
        }) } as unknown) as Client,
        esConfig: (esConfig as unknown) as Config,
      });
      const document = 'document';
      try {
        await searchService.bulk(document);
      } catch (error) {
        expect(error.message).to.equal('Error on bulk request');
        expect(error.errors).to.deep.equal([
          { type: 'a' },
          { type: 'b' },
          { type: 'c' },
          { type: 'd' },
        ]);
      }
    });
  });
});
