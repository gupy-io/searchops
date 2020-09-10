import { jest, expect, describe, describe as context, it } from "@jest/globals";
import { Client } from "@elastic/elasticsearch";
import { SearchService, Config } from "./service";

const fakeLogger = {
  // eslint-disable-next-line no-console
  error: console.log,
};

describe("SearchService", () => {
  context("bulk", () => {
    const bulk = jest.fn().mockReturnValue({ body: { errors: false } });
    const esConfig = {
      alias: "abc",
      mappings: {},
    };

    it("delegates to esClient", async () => {
      const searchService = new SearchService({
        esClient: ({ bulk } as unknown) as Client,
        esConfig: (esConfig as unknown) as Config,
        logger: fakeLogger,
      });
      const document = "document";
      await searchService.bulk(document);
      expect(bulk).toHaveBeenCalled();
      expect(bulk).toHaveBeenCalledWith({
        index: esConfig.alias,
        body: document,
        refresh: false,
      });
    });

    it("can ask for ES to wait document to be available", async () => {
      const searchService = new SearchService({
        esClient: ({ bulk } as unknown) as Client,
        esConfig: (esConfig as unknown) as Config,
        logger: fakeLogger,
      });
      const document = "document";
      await searchService.bulk(document, "wait_for");
      expect(bulk).toHaveBeenCalled();
      expect(bulk).toHaveBeenCalledWith({
        index: esConfig.alias,
        body: document,
        refresh: "wait_for",
      });
    });

    it("throws if esClient.bulk informs error", async () => {
      const searchService = new SearchService({
        esClient: ({
          bulk: () => ({
            body: {
              errors: true,
              items: [
                { create: { error: { type: "a" } } },
                { delete: { error: { type: "b" } } },
                { index: { error: { type: "c" } } },
                { update: { error: { type: "d" } } },
                { somethingElse: { error: { type: "e" } } },
                { update: {} },
              ],
            },
          }),
        } as unknown) as Client,
        esConfig: (esConfig as unknown) as Config,
        logger: fakeLogger,
      });
      const document = "document";
      try {
        await searchService.bulk(document);
      } catch (error) {
        expect(error.message).toEqual("Error on bulk request");
        expect(error.errors).toEqual([
          { type: "a" },
          { type: "b" },
          { type: "c" },
          { type: "d" },
        ]);
      }
    });
  });
});
