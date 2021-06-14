import { jest, expect, describe, describe as context, it } from "@jest/globals";
import { createLogger } from "winston";
import { Client } from "@elastic/elasticsearch";
import {
  SearchService,
  Config,
  BulkError,
  DeleteByQueryError,
} from "./service";
import * as validations from "./validation";

const logger = createLogger({ silent: true });

describe("SearchService", () => {
  const esConfig = {
    alias: "abc",
    mappings: {},
  };

  context("index", () => {
    afterEach(() => {
      jest.restoreAllMocks();
    });

    it("Should pre validate mapping when shouldPreValidate is true", async () => {
      const spy = jest.spyOn(validations, "getValidatorForMapping");
      const searchService = new SearchService({
        esClient: {} as unknown as Client,
        esConfig: esConfig as unknown as Config,
        logger,
        shouldPreValidate: true,
      });
      const document = { id: "1" };
      await searchService.index(document);
      expect(spy).toHaveBeenCalled();
    });

    it("Should not pre validate mapping when shouldPreValidate is false", async () => {
      const spy = jest.spyOn(validations, "getValidatorForMapping");
      const searchService = new SearchService({
        esClient: {} as unknown as Client,
        esConfig: esConfig as unknown as Config,
        logger,
        shouldPreValidate: false,
      });
      const document = { id: "1" };
      await searchService.index(document);
      expect(spy).not.toHaveBeenCalled();
    });
  });

  context("deleteByQuery", () => {
    it("throws when deleteByQuery fails", async () => {
      const searchService = new SearchService({
        esClient: {
          deleteByQuery: () => {
            throw new Error();
          },
        } as unknown as Client,
        esConfig: esConfig as unknown as Config,
        logger,
      });
      const query = { ids: ["1"] };
      try {
        await searchService.deleteByQuery(query);
        throw new Error("failed");
      } catch (e: unknown) {
        expect(e).toBeInstanceOf(DeleteByQueryError);
        if (e instanceof DeleteByQueryError) {
          expect(e.message).toEqual(
            'Error on deleting documents by query {"ids":["1"]}'
          );
        }
      }
    });
  });

  context("bulk", () => {
    const bulk = jest.fn().mockReturnValue({ body: { errors: false } });

    it("delegates to esClient", async () => {
      const searchService = new SearchService({
        esClient: { bulk } as unknown as Client,
        esConfig: esConfig as unknown as Config,
        logger,
      });
      const document = [{}];
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
        esClient: { bulk } as unknown as Client,
        esConfig: esConfig as unknown as Config,
        logger,
      });
      const document = [{}];
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
        esClient: {
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
        } as unknown as Client,
        esConfig: esConfig as unknown as Config,
        logger,
      });
      const document = [{}];
      try {
        await searchService.bulk(document);
      } catch (e: unknown) {
        expect(e).toBeInstanceOf(BulkError);
        if (e instanceof BulkError) {
          expect(e.message).toEqual("Error on bulk request");
          expect(e.errors).toEqual([
            { type: "a" },
            { type: "b" },
            { type: "c" },
            { type: "d" },
          ]);
        }
      }
    });
  });
});
