import {
  jest,
  expect,
  describe,
  it,
  beforeEach,
  afterEach,
} from "@jest/globals";
import faker from "faker";

import { getTestClient } from "./test/utils";
import { Config } from "./service";
import { IndexManager } from "./migration";

const randomSnakeCase = (): string =>
  faker.random.word().replace(/\W/g, "_").toLowerCase();

describe("Elasticsearch Index Migration @integration tests", () => {
  const esClient = getTestClient();
  const esConfig: Config = {
    index: randomSnakeCase(),
    alias: randomSnakeCase(),
    dtype: randomSnakeCase(),
    settings: {
      number_of_shards: "1",
      number_of_replicas: "1",
      refresh_interval: "1ms",
    },
    mappings: { properties: { code: { type: "text" } } },
  };

  const manager = new IndexManager({ esClient, esConfig });

  beforeEach(() => {
    jest.spyOn(esClient, "reindex");
    jest.spyOn(esClient, "updateByQuery");
    jest.spyOn(esClient.indices, "create");
    jest.spyOn(esClient.indices, "delete");
    jest.spyOn(esClient.indices, "putMapping");
    jest.spyOn(esClient.indices, "putSettings");
    jest.spyOn(esClient.indices, "updateAliases");
  });
  afterEach(async () => {
    await manager.deleteIndex();
    jest.restoreAllMocks();
  });

  describe("when aliased index does not exist", () => {
    beforeEach(async () => {
      expect(await manager.existsIndex()).toBeFalsy();
      expect(await manager.existsAlias()).toBeFalsy();
    });
    it("should create aliased index with settings and mappings", async () => {
      await manager.migrate();

      expect(await manager.existsIndex()).toBeTruthy();
      expect(await manager.existsAlias()).toBeTruthy();
      expect(await manager.getSettings()).toEqual(esConfig.settings);
      expect(await manager.getMappings()).toEqual(esConfig.mappings);
    });
  });

  describe("when aliased index already exists", () => {
    let initialVersion: string;

    beforeEach(async () => {
      await manager.migrate();
      initialVersion = await manager.getVersion();
      await esClient.index({
        index: esConfig.index,
        body: { code: "123/456" },
        refresh: "wait_for",
      });
    });

    describe("when settings and mappings are still the same", () => {
      beforeEach(async () => {
        expect(await manager.getSettings()).toEqual(esConfig.settings);
        expect(await manager.getMappings()).toEqual(esConfig.mappings);
        jest.resetAllMocks();
      });
      it("should perform no maintenance", async () => {
        await manager.migrate();

        expect(await manager.getVersion()).toEqual(initialVersion);
        expect(esClient.reindex).not.toHaveBeenCalled();
        expect(esClient.updateByQuery).not.toHaveBeenCalled();
        expect(esClient.indices.create).not.toHaveBeenCalled();
        expect(esClient.indices.delete).not.toHaveBeenCalled();
        expect(esClient.indices.putMapping).not.toHaveBeenCalled();
        expect(esClient.indices.putSettings).not.toHaveBeenCalled();
        expect(esClient.indices.updateAliases).not.toHaveBeenCalled();
      });
    });

    describe("when dynamic mappings have changed", () => {
      beforeEach((): void => {
        esConfig.mappings = {
          properties: {
            ...esConfig.mappings.properties,
            code: { type: "text", fields: { keyword: { type: "keyword" } } },
          },
        };
      });
      afterEach(() => {
        jest.restoreAllMocks();
      });
      it("should update mappings without recreating index", async () => {
        await manager.migrate();
        expect(await manager.getVersion()).toEqual(initialVersion);
        expect(await manager.getSettings()).toEqual(esConfig.settings);
        expect(await manager.getMappings()).toEqual(esConfig.mappings);
      });
    });

    describe("when dynamic settings have changed", () => {
      beforeEach(() => {
        esConfig.settings = {
          ...esConfig.settings,
          refresh_interval: "2ms",
        };
      });
      afterEach(() => {
        jest.resetAllMocks();
      });
      it("should update settings without recreating index", async () => {
        await manager.migrate();
        expect(await manager.getVersion()).toEqual(initialVersion);
        expect(await manager.getSettings()).toEqual(esConfig.settings);
        expect(await manager.getMappings()).toEqual(esConfig.mappings);
      });
    });
  });
});
