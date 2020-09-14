"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
/* eslint-disable @typescript-eslint/no-misused-promises */
/* eslint-disable @typescript-eslint/no-floating-promises */
/* eslint-disable @typescript-eslint/unbound-method */
const globals_1 = require("@jest/globals");
const faker_1 = __importDefault(require("faker"));
const utils_1 = require("./test/utils");
const migration_1 = require("./migration");
const randomSnakeCase = () => faker_1.default.random.word().replace(/\W/g, "_").toLowerCase();
globals_1.describe("Elasticsearch Index Migration @integration tests", () => {
    const esClient = utils_1.getTestClient();
    const esConfig = {
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
    const manager = new migration_1.IndexManager({ esClient, esConfig });
    globals_1.beforeEach(() => {
        globals_1.jest.spyOn(esClient, "reindex");
        globals_1.jest.spyOn(esClient, "updateByQuery");
        globals_1.jest.spyOn(esClient.indices, "create");
        globals_1.jest.spyOn(esClient.indices, "delete");
        globals_1.jest.spyOn(esClient.indices, "putMapping");
        globals_1.jest.spyOn(esClient.indices, "putSettings");
        globals_1.jest.spyOn(esClient.indices, "updateAliases");
    });
    globals_1.afterEach(async () => {
        await manager.deleteIndex();
        globals_1.jest.restoreAllMocks();
    });
    globals_1.describe("when aliased index does not exist", () => {
        globals_1.beforeEach(async () => {
            globals_1.expect(await manager.existsIndex()).toBeFalsy();
            globals_1.expect(await manager.existsAlias()).toBeFalsy();
        });
        globals_1.it("should create aliased index with settings and mappings", async () => {
            await manager.migrate();
            globals_1.expect(await manager.existsIndex()).toBeTruthy();
            globals_1.expect(await manager.existsAlias()).toBeTruthy();
            globals_1.expect(await manager.getSettings()).toEqual(esConfig.settings);
            globals_1.expect(await manager.getMappings()).toEqual(esConfig.mappings);
        });
    });
    globals_1.describe("when aliased index already exists", () => {
        let initialVersion;
        globals_1.beforeEach(async () => {
            await manager.migrate();
            initialVersion = await manager.getVersion();
            await esClient.index({
                index: esConfig.index,
                body: { code: "123/456" },
                refresh: "wait_for",
            });
        });
        globals_1.describe("when settings and mappings are still the same", () => {
            globals_1.beforeEach(async () => {
                globals_1.expect(await manager.getSettings()).toEqual(esConfig.settings);
                globals_1.expect(await manager.getMappings()).toEqual(esConfig.mappings);
                globals_1.jest.resetAllMocks();
            });
            globals_1.it("should perform no maintenance", async () => {
                await manager.migrate();
                globals_1.expect(await manager.getVersion()).toEqual(initialVersion);
                globals_1.expect(esClient.reindex).not.toHaveBeenCalled();
                globals_1.expect(esClient.updateByQuery).not.toHaveBeenCalled();
                globals_1.expect(esClient.indices.create).not.toHaveBeenCalled();
                globals_1.expect(esClient.indices.delete).not.toHaveBeenCalled();
                globals_1.expect(esClient.indices.putMapping).not.toHaveBeenCalled();
                globals_1.expect(esClient.indices.putSettings).not.toHaveBeenCalled();
                globals_1.expect(esClient.indices.updateAliases).not.toHaveBeenCalled();
            });
        });
        globals_1.describe("when dynamic mappings have changed", () => {
            globals_1.beforeEach(() => {
                esConfig.mappings = {
                    properties: {
                        ...esConfig.mappings.properties,
                        code: { type: "text", fields: { keyword: { type: "keyword" } } },
                    },
                };
            });
            globals_1.afterEach(() => {
                globals_1.jest.restoreAllMocks();
            });
            globals_1.it("should update mappings without recreating index", async () => {
                await manager.migrate();
                globals_1.expect(await manager.getVersion()).toEqual(initialVersion);
                globals_1.expect(await manager.getSettings()).toEqual(esConfig.settings);
                globals_1.expect(await manager.getMappings()).toEqual(esConfig.mappings);
            });
        });
        globals_1.describe("when dynamic settings have changed", () => {
            globals_1.beforeEach(() => {
                esConfig.settings = {
                    ...esConfig.settings,
                    refresh_interval: "2ms",
                };
            });
            globals_1.afterEach(() => {
                globals_1.jest.resetAllMocks();
            });
            globals_1.it("should update settings without recreating index", async () => {
                await manager.migrate();
                globals_1.expect(await manager.getVersion()).toEqual(initialVersion);
                globals_1.expect(await manager.getSettings()).toEqual(esConfig.settings);
                globals_1.expect(await manager.getMappings()).toEqual(esConfig.mappings);
            });
        });
    });
});
