"use strict";
/* eslint-disable @typescript-eslint/camelcase */
// Elasticsearch types follow the snake_case JSON convention
// Document is in _source, plus other metadata fields with _
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const chai_1 = require("chai");
const faker_1 = __importDefault(require("faker"));
const sinon_1 = __importDefault(require("sinon"));
const utils_1 = require("./test/utils");
const migration_1 = require("./migration");
const randomSnakeCase = () => faker_1.default.random.word().replace(/\W/g, "_").toLowerCase();
describe("Elasticsearch Index Migration @integration tests", () => {
    const sandbox = sinon_1.default.createSandbox();
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
    beforeEach(() => {
        sandbox.spy(esClient, "reindex");
        sandbox.spy(esClient, "updateByQuery");
        sandbox.spy(esClient.indices, "create");
        sandbox.spy(esClient.indices, "delete");
        sandbox.spy(esClient.indices, "putMapping");
        sandbox.spy(esClient.indices, "putSettings");
        sandbox.spy(esClient.indices, "updateAliases");
    });
    afterEach(async () => {
        await manager.deleteIndex();
        sandbox.restore();
    });
    context("when aliased index does not exist", () => {
        beforeEach(async () => {
            chai_1.expect(await manager.existsIndex()).to.be.false;
            chai_1.expect(await manager.existsAlias()).to.be.false;
        });
        it("should create aliased index with settings and mappings", async () => {
            await manager.migrate();
            chai_1.expect(await manager.existsIndex()).to.be.true;
            chai_1.expect(await manager.existsAlias()).to.be.true;
            chai_1.expect(await manager.getSettings()).to.deep.include(esConfig.settings);
            chai_1.expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
        });
    });
    context("when aliased index already exists", () => {
        let initialVersion;
        beforeEach(async () => {
            await manager.migrate();
            initialVersion = await manager.getVersion();
            await esClient.index({
                index: esConfig.index,
                body: { code: "123/456" },
                refresh: "wait_for",
            });
        });
        context("when settings and mappings are still the same", () => {
            beforeEach(async () => {
                chai_1.expect(await manager.getSettings()).to.deep.include(esConfig.settings);
                chai_1.expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
                sandbox.resetHistory();
            });
            it("should perform no maintenance", async () => {
                await manager.migrate();
                chai_1.expect(await manager.getVersion()).to.equal(initialVersion);
                chai_1.expect(esClient.reindex).to.not.have.been.called;
                chai_1.expect(esClient.updateByQuery).to.not.have.been.called;
                chai_1.expect(esClient.indices.create).to.not.have.been.called;
                chai_1.expect(esClient.indices.delete).to.not.have.been.called;
                chai_1.expect(esClient.indices.putMapping).to.not.have.been.called;
                chai_1.expect(esClient.indices.putSettings).to.not.have.been.called;
                chai_1.expect(esClient.indices.updateAliases).to.not.have.been.called;
            });
        });
        context("when dynamic mappings have changed", () => {
            const subSandbox = sinon_1.default.createSandbox();
            beforeEach(() => {
                subSandbox.replace(esConfig, "mappings", {
                    properties: {
                        ...esConfig.mappings.properties,
                        code: { type: "text", fields: { keyword: { type: "keyword" } } },
                    },
                });
            });
            afterEach(() => {
                subSandbox.restore();
            });
            it("should update mappings without recreating index", async () => {
                await manager.migrate();
                chai_1.expect(await manager.getVersion()).to.equal(initialVersion);
                chai_1.expect(await manager.getSettings()).to.deep.include(esConfig.settings);
                chai_1.expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
            });
        });
        context("when dynamic settings have changed", () => {
            const subSandbox = sinon_1.default.createSandbox();
            beforeEach(() => {
                subSandbox.replace(esConfig, "settings", {
                    ...esConfig.settings,
                    refresh_interval: "2ms",
                });
            });
            afterEach(() => {
                subSandbox.restore();
            });
            it("should update settings without recreating index", async () => {
                await manager.migrate();
                chai_1.expect(await manager.getVersion()).to.equal(initialVersion);
                chai_1.expect(await manager.getSettings()).to.deep.include(esConfig.settings);
                chai_1.expect(await manager.getMappings()).to.deep.include(esConfig.mappings);
            });
        });
    });
});
