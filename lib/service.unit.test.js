"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const sinon_1 = __importDefault(require("sinon"));
const chai_1 = require("chai");
const service_1 = require("./service");
const fakeLogger = {
    // eslint-disable-next-line no-console
    error: console.log,
};
describe("SearchService", () => {
    context("bulk", () => {
        const bulk = sinon_1.default.fake.returns({ body: { errors: false } });
        const esConfig = {
            alias: "abc",
            mappings: {},
        };
        it("delegates to esClient", async () => {
            const searchService = new service_1.SearchService({
                esClient: { bulk },
                esConfig: esConfig,
                logger: fakeLogger,
            });
            const document = "document";
            await searchService.bulk(document);
            chai_1.expect(bulk).to.have.been.called;
            chai_1.expect(bulk).to.have.been.calledWith({
                index: esConfig.alias,
                body: document,
                refresh: false,
            });
        });
        it("can ask for ES to wait document to be available", async () => {
            const searchService = new service_1.SearchService({
                esClient: { bulk },
                esConfig: esConfig,
                logger: fakeLogger,
            });
            const document = "document";
            await searchService.bulk(document, "wait_for");
            chai_1.expect(bulk.called).to.be.true;
            chai_1.expect(bulk.calledWith({
                index: esConfig.alias,
                body: document,
                refresh: "wait_for",
            })).to.be.true;
        });
        it("throws if esClient.bulk informs error", async () => {
            const searchService = new service_1.SearchService({
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
                },
                esConfig: esConfig,
                logger: fakeLogger,
            });
            const document = "document";
            try {
                await searchService.bulk(document);
            }
            catch (error) {
                chai_1.expect(error.message).to.equal("Error on bulk request");
                chai_1.expect(error.errors).to.deep.equal([
                    { type: "a" },
                    { type: "b" },
                    { type: "c" },
                    { type: "d" },
                ]);
            }
        });
    });
});
