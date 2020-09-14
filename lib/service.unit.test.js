"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const globals_1 = require("@jest/globals");
const winston_1 = require("winston");
const service_1 = require("./service");
const logger = winston_1.createLogger({ silent: true });
globals_1.describe("SearchService", () => {
    globals_1.describe("bulk", () => {
        const bulk = globals_1.jest.fn().mockReturnValue({ body: { errors: false } });
        const esConfig = {
            alias: "abc",
            mappings: {},
        };
        globals_1.it("delegates to esClient", async () => {
            const searchService = new service_1.SearchService({
                esClient: { bulk },
                esConfig: esConfig,
                logger,
            });
            const document = "document";
            await searchService.bulk(document);
            globals_1.expect(bulk).toHaveBeenCalled();
            globals_1.expect(bulk).toHaveBeenCalledWith({
                index: esConfig.alias,
                body: document,
                refresh: false,
            });
        });
        globals_1.it("can ask for ES to wait document to be available", async () => {
            const searchService = new service_1.SearchService({
                esClient: { bulk },
                esConfig: esConfig,
                logger,
            });
            const document = "document";
            await searchService.bulk(document, "wait_for");
            globals_1.expect(bulk).toHaveBeenCalled();
            globals_1.expect(bulk).toHaveBeenCalledWith({
                index: esConfig.alias,
                body: document,
                refresh: "wait_for",
            });
        });
        globals_1.it("throws if esClient.bulk informs error", async () => {
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
                logger,
            });
            const document = "document";
            try {
                await searchService.bulk(document);
            }
            catch (e) {
                globals_1.expect(e).toBeInstanceOf(service_1.BulkError);
                if (e instanceof service_1.BulkError) {
                    globals_1.expect(e.message).toEqual("Error on bulk request");
                    globals_1.expect(e.errors).toEqual([
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
