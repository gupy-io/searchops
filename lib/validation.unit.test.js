"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const globals_1 = require("@jest/globals");
const validation_1 = require("./validation");
globals_1.describe("Elasticsearch Mapping Schema Validation @unit tests", () => {
    globals_1.describe("mapping to schema translation", () => {
        globals_1.describe("when converting a mapping with most features", () => {
            const mapping = {
                properties: {
                    name: {
                        dynamic: "strict",
                        properties: {
                            first: { type: "text" },
                            last: { type: "text" },
                        },
                    },
                    user_id: {
                        type: "keyword",
                        ignore_above: 100,
                    },
                    tags: {
                        type: "nested",
                        properties: {
                            id: { type: "integer" },
                            label: { type: "keyword" },
                        },
                    },
                },
            };
            globals_1.it("should get the correct schema without errors", () => {
                const schema = validation_1.translateObjectMapping(mapping);
                globals_1.expect(schema).toEqual({
                    type: ["object", "null"],
                    additionalProperties: true,
                    properties: {
                        name: {
                            type: ["object", "null"],
                            additionalProperties: false,
                            properties: {
                                first: { type: ["string", "null"] },
                                last: { type: ["string", "null"] },
                            },
                        },
                        user_id: { type: ["string", "null"] },
                        tags: {
                            type: ["array", "null"],
                            items: {
                                type: "object",
                                properties: {
                                    id: { type: ["integer", "null"] },
                                    label: { type: ["string", "null"] },
                                },
                            },
                        },
                    },
                });
            });
        });
    });
    globals_1.describe("validation function", () => {
        const mapping = {
            properties: {
                name: {
                    dynamic: "strict",
                    properties: {
                        first: { type: "text" },
                        last: { type: "text" },
                    },
                },
                user_id: {
                    type: "keyword",
                    ignore_above: 100,
                },
                tags: {
                    type: "nested",
                    properties: {
                        id: { type: "integer" },
                        label: { type: "keyword" },
                    },
                },
            },
        };
        const validate = validation_1.getValidatorForMapping(mapping);
        globals_1.describe("when validating data conforming to schema", () => {
            const data = {
                name: { first: "John", last: undefined },
                tags: [
                    { id: 1, label: "Unicorn" },
                    { id: 2, label: "Missing Surname" },
                ],
            };
            globals_1.it("should accept and keep all data", () => {
                const good = validate(data);
                globals_1.expect(good).toBeTruthy();
                globals_1.expect(validate.errors).toBeNull();
                globals_1.expect(data).toEqual({
                    name: { first: "John", last: undefined },
                    tags: [
                        { id: 1, label: "Unicorn" },
                        { id: 2, label: "Missing Surname" },
                    ],
                });
            });
        });
        globals_1.describe("when validating data with unmapped fields", () => {
            const data = {
                first: "John",
                last: "Doe",
                user_id: 1,
            };
            globals_1.it("should accept and keep unexpected data", () => {
                const ok = validate(data);
                globals_1.expect(ok).toBeTruthy();
                globals_1.expect(validate.errors).toBeNull();
                globals_1.expect(data).toEqual({
                    first: "John",
                    last: "Doe",
                    user_id: "1",
                });
            });
        });
        globals_1.describe("when validating data with forbidden fields", () => {
            const data = {
                name: { full: "John Doe" },
                user_id: 1,
            };
            globals_1.it("should reject and report unexpected data", () => {
                const ok = validate(data);
                globals_1.expect(ok).toBeFalsy();
                // expect(validate.errors).toBeArr("array").that.is.not.empty;
            });
        });
        globals_1.describe("when validating data with compatible types", () => {
            const data = {
                user_id: 1,
                tags: [
                    { id: "1", label: 1 },
                    { id: "2", label: 2 },
                ],
            };
            globals_1.it("should accept and coerce all data", () => {
                const good = validate(data);
                globals_1.expect(good).toBeTruthy();
                globals_1.expect(validate.errors).toBeNull();
                globals_1.expect(data).toEqual({
                    user_id: "1",
                    tags: [
                        { id: 1, label: "1" },
                        { id: 2, label: "2" },
                    ],
                });
            });
        });
        globals_1.describe("when validating data with incompatible types", () => {
            const data = {
                tags: [{ id: "a" }],
            };
            globals_1.it("should reject and report errors", () => {
                const bad = !validate(data);
                globals_1.expect(bad).toBeTruthy();
                // expect(validate.errors).to.be.an("array").that.is.not.empty;
            });
        });
    });
});
