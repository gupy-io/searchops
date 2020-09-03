"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const globals_1 = require("@jest/globals");
const deep_1 = require("./deep");
globals_1.describe("deepEqual", () => {
    globals_1.it("should work for simple values", () => {
        globals_1.expect(deep_1.deepEqual(1, 1)).toBeTruthy();
        globals_1.expect(deep_1.deepEqual(1, "1")).toBeFalsy();
        globals_1.expect(deep_1.deepEqual(1, null)).toBeFalsy();
        globals_1.expect(deep_1.deepEqual(1, undefined)).toBeFalsy();
    });
    globals_1.it("should work for empty objects", () => {
        globals_1.expect(deep_1.deepEqual({}, {})).toBeTruthy();
        globals_1.expect(deep_1.deepEqual({}, 1)).toBeFalsy();
        globals_1.expect(deep_1.deepEqual({}, null)).toBeFalsy();
        globals_1.expect(deep_1.deepEqual({}, undefined)).toBeFalsy();
    });
    globals_1.it("should work for shallow objects", () => {
        globals_1.expect(deep_1.deepEqual({ 1: 1 }, { 1: 1 })).toBeTruthy();
        globals_1.expect(deep_1.deepEqual({ 1: 1 }, { 1: 2 })).toBeFalsy();
    });
    globals_1.it("should work for nested objects", () => {
        globals_1.expect(deep_1.deepEqual({ 1: { 2: 2 } }, { 1: { 2: 2 } })).toBeTruthy();
        globals_1.expect(deep_1.deepEqual({ 1: { 2: 2 } }, { 1: { 2: 3 } })).toBeFalsy();
    });
});
globals_1.describe("deepPatch", () => {
    globals_1.it("should work for simple values", () => {
        globals_1.expect(deep_1.deepPatch(1, 1)).toEqual(undefined);
        globals_1.expect(deep_1.deepPatch(1, undefined)).toEqual(undefined);
        globals_1.expect(deep_1.deepPatch(1, "1")).toEqual("1");
        globals_1.expect(deep_1.deepPatch(1, null)).toEqual(null);
    });
    globals_1.it("should work for empty objects", () => {
        globals_1.expect(deep_1.deepPatch({}, {})).toEqual(undefined);
        globals_1.expect(deep_1.deepPatch({}, undefined)).toEqual(undefined);
        globals_1.expect(deep_1.deepPatch({}, 1)).toEqual(1);
        globals_1.expect(deep_1.deepPatch({}, null)).toEqual(null);
    });
    globals_1.it("should work for shallow objects", () => {
        globals_1.expect(deep_1.deepPatch({ 1: 1 }, { 1: 1 })).toEqual(undefined);
        globals_1.expect(deep_1.deepPatch({ 1: 1 }, { 1: 2 })).toEqual({ 1: 2 });
    });
    globals_1.it("should work for nested objects", () => {
        globals_1.expect(deep_1.deepPatch({
            1: { a: "1" },
            2: { b: "2" },
            3: { c: "3" },
        }, {
            1: { a: "1" },
            2: { b: "x" },
            4: { d: "4" },
        })).toEqual({
            2: { b: "x" },
            4: { d: "4" },
        });
    });
});
