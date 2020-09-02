"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const chai_1 = require("chai");
const deep_1 = require("./deep");
describe("deepEqual", () => {
    it("should work for simple values", () => {
        chai_1.expect(deep_1.deepEqual(1, 1)).to.be.true;
        chai_1.expect(deep_1.deepEqual(1, "1")).to.be.false;
        chai_1.expect(deep_1.deepEqual(1, null)).to.be.false;
        chai_1.expect(deep_1.deepEqual(1, undefined)).to.be.false;
    });
    it("should work for empty objects", () => {
        chai_1.expect(deep_1.deepEqual({}, {})).to.be.true;
        chai_1.expect(deep_1.deepEqual({}, 1)).to.be.false;
        chai_1.expect(deep_1.deepEqual({}, null)).to.be.false;
        chai_1.expect(deep_1.deepEqual({}, undefined)).to.be.false;
    });
    it("should work for shallow objects", () => {
        chai_1.expect(deep_1.deepEqual({ 1: 1 }, { 1: 1 })).to.be.true;
        chai_1.expect(deep_1.deepEqual({ 1: 1 }, { 1: 2 })).to.be.false;
    });
    it("should work for nested objects", () => {
        chai_1.expect(deep_1.deepEqual({ 1: { 2: 2 } }, { 1: { 2: 2 } })).to.be.true;
        chai_1.expect(deep_1.deepEqual({ 1: { 2: 2 } }, { 1: { 2: 3 } })).to.be.false;
    });
});
describe("deepPatch", () => {
    it("should work for simple values", () => {
        chai_1.expect(deep_1.deepPatch(1, 1)).to.equal(undefined);
        chai_1.expect(deep_1.deepPatch(1, undefined)).to.equal(undefined);
        chai_1.expect(deep_1.deepPatch(1, "1")).to.equal("1");
        chai_1.expect(deep_1.deepPatch(1, null)).to.equal(null);
    });
    it("should work for empty objects", () => {
        chai_1.expect(deep_1.deepPatch({}, {})).to.equal(undefined);
        chai_1.expect(deep_1.deepPatch({}, undefined)).to.equal(undefined);
        chai_1.expect(deep_1.deepPatch({}, 1)).to.equal(1);
        chai_1.expect(deep_1.deepPatch({}, null)).to.equal(null);
    });
    it("should work for shallow objects", () => {
        chai_1.expect(deep_1.deepPatch({ 1: 1 }, { 1: 1 })).to.equal(undefined);
        chai_1.expect(deep_1.deepPatch({ 1: 1 }, { 1: 2 })).to.deep.equal({ 1: 2 });
    });
    it("should work for nested objects", () => {
        chai_1.expect(deep_1.deepPatch({
            1: { a: "1" },
            2: { b: "2" },
            3: { c: "3" },
        }, {
            1: { a: "1" },
            2: { b: "x" },
            4: { d: "4" },
        })).to.deep.equal({
            2: { b: "x" },
            4: { d: "4" },
        });
    });
});
