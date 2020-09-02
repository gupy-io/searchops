import { expect } from "chai";
import { deepEqual, deepPatch } from "./deep";

describe("deepEqual", () => {
  it("should work for simple values", () => {
    expect(deepEqual(1, 1)).to.be.true;
    expect(deepEqual(1, "1")).to.be.false;
    expect(deepEqual(1, null)).to.be.false;
    expect(deepEqual(1, undefined)).to.be.false;
  });
  it("should work for empty objects", () => {
    expect(deepEqual({}, {})).to.be.true;
    expect(deepEqual({}, 1)).to.be.false;
    expect(deepEqual({}, null)).to.be.false;
    expect(deepEqual({}, undefined)).to.be.false;
  });
  it("should work for shallow objects", () => {
    expect(deepEqual({ 1: 1 }, { 1: 1 })).to.be.true;
    expect(deepEqual({ 1: 1 }, { 1: 2 })).to.be.false;
  });
  it("should work for nested objects", () => {
    expect(deepEqual({ 1: { 2: 2 } }, { 1: { 2: 2 } })).to.be.true;
    expect(deepEqual({ 1: { 2: 2 } }, { 1: { 2: 3 } })).to.be.false;
  });
});

describe("deepPatch", () => {
  it("should work for simple values", () => {
    expect(deepPatch(1, 1)).to.equal(undefined);
    expect(deepPatch(1, undefined)).to.equal(undefined);
    expect(deepPatch(1, "1")).to.equal("1");
    expect(deepPatch(1, null)).to.equal(null);
  });
  it("should work for empty objects", () => {
    expect(deepPatch({}, {})).to.equal(undefined);
    expect(deepPatch({}, undefined)).to.equal(undefined);
    expect(deepPatch({}, 1)).to.equal(1);
    expect(deepPatch({}, null)).to.equal(null);
  });
  it("should work for shallow objects", () => {
    expect(deepPatch({ 1: 1 }, { 1: 1 })).to.equal(undefined);
    expect(deepPatch({ 1: 1 }, { 1: 2 })).to.deep.equal({ 1: 2 });
  });
  it("should work for nested objects", () => {
    expect(
      deepPatch(
        {
          1: { a: "1" },
          2: { b: "2" },
          3: { c: "3" },
        },
        {
          1: { a: "1" },
          2: { b: "x" },
          4: { d: "4" },
        }
      )
    ).to.deep.equal({
      2: { b: "x" },
      4: { d: "4" },
    });
  });
});
