import { expect, it, describe } from "@jest/globals";
import { deepEqual, deepPatch } from "./deep";

describe("deepEqual", () => {
  it("should work for simple values", () => {
    expect(deepEqual(1, 1)).toBeTruthy();
    expect(deepEqual(1, "1")).toBeFalsy();
    expect(deepEqual(1, null)).toBeFalsy();
    expect(deepEqual(1, undefined)).toBeFalsy();
  });
  it("should work for empty objects", () => {
    expect(deepEqual({}, {})).toBeTruthy();
    expect(deepEqual({}, 1)).toBeFalsy();
    expect(deepEqual({}, null)).toBeFalsy();
    expect(deepEqual({}, undefined)).toBeFalsy();
  });
  it("should work for shallow objects", () => {
    expect(deepEqual({ 1: 1 }, { 1: 1 })).toBeTruthy();
    expect(deepEqual({ 1: 1 }, { 1: 2 })).toBeFalsy();
  });
  it("should work for nested objects", () => {
    expect(deepEqual({ 1: { 2: 2 } }, { 1: { 2: 2 } })).toBeTruthy();
    expect(deepEqual({ 1: { 2: 2 } }, { 1: { 2: 3 } })).toBeFalsy();
  });
});

describe("deepPatch", () => {
  it("should work for simple values", () => {
    expect(deepPatch(1, 1)).toEqual(undefined);
    expect(deepPatch(1, undefined)).toEqual(undefined);
    expect(deepPatch(1, "1")).toEqual("1");
    expect(deepPatch(1, null)).toEqual(null);
  });
  it("should work for empty objects", () => {
    expect(deepPatch({}, {})).toEqual(undefined);
    expect(deepPatch({}, undefined)).toEqual(undefined);
    expect(deepPatch({}, 1)).toEqual(1);
    expect(deepPatch({}, null)).toEqual(null);
  });
  it("should work for shallow objects", () => {
    expect(deepPatch({ 1: 1 }, { 1: 1 })).toEqual(undefined);
    expect(deepPatch({ 1: 1 }, { 1: 2 })).toEqual({ 1: 2 });
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
    ).toEqual({
      2: { b: "x" },
      4: { d: "4" },
    });
  });
});
