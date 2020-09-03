const { describe, it, expect } = require("@jest/globals");
const { removeUndefined, removeUndefinedOfItems } = require("./index");

describe("helpers", () => {
  describe("Object helper functions", () => {
    describe("removeUndefined", () => {
      it("should remove undefined properties of complex objects", () => {
        const input = {
          key1: "any",
          key2: undefined,
          key3: {
            key4: 0,
            key5: undefined,
          },
          key6: {
            key7: undefined,
          },
        };
        const expected = {
          key1: "any",
          key3: {
            key4: 0,
          },
          key6: {},
        };

        expect(removeUndefined(input)).toEqual(expected);
      });
    });

    describe("removeUndefinedOfItems()", () => {
      it("should remove undefined properties of complex objects in an array", () => {
        const input = [
          {
            key1: "any",
            key2: undefined,
            key3: {
              key4: 0,
              key5: undefined,
            },
            key6: {
              key7: undefined,
            },
          },
          {
            key1: "other",
            key2: undefined,
            key3: {
              key4: 0,
              key5: undefined,
            },
            key6: {
              key7: undefined,
            },
          },
        ];
        const expected = [
          {
            key1: "any",
            key3: {
              key4: 0,
            },
            key6: {},
          },
          {
            key1: "other",
            key3: {
              key4: 0,
            },
            key6: {},
          },
        ];

        expect(removeUndefinedOfItems(input)).toEqual(expected);
      });
    });
  });
});
