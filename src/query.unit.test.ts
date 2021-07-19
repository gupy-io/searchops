import { jest, expect, describe, describe as context, it } from "@jest/globals";

import { QueryBuilder } from "./query";
import { Params } from "./service";

const testProvider = () => {
  return {
    search: jest.fn<Promise<never>, [Params]>(),
  };
};

describe("QueryBuilder", () => {
  describe("withOneOfFilter", () => {
    it("builds a should clause with all options", async () => {
      const docsProvider = testProvider();
      const qb = new QueryBuilder({ docsProvider });

      qb.withOneOfFilter([
        { field: "fieldA", terms: ["A"] },
        { field: "fieldB", terms: ["B1", "B2"] },
      ]);
      await qb.search();

      const { filter } = docsProvider.search.mock.calls[0][0];
      expect(filter).toStrictEqual([
        {
          bool: {
            should: [
              { terms: { fieldA: ["A"] } },
              { terms: { fieldB: ["B1", "B2"] } },
            ],
          },
        },
      ]);
    });

    it("ignores empty groups", async () => {
      const docsProvider = testProvider();
      const qb = new QueryBuilder({ docsProvider });

      qb.withOneOfFilter([]);
      await qb.search();

      const { filter } = docsProvider.search.mock.calls[0][0];
      expect(filter).toStrictEqual([]);
    });

    it("ignores empty terms in an option", async () => {
      const docsProvider = testProvider();
      const qb = new QueryBuilder({ docsProvider });

      qb.withOneOfFilter([{ field: "fieldA", terms: ["", "A2"] }]);
      await qb.search();

      const { filter } = docsProvider.search.mock.calls[0][0];
      expect(filter).toStrictEqual([
        {
          bool: {
            should: [{ terms: { fieldA: ["A2"] } }],
          },
        },
      ]);
    });

    context("when an option has null terms", () => {
      it("adds a must_not clause for that field", async () => {
        const docsProvider = testProvider();
        const qb = new QueryBuilder({ docsProvider });

        qb.withOneOfFilter([{ field: "field with null", terms: [null] }]);
        await qb.search();

        const { filter } = docsProvider.search.mock.calls[0][0];
        expect(filter).toStrictEqual([
          {
            bool: {
              should: [
                {
                  bool: { must_not: { exists: { field: "field with null" } } },
                },
              ],
            },
          },
        ]);
      });

      it("adds a clause with the non-null terms", async () => {
        const docsProvider = testProvider();
        const qb = new QueryBuilder({ docsProvider });

        qb.withOneOfFilter([
          { field: "fieldA", terms: ["non-null", null, "not-null", null] },
        ]);
        await qb.search();

        const { filter } = docsProvider.search.mock.calls[0][0];
        expect(filter).toStrictEqual([
          {
            bool: {
              should: [
                { bool: { must_not: { exists: { field: "fieldA" } } } },
                { terms: { fieldA: ["non-null", "not-null"] } },
              ],
            },
          },
        ]);
      });
    });
  });

  describe("range", () => {
    it("builds a should clause with date range", async () => {
      const docsProvider = testProvider();
      const qb = new QueryBuilder({ docsProvider });

      qb.withRange("age", { gt: 10, lte: 20 });
      await qb.search();

      const { filter } = docsProvider.search.mock.calls[0][0];
      expect(filter).toStrictEqual([
        {
          range: { age: { gt: 10, lte: 20 } },
        },
      ]);
    });
  });
});
