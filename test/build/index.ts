/**
 * Test will pass if this module compiles.
 */

import { SearchEngine } from 'searchops';
import { Query } from 'searchops/lib/es-types';

const matchPhraseSimple: Query = {
  match_phrase: {
    ["field"]: "this is a phrase",
  },
};

const matchPhraseDetailed: Query = {
  match_phrase: {
    ["field"]: {
      query: "this is a phrase",
    },
  },
};

const queryString: Query = {
  query_string: {
    query: "this is a query AND it's simple",
    fields: ["field1", "field2"],
  }
};
