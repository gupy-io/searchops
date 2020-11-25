type Value = string | number;

export interface UpdateBody<T> {
  doc: T;
  doc_as_upsert: boolean;
}

export interface SearchBody {
  query: Query;
  sort?: Sort | Sort[];
  aggs?: Aggregations;
}

// #region Query
export interface Query {
  bool?: BoolQuery;
  exists?: ExistsQuery;
  match_all?: MatchAllQuery;
  nested?: NestedQuery;
  query_string?: QueryStringQuery;
  term?: TermQuery;
  terms?: TermsQuery;
  match?: MatchQuery;
  match_phrase?: MatchPhraseQuery;
  match_phrase_prefix?: MatchPhrasePrefixQuery;
}

export interface BoolQuery {
  should?: Query | Query[];
  filter?: Query | Query[];
  must?: Query | Query[];
  must_not?: Query | Query[];
  minimum_should_match?: number;
}

export interface ExistsQuery {
  field: string;
}

export interface MatchAllQuery {
  boost?: number;
}

export interface NestedQuery {
  path: string;
  query: Query;
}

export interface QueryStringQuery {
  query: string;
  default_field?: string;
  allow_leading_wildcard?: boolean;
  analyze_wildcard?: boolean;
  analyzer?: string;
  auto_generate_synonyms_phrase_query?: boolean;
  boost?: number;
  default_operator?: "OR" | "AND";
  enable_position_increments?: boolean;
  fields?: string[];
  fuzziness?: string;
  fuzzy_max_expansions?: number;
  fuzzy_prefix_length?: number;
  fuzzy_transpositions?: boolean;
  lenient?: boolean;
  max_determinized_states?: number;
  minimum_should_match?: string;
  quote_analyzer?: string;
  phrase_slop?: number;
  quote_field_suffix?: string;
  rewrite?: string;
  time_zone?: string;
}

export interface TermQuery {
  [field: string]: Value;
}

export interface TermsQuery {
  [field: string]: Value[];
}

export interface MatchQuery {
  [field: string]:
    | Value
    | {
        query: Value;
        analyzer?: string;
        auto_generate_synonyms_phrase_query?: boolean;
        fuzziness?: string;
        max_expansions?: number;
        prefix_length?: number;
        fuzzy_transpositions?: boolean;
        fuzzy_rewrite?: string;
        lenient?: boolean;
        operator?: "OR" | "AND";
        minimum_should_match?: string;
        zero_terms_query?: "none" | "all";
      };
}

export interface MatchPhraseQuery {
  [field: string]:
    | Value
    | {
        query: Value;
        analyzer?: string;
        zero_terms_query?: "none" | "all";
      };
}

export interface MatchPhrasePrefixQuery {
  [field: string]:
    | Value
    | {
        query: Value;
        analyzer?: string;
        max_expansions?: number;
        slop?: number;
        zero_terms_query?: "none" | "all";
      };
}

// #endregion

// #region Sort
export interface Sort {
  [key: string]: {
    order?: "asc" | "desc";
    missing?: "_last" | "_first" | Value;
  };
}
// #endregion

// #region Aggregations
export interface Aggregations {
  [key: string]: Aggregation;
}

export interface Aggregation {
  aggs?: Aggregations;
  terms?: TermsAggregation;
}

export interface TermsAggregation {
  field: string;
  size?: number;
  missing?: Value;
}
// #endregion

export interface SearchResponse<T> {
  took: number;
  timed_out: boolean;
  hits: {
    total: { value: number; relation: "eq" | "gte" };
    max_score: number;
    hits: Hit<T>[];
  };
  aggregations?: Aggregations;
}

export interface Hit<T> {
  _index: string;
  _type: string;
  _id: string;
  _score: number;
  _source: T;
  sort?: string[];
}

// #region Mappings
export interface Mappings {
  _routing?: { required: boolean };
  dynamic?: boolean | "strict";
  properties?: Properties;
}

export interface Properties {
  [field: string]: Mapping;
}

export type Mapping =
  | BooleanMapping
  | JoinMapping
  | KeywordMapping
  | NestedMapping
  | ObjectMapping
  | SimpleMapping
  | TextMapping;

export interface BooleanMapping {
  type: "boolean";
  null_value?: boolean;
}
export interface JoinMapping {
  type: "join";
  relations: { [key: string]: string };
}

export interface KeywordMapping {
  type: "keyword";
  ignore_above?: number;
  null_value?: string;
  fields?: Properties;
}

export interface NestedMapping {
  type: "nested";
  properties?: Properties;
}

export interface ObjectMapping {
  type?: "object";
  dynamic?: boolean | "strict";
  enabled?: boolean;
  properties?: Properties;
}

export interface SimpleMapping {
  type: SimpleType;
  null_value?: string;
}

export interface TextMapping {
  type: "text";
  analyzer?: MappingAnalyzer;
  fields?: Properties;
}

export type SimpleType =
  | "long"
  | "integer"
  | "short"
  | "byte"
  | "double"
  | "float"
  | "half_float"
  | "scaled_float"
  | "date"
  | "date_nanos"
  | "binary"
  | "integer_range"
  | "float_range"
  | "long_range"
  | "double_range"
  | "date_range"
  | "geo_point"
  | "geo_shape";

export type MappingAnalyzer = "english" | "spanish" | "portuguese" | string; // TODO: couple with custom analyzer without allowing any string

export interface GetMappingsResponse {
  [key: string]: { mappings: Mappings };
}
// #endregion

// #region Settings
export interface Settings {
  [key: string]: unknown;
}

export interface ConcreteIndexSettings extends Settings {
  index: {
    uuid: string;
    provided_name: string;
    creation_date: string;
    version: {
      created: string;
    };
  };
}

export interface GetSettingsResponse {
  [key: string]: { settings: ConcreteIndexSettings };
}
// #endregion
