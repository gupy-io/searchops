declare type Value = string | number;
export interface UpdateBody<T> {
    doc: T;
    doc_as_upsert: boolean;
}
export interface SearchBody {
    query: Query;
    sort: Sort | Sort[];
    aggs: Aggregations;
}
export interface Query {
    bool?: BoolQuery;
    exists?: ExistsQuery;
    match_all?: MatchAllQuery;
    nested?: NestedQuery;
    query_string?: QueryStringQuery;
    term?: TermQuery;
    terms?: TermsQuery;
    match?: TermQuery;
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
}
export interface TermQuery {
    [field: string]: Value;
}
export interface TermsQuery {
    [field: string]: Value[];
}
export interface MatchPhrasePrefixQuery {
    [field: string]: Value | {
        query: Value;
        max_expansions?: number;
    };
}
export interface Sort {
    [key: string]: {
        order?: "asc" | "desc";
        missing?: "_last" | "_first" | Value;
    };
}
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
export interface SearchResponse<T> {
    took: number;
    timed_out: boolean;
    hits: {
        total: {
            value: number;
            relation: "eq" | "gte";
        };
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
export interface Mappings {
    _routing?: {
        required: boolean;
    };
    dynamic?: boolean | "strict";
    properties?: Properties;
}
export interface Properties {
    [field: string]: Mapping;
}
export declare type Mapping = BooleanMapping | JoinMapping | KeywordMapping | NestedMapping | ObjectMapping | SimpleMapping | TextMapping;
export interface BooleanMapping {
    type: "boolean";
    null_value?: boolean;
}
export interface JoinMapping {
    type: "join";
    relations: {
        [key: string]: string;
    };
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
export declare type SimpleType = "long" | "integer" | "short" | "byte" | "double" | "float" | "half_float" | "scaled_float" | "date" | "date_nanos" | "binary" | "integer_range" | "float_range" | "long_range" | "double_range" | "date_range" | "geo_point" | "geo_shape";
export declare type MappingAnalyzer = "english" | "spanish" | "portuguese" | string;
export interface GetMappingsResponse {
    [key: string]: {
        mappings: Mappings;
    };
}
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
    [key: string]: {
        settings: ConcreteIndexSettings;
    };
}
export {};
