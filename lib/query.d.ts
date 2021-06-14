import { Document, Provider, Result } from "./service";
export declare class OneOfFilterGroupBuilder {
    private group;
    add(field: string, terms: (string | null)[]): OneOfFilterGroupBuilder;
    build(): {
        field: string;
        terms: (string | null)[];
    }[];
}
export declare class QueryBuilder<D extends Document> {
    private docsProvider;
    private searchParams;
    constructor({ docsProvider }: {
        docsProvider: Provider<D>;
    });
    withSearch(string: string): QueryBuilder<D>;
    withNested(string: string): QueryBuilder<D>;
    withFilter(field: string, terms: (string | null)[]): QueryBuilder<D>;
    withFiltersMatchPhrasePrefix(fields: {
        field: string;
        term: string;
    }[]): QueryBuilder<D>;
    withNestedFilter(source: string, field: string, terms: string[]): QueryBuilder<D>;
    getOneOfFilterGroupBuilder(): OneOfFilterGroupBuilder;
    withOneOfFilter(options: {
        field: string;
        terms: (string | null)[];
    }[]): QueryBuilder<D>;
    withGrants(field: string, terms: (string | null)[]): QueryBuilder<D>;
    withNestedGrants(source: string, field: string, terms: string[]): QueryBuilder<D>;
    withSortBy(field: string, direction: "asc" | "desc"): QueryBuilder<D>;
    onWindow(from: number, size: number): QueryBuilder<D>;
    search(): Promise<Result<D>>;
}
