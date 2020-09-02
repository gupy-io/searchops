import { Document, Provider, Result } from "./service";
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
    withGrants(field: string, terms: (string | null)[]): QueryBuilder<D>;
    withNestedGrants(source: string, field: string, terms: string[]): QueryBuilder<D>;
    withSortBy(field: string, direction: "asc" | "desc"): QueryBuilder<D>;
    onWindow(from: number, size: number): QueryBuilder<D>;
    search(): Promise<Result<D>>;
}
