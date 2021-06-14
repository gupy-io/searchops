"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QueryBuilder = exports.OneOfFilterGroupBuilder = void 0;
class OneOfFilterGroupBuilder {
    constructor() {
        this.group = [];
    }
    add(field, terms) {
        this.group.push({ field, terms });
        return this;
    }
    build() {
        return this.group;
    }
}
exports.OneOfFilterGroupBuilder = OneOfFilterGroupBuilder;
class QueryBuilder {
    constructor({ docsProvider }) {
        this.docsProvider = docsProvider;
        this.searchParams = {
            string: "",
            nested: [],
            filter: [],
            grants: [],
            facets: {},
            rerank: [],
            window: { from: 0, size: 0 },
        };
        this.searchParams.facets = {
            status: { terms: { field: "status" } },
            recruiters: { terms: { field: "recruiter.id" } },
        };
    }
    withSearch(string) {
        this.searchParams.string = string;
        return this;
    }
    withNested(string) {
        this.searchParams.nested.push(string);
        return this;
    }
    withFilter(field, terms) {
        const filter = [
            {
                terms: {
                    [field]: terms.filter((s) => !!s).map((s) => `${s}`),
                },
            },
        ];
        if (terms.includes(null)) {
            filter.push({ bool: { must_not: { exists: { field } } } });
        }
        this.searchParams.filter.push({ bool: { should: filter } });
        return this;
    }
    withFiltersMatchPhrasePrefix(fields) {
        const filters = fields.map((item) => {
            const filter = {
                match_phrase_prefix: { [item.field]: item.term },
            };
            return filter;
        });
        this.searchParams.filter.push({ bool: { should: filters } });
        return this;
    }
    withNestedFilter(source, field, terms) {
        this.searchParams.filter.push({
            nested: {
                path: source,
                query: { terms: { [`${source}.${field}`]: terms } },
            },
        });
        return this;
    }
    // Returns an object used to build a clause that filters documents that match
    // any of the clauses in the group.
    getOneOfFilterGroupBuilder() {
        return new OneOfFilterGroupBuilder();
    }
    withOneOfFilter(options) {
        const group = [];
        options.forEach(({ field, terms }) => {
            if (terms.includes(null)) {
                group.push({ bool: { must_not: { exists: { field } } } });
            }
            const values = terms.filter((s) => !!s).map((s) => `${s}`);
            if (values.length === 0) {
                return;
            }
            const filter = { terms: { [field]: values } };
            group.push(filter);
        });
        if (group.length === 0) {
            return this;
        }
        this.searchParams.filter.push({ bool: { should: group } });
        return this;
    }
    withGrants(field, terms) {
        const grants = [
            {
                terms: {
                    [field]: terms.filter((s) => !!s).map((s) => `${s}`),
                },
            },
        ];
        if (terms.includes(null)) {
            grants.push({ bool: { must_not: { exists: { field } } } });
        }
        this.searchParams.grants.push({ bool: { should: grants } });
        return this;
    }
    withNestedGrants(source, field, terms) {
        this.searchParams.grants.push({
            nested: {
                path: source,
                query: { terms: { [`${source}.${field}`]: terms } },
            },
        });
        return this;
    }
    withSortBy(field, direction) {
        this.searchParams.rerank.push({ [field]: { order: direction } });
        return this;
    }
    onWindow(from, size) {
        this.searchParams.window = { from, size };
        return this;
    }
    search() {
        return this.docsProvider.search(this.searchParams);
    }
}
exports.QueryBuilder = QueryBuilder;
