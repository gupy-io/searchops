import { Query } from "./es-types";
import { Document, Provider, Params, Result } from "./service";

export class OneOfFilterGroupBuilder {
  private group: { field: string; terms: (string | null)[] }[] = [];

  public add(field: string, terms: (string | null)[]): OneOfFilterGroupBuilder {
    this.group.push({ field, terms });

    return this;
  }

  public build(): { field: string; terms: (string | null)[] }[] {
    return this.group;
  }
}

export class QueryBuilder<D extends Document> {
  private docsProvider: Provider<D>;
  private searchParams: Params;

  public constructor({ docsProvider }: { docsProvider: Provider<D> }) {
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

  public withSearch(string: string): QueryBuilder<D> {
    this.searchParams.string = string;
    return this;
  }

  public withNested(string: string): QueryBuilder<D> {
    this.searchParams.nested.push(string);
    return this;
  }

  public withFilter(field: string, terms: (string | null)[]): QueryBuilder<D> {
    const filter: Query[] = [
      {
        terms: {
          [field]: terms.filter((s): s is string => !!s).map((s) => `${s}`),
        },
      },
    ];
    if (terms.includes(null)) {
      filter.push({ bool: { must_not: { exists: { field } } } });
    }
    this.searchParams.filter.push({ bool: { should: filter } });
    return this;
  }

  public withFiltersMatchPhrasePrefix(
    fields: { field: string; term: string }[]
  ): QueryBuilder<D> {
    const filters = fields.map((item) => {
      const filter: Query = {
        match_phrase_prefix: { [item.field]: item.term },
      };
      return filter;
    });
    this.searchParams.filter.push({ bool: { should: filters } });
    return this;
  }

  public withNestedFilter(
    source: string,
    field: string,
    terms: string[]
  ): QueryBuilder<D> {
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
  public getOneOfFilterGroupBuilder(): OneOfFilterGroupBuilder {
    return new OneOfFilterGroupBuilder();
  }

  public withOneOfFilter(
    options: { field: string; terms: (string | null)[] }[]
  ): QueryBuilder<D> {
    const group: Query[] = [];
    options.forEach(({ field, terms }) => {
      if (terms.includes(null)) {
        group.push({ bool: { must_not: { exists: { field } } } });
      }

      const values = terms.filter((s): s is string => !!s).map((s) => `${s}`);
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

  public withGrants(field: string, terms: (string | null)[]): QueryBuilder<D> {
    const grants: Query[] = [
      {
        terms: {
          [field]: terms.filter((s): s is string => !!s).map((s) => `${s}`),
        },
      },
    ];
    if (terms.includes(null)) {
      grants.push({ bool: { must_not: { exists: { field } } } });
    }
    this.searchParams.grants.push({ bool: { should: grants } });
    return this;
  }

  public withNestedGrants(
    source: string,
    field: string,
    terms: string[]
  ): QueryBuilder<D> {
    this.searchParams.grants.push({
      nested: {
        path: source,
        query: { terms: { [`${source}.${field}`]: terms } },
      },
    });
    return this;
  }

  public withSortBy(field: string, direction: "asc" | "desc"): QueryBuilder<D> {
    this.searchParams.rerank.push({ [field]: { order: direction } });
    return this;
  }

  public onWindow(from: number, size: number): QueryBuilder<D> {
    this.searchParams.window = { from, size };
    return this;
  }

  public search(): Promise<Result<D>> {
    return this.docsProvider.search(this.searchParams);
  }
}
