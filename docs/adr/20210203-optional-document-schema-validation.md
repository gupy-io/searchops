# Optional document schema validation

- Status: draft
- Date: 2021-02-03
- Tags: validation, mappings

## Context and Problem Statement

Searchops versions <0.0.4 used Ajv version 6.x to validate the incoming document
before sending it to Elasticsearch on index requests. The conversion Mapping ->
JSON Schema -> Validator would happen in the constructor for every client
instantiation. This was not optimal but not significant as Ajv 6.x would cache
compiled schemas.

The feature exists in order to protect the client from sending index requests of
documents containing invalid data. In the early days of adopting Elasticsearch,
most indexes wouldn't have strict mappings, which could be dangerous. Validation
would help users prevent sending new data serialized in ways that Elasticsearch
dynamic mapping would find ambiguous, e.g. failing to interpret a string as
Date.

Version 0.0.4 of searchops upgraded Ajv to 7.x, which [introduced a change][ajv]
in schema caching so that the schema object reference would be used as cache key
directly instead of using the serialization of the schema as 6.x did previously.
This introduced a significant performance issue since the JSON Schema was
generated in a new reference at every class instantiation even if the mapping
stayed unchanged.

[ajv]: https://github.com/ajv-validator/ajv/releases/tag/v7.0.0

## Decision Drivers

1. [You Aren't Gonna Need It][yagni]
2. [Principle of Least Astonishment][pola]

[yagni]: https://en.wikipedia.org/wiki/You_aren%27t_gonna_need_it
[pola]: https://en.wikipedia.org/wiki/Principle_of_least_astonishment

## Considered Options

A) Regarding the performance problem:

1. Cache schema objects ourselves
2. Use Ajv 6.x indefinitely
3. Change to a different library

B) Regarding the validation feature:

1. Make validation opt-in
2. Remove the validation feature


## Decision Outcome

Chosen option: **cache schema objects ourselves AND make validation opt-in**.

### Positive Consequences

- Validation is still available
- Validation cost is paid only by those who need it
- Schema compilation cost stays amortized
- Default behavior is intuitive

### Negative Consequences

- More opt-in features means more complexity
- Default behavior is less safe

## Pros and Cons of the Options

### A1: Cache schema objects ourselves

Pros:

- Keeps dependency up to date

Cons:

- More code to maintain

### A2: Use Ajv 6.x indefinitely

Pros:

- Less code to maintain

Cons:

- Stale dependency

### A3: Change to a different library

A library that behaves like Ajv 6.x did, caching by serialized schema.

Pros:

- Less code to maintain
- Keeps dependency up to date

Cons:

- No suitable alternative found

### B1: Make validation opt-in

Pros:

- The performance cost is paid only by those who chose to (+POLA)

Cons:

- Default behavior is not the safest

### B2: Remove the validation feature

Pros:

- Less code to maintain (+YAGNI)

Cons:

- A helpful-proven feature would be gone

## Links <!-- optional -->

- [GitHub Issue #163: Upgrade to Ajv 7.x introduced critical performance issue][issue]

[issue]: (https://github.com/gupy-io/searchops/issues/163)
