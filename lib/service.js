"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.SearchService = exports.BulkError = exports.ValidationError = void 0;
const validation_1 = require("./validation");
class ValidationError extends Error {
    constructor(message, context) {
        super(message);
        this.context = context;
    }
}
exports.ValidationError = ValidationError;
class BulkError extends Error {
    constructor(message, errors) {
        super(message);
        this.errors = errors;
    }
}
exports.BulkError = BulkError;
class SearchService {
    constructor({ esClient, esConfig, logger, }) {
        this.esClient = esClient;
        this.esConfig = esConfig;
        this.validate = validation_1.getValidatorForMapping(esConfig.mappings);
        this.logger = logger;
    }
    getAction(item) {
        if (item.create) {
            return item.create;
        }
        if (item.delete) {
            return item.delete;
        }
        if (item.index) {
            return item.index;
        }
        if (item.update) {
            return item.update;
        }
        return {};
    }
    async bulk(body, refresh = false) {
        const response = await this.esClient.bulk({
            index: this.esConfig.alias,
            body,
            refresh,
        });
        if (response.body.errors) {
            // eslint-disable-next-line
            const errors = response.body.items
                // eslint-disable-next-line
                .filter((item) => !!this.getAction(item).error)
                // eslint-disable-next-line
                .map((item) => this.getAction(item).error);
            // This logger is temporary and will be removed soon
            this.logger.error("Error on bulk request (complete log)", response.body);
            throw new BulkError("Error on bulk request", errors);
        }
    }
    async get(id) {
        const response = await this.esClient.get({
            id,
            index: this.esConfig.alias,
        });
        return response.body._source;
    }
    async index(doc, refresh = "false") {
        try {
            const valid = this.validate(doc);
            if (!valid) {
                throw new ValidationError("Document did not pass mapping pre-validation", { doc, mapping: this.esConfig.mappings, errors: this.validate.errors });
            }
            await this.esClient.update({
                id: `${doc.id}`,
                index: this.esConfig.alias,
                body: { doc, doc_as_upsert: true },
                retry_on_conflict: 10,
                refresh,
            });
        }
        catch (error) {
            this.logger.error(`Error on indexing document ${doc.id}`, error);
        }
    }
    async delete(docId, routing) {
        try {
            await this.esClient.delete({
                id: `${docId}`,
                index: this.esConfig.alias,
                type: this.esConfig.dtype,
                routing,
            });
        }
        catch (error) {
            this.logger.error(`Error on deleting document ${docId}`, error);
        }
    }
    checkIfIsBooleanQuery(query) {
        return query.includes(":");
    }
    getshould(string, nested) {
        if (!string)
            return { match_all: {} };
        const isBooleanQuery = this.checkIfIsBooleanQuery(string);
        if (isBooleanQuery) {
            return {
                bool: {
                    should: [
                        { query_string: { query: string } },
                        ...nested.map((path) => ({
                            nested: { path, query: { query_string: { query: string } } },
                        })),
                    ],
                },
            };
        }
        return [
            {
                match_phrase_prefix: { name: string },
            },
            {
                match: { "code.text": string },
            },
            {
                nested: {
                    path: "positions",
                    query: { match: { "positions.code.text": string } },
                },
            },
        ];
    }
    async search(params) {
        const { string, nested, filter, grants, facets, rerank, window } = params;
        try {
            const searchBody = {
                query: {
                    bool: {
                        should: this.getshould(string, nested),
                        minimum_should_match: 1,
                        filter: {
                            bool: {
                                must: filter,
                                should: grants,
                                minimum_should_match: grants.length > 0 ? 1 : 0,
                            },
                        },
                    },
                },
                sort: rerank,
                aggs: facets,
            };
            const response = await this.esClient.search({
                index: this.esConfig.alias,
                type: this.esConfig.dtype,
                body: searchBody,
                from: window.from,
                size: window.size,
            });
            return {
                summary: { total: response.body.hits.total.value },
                results: response.body.hits.hits.map((hit) => hit._source),
                buckets: response.body.aggregations || {},
            };
        }
        catch (error) {
            this.logger.error("Unexpected search error", error);
            return { summary: { total: 0 }, results: [], buckets: {} };
        }
    }
    async count(body) {
        try {
            const response = await this.esClient.count({
                index: this.esConfig.alias,
                type: this.esConfig.dtype,
                body,
            });
            return response.body.count;
        }
        catch (error) {
            if (error instanceof Error &&
                error.message === "search_phase_execution_exception")
                return 0;
            throw error;
        }
    }
}
exports.SearchService = SearchService;
