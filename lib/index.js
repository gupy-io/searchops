"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.SearchEngine = void 0;
const service_1 = require("./service");
const query_1 = require("./query");
const migration_1 = require("./migration");
class SearchEngine {
    constructor({ esClient, domain, namespace, settings, mappings, serialize, logger, }) {
        const actualPrefix = namespace ? `${namespace}_` : "";
        const esConfig = {
            alias: `${actualPrefix}${domain}`,
            index: `${actualPrefix}${domain}_index`,
            dtype: "_doc",
            settings: settings || {},
            mappings: mappings || {},
        };
        this.esClient = esClient;
        this.esConfig = esConfig;
        this.serialize = serialize;
        this.searchService = new service_1.SearchService({ esClient, esConfig, logger });
    }
    getQueryBuilder() {
        return new query_1.QueryBuilder({ docsProvider: this });
    }
    getIndexManager(triggerUpdate = false) {
        return new migration_1.IndexManager({
            esClient: this.esClient,
            esConfig: this.esConfig,
            triggerUpdate,
        });
    }
    async bulk(body, refresh) {
        await this.searchService.bulk(body, refresh);
    }
    index(entity) {
        return this.searchService.index(this.serialize(entity));
    }
    delete(docId, routing) {
        return this.searchService.delete(docId, routing);
    }
    deleteByQuery(query) {
        return this.searchService.deleteByQuery(query);
    }
    search(params) {
        return this.searchService.search(params);
    }
    count(body) {
        return this.searchService.count(body);
    }
}
exports.SearchEngine = SearchEngine;
