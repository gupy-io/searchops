"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.getRandomConfig = exports.getTestClient = exports.getRandomSnakeCase = void 0;
const elasticsearch_1 = require("@elastic/elasticsearch");
const faker_1 = require("faker");
function getRandomSnakeCase() {
    return faker_1.random.word().replace(/\W/g, "_").toLowerCase();
}
exports.getRandomSnakeCase = getRandomSnakeCase;
function getTestClient() {
    var _a, _b;
    const elasticHost = (_a = process.env.ELASTIC_HOST) !== null && _a !== void 0 ? _a : "localhost";
    const elasticPort = (_b = process.env.ELASTIC_PORT) !== null && _b !== void 0 ? _b : "9200";
    const esClient = new elasticsearch_1.Client({
        node: `http://${elasticHost}:${elasticPort}`,
    });
    esClient.on("response", (error, result) => {
        if (error)
            console.log(JSON.stringify(result, null, 2));
    });
    return esClient;
}
exports.getTestClient = getTestClient;
function getRandomConfig() {
    return {
        index: getRandomSnakeCase(),
        alias: getRandomSnakeCase(),
        dtype: "_doc",
        settings: {
            number_of_shards: "1",
            number_of_replicas: "1",
            refresh_interval: "1ms",
        },
        mappings: {},
    };
}
exports.getRandomConfig = getRandomConfig;
