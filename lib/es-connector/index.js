"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.createElasticsearch = void 0;
const aws_sdk_1 = __importDefault(require("aws-sdk"));
const elasticsearch_1 = require("@elastic/elasticsearch");
const aws_1 = require("./aws");
let client;
exports.createElasticsearch = ({ elasticConfig, logger, }) => {
    if (!client) {
        const host = elasticConfig.elasticHost || "localhost";
        const port = elasticConfig.elasticPort || 9200;
        const protocol = elasticConfig.elasticProtocol || "http";
        client = new elasticsearch_1.Client({
            Connection: aws_sdk_1.default.config.credentials
                ? aws_1.AwsSignedConnection
                : aws_1.UnsignedConnection,
            node: `${protocol}://${host}:${port}`,
        });
        client.on("response", (_error, result) => {
            logger.silly(JSON.stringify(result, null, 2));
            if (result && result.warnings) {
                logger.warn(result.warnings);
            }
        });
    }
    return client;
};
