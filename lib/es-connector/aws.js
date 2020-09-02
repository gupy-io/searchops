"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    Object.defineProperty(o, k2, { enumerable: true, get: function() { return m[k]; } });
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.AwsElasticsearchError = exports.UnsignedConnection = exports.AwsSignedConnection = void 0;
const stream_1 = require("stream");
const elasticsearch_1 = require("@elastic/elasticsearch");
Object.defineProperty(exports, "UnsignedConnection", { enumerable: true, get: function () { return elasticsearch_1.Connection; } });
const AWS = __importStar(require("aws-sdk"));
const v4_1 = __importDefault(require("aws-sdk/lib/signers/v4"));
class AwsElasticsearchError extends Error {
}
exports.AwsElasticsearchError = AwsElasticsearchError;
class AwsSignedConnection extends elasticsearch_1.Connection {
    request(params, callback) {
        const signedParams = this.signParams(params);
        return super.request(signedParams, callback);
    }
    signParams(params) {
        const region = AWS.config.region || process.env.AWS_DEFAULT_REGION;
        if (!region)
            throw new AwsElasticsearchError("missing region configuration");
        if (!params.method)
            throw new AwsElasticsearchError("missing request method");
        if (!params.path)
            throw new AwsElasticsearchError("missing request path");
        if (!params.headers)
            throw new AwsElasticsearchError("missing request headers");
        const endpoint = new AWS.Endpoint(this.url.href);
        const request = new AWS.HttpRequest(endpoint, region);
        request.method = params.method;
        request.path = params.querystring
            ? `${params.path}/?${params.querystring}`
            : params.path;
        if (typeof params.body === "string")
            request.body = params.body;
        else if (params.body instanceof Buffer)
            request.body = params.body.toString();
        else if (params.body instanceof stream_1.Readable)
            throw new AwsElasticsearchError("unsupported");
        else if (params.body !== undefined && params.body !== null) {
            throw new AwsElasticsearchError("body type unhandled");
        }
        Object.entries(params.headers).forEach(([header, value]) => {
            if (typeof value === "string")
                request.headers[header] = value;
            else if (typeof value === "number")
                request.headers[header] = `${value}`;
            else if (Array.isArray(value))
                request.headers[header] = value.join("; ");
            else if (value !== undefined)
                throw new AwsElasticsearchError("header type unhandled");
        });
        request.headers.Host = endpoint.host;
        const signer = new v4_1.default(request, "es");
        signer.addAuthorization(AWS.config.credentials, new Date());
        return request;
    }
}
exports.AwsSignedConnection = AwsSignedConnection;
