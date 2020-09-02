/// <reference types="node" />
import { Connection as UnsignedConnection } from "@elastic/elasticsearch";
import { ClientRequest, IncomingMessage } from "http";
declare class AwsElasticsearchError extends Error {
}
declare type RequestOptions = Parameters<UnsignedConnection["request"]>[0];
declare class AwsSignedConnection extends UnsignedConnection {
    request(params: RequestOptions, callback: (err: Error | null, response: IncomingMessage | null) => void): ClientRequest;
    private signParams;
}
export { AwsSignedConnection, UnsignedConnection, AwsElasticsearchError };
