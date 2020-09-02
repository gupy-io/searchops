import { Client } from "@elastic/elasticsearch";
import { Config } from "../service";
export declare function getRandomSnakeCase(): string;
export declare function getTestClient(): Client;
export declare function getRandomConfig(): Config;
export declare function collectDeepMembers(object: any, structure: any): object;
