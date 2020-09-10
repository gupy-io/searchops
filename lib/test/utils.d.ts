import { Client } from "@elastic/elasticsearch";
import { Config } from "../service";
export declare function getRandomSnakeCase(): string;
export declare function getTestClient(): Client;
export declare function getRandomConfig(): Config;
export declare type RecursivePartial<T> = {
    [P in keyof T]?: RecursivePartial<T[P]>;
};
