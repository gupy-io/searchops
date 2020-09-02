import { Client } from "@elastic/elasticsearch";
import { Config } from "./service";
import { Settings, Mappings } from "./es-types";
export declare class IndexManager {
    private esClient;
    private esConfig;
    private triggerUpdate;
    private allowLockdown;
    constructor({ esClient, esConfig, triggerUpdate, allowLockdown, }: {
        esClient: Client;
        esConfig: Config;
        triggerUpdate?: boolean;
        allowLockdown?: boolean;
    });
    migrate(): Promise<void>;
    private migrateNewIndex;
    private migrateOldIndex;
    private migrateLockdown;
    createIndex(name?: string): Promise<void>;
    existsIndex(index?: string): Promise<boolean>;
    getVersion(index?: string): Promise<string>;
    getSettings(index?: string): Promise<Settings>;
    putSettings(index?: string, settings?: Settings): Promise<void>;
    getMappings(index?: string): Promise<Mappings>;
    putMappings(index?: string, mappings?: Mappings): Promise<void>;
    deleteIndex(name?: string): Promise<void>;
    assignAlias(index?: string, alias?: string): Promise<void>;
    existsAlias(index?: string, name?: string): Promise<boolean>;
    retireAlias(index?: string, alias?: string): Promise<void>;
    openIndex(name?: string): Promise<void>;
    closeIndex(name?: string): Promise<void>;
    duplicate(sourceName: string, targetname: string): Promise<void>;
    swap(sourceName: string, targetName: string): Promise<void>;
}
