"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.IndexManager = void 0;
const deep_1 = require("./object/deep");
class IndexManager {
    constructor({ esClient, esConfig, triggerUpdate = false, allowLockdown = false, }) {
        this.esClient = esClient;
        this.esConfig = esConfig;
        this.triggerUpdate = triggerUpdate;
        this.allowLockdown = allowLockdown;
    }
    async migrate() {
        if (!(await this.existsIndex()) && !(await this.existsAlias())) {
            await this.migrateNewIndex();
        }
        else {
            await this.migrateOldIndex();
        }
    }
    async migrateNewIndex() {
        await this.createIndex();
        await this.assignAlias();
    }
    async migrateOldIndex() {
        try {
            if (!deep_1.deepEqual(await this.getSettings(), this.esConfig.settings)) {
                await this.putSettings();
            }
            if (!deep_1.deepEqual(await this.getMappings(), this.esConfig.mappings)) {
                await this.putMappings();
            }
        }
        catch (error) {
            if (this.allowLockdown)
                await this.migrateLockdown();
            else
                throw error;
        }
    }
    async migrateLockdown() {
        const stageIndex = `${this.esConfig.index}_tmp`;
        await this.createIndex(stageIndex);
        await this.closeIndex();
        await this.duplicate(this.esConfig.index, stageIndex);
        await this.closeIndex(stageIndex);
        await this.swap(this.esConfig.index, stageIndex);
        await this.deleteIndex();
        await this.createIndex();
        await this.duplicate(stageIndex, this.esConfig.index);
        await this.swap(stageIndex, this.esConfig.index);
        await this.deleteIndex(stageIndex);
    }
    async createIndex(name = this.esConfig.index) {
        await this.esClient.indices.create({
            index: name,
            include_type_name: false,
            body: {
                settings: this.esConfig.settings,
                mappings: this.esConfig.mappings,
            },
        });
    }
    async existsIndex(index = this.esConfig.index) {
        const { body: indexExists } = await this.esClient.indices.exists({ index });
        return indexExists;
    }
    async getVersion(index = this.esConfig.index) {
        const { body: { [index]: { settings: { index: settings }, }, }, } = await this.esClient.indices.getSettings({ index });
        return settings.version.created;
    }
    async getSettings(index = this.esConfig.index) {
        const { body: { [index]: { settings: { index: settings }, }, }, } = await this.esClient.indices.getSettings({ index });
        const readonlySettings = [
            "uuid",
            "provided_name",
            "creation_date",
            "version",
        ];
        readonlySettings.forEach((key) => delete settings[key]);
        return settings;
    }
    async putSettings(index = this.esConfig.index, settings = this.esConfig.settings) {
        const settigsToPatch = deep_1.deepPatch(await this.getSettings(index), settings);
        if (settigsToPatch instanceof Object) {
            await this.esClient.indices.putSettings({ index, body: settigsToPatch });
        }
    }
    async getMappings(index = this.esConfig.index) {
        const { body: { [index]: config }, } = await this.esClient.indices.getMapping({
            index,
            include_type_name: false,
        });
        // eslint-disable-next-line
        return config.mappings;
    }
    async putMappings(index = this.esConfig.index, mappings = this.esConfig.mappings) {
        await this.esClient.indices.putMapping({
            index,
            body: mappings,
            include_type_name: false,
        });
        if (this.triggerUpdate) {
            await this.esClient.updateByQuery({
                index,
                conflicts: "proceed",
                wait_for_completion: true,
            });
        }
    }
    async deleteIndex(name = this.esConfig.index) {
        await this.esClient.indices.delete({ index: name });
    }
    async assignAlias(index = this.esConfig.index, alias = this.esConfig.alias) {
        await this.esClient.indices.updateAliases({
            body: { actions: [{ add: { index, alias } }] },
        });
    }
    async existsAlias(index = this.esConfig.index, name = this.esConfig.alias) {
        const { body: aliasExists } = await this.esClient.indices.existsAlias({
            index,
            name,
        });
        return aliasExists;
    }
    async retireAlias(index = this.esConfig.index, alias = this.esConfig.alias) {
        await this.esClient.indices.updateAliases({
            body: { actions: [{ remove: { index, alias } }] },
        });
    }
    async openIndex(name = this.esConfig.index) {
        await this.esClient.indices.putSettings({
            index: name,
            body: { index: { blocks: { write: false } } },
        });
    }
    async closeIndex(name = this.esConfig.index) {
        await this.esClient.indices.putSettings({
            index: name,
            body: { index: { blocks: { write: true } } },
        });
    }
    async duplicate(sourceName, targetname) {
        await this.esClient.reindex({
            body: { source: { index: sourceName }, dest: { index: targetname } },
        });
    }
    async swap(sourceName, targetName) {
        await this.esClient.indices.updateAliases({
            body: {
                actions: [
                    { remove: { index: sourceName, alias: this.esConfig.alias } },
                    { add: { index: targetName, alias: this.esConfig.alias } },
                ],
            },
        });
    }
}
exports.IndexManager = IndexManager;
