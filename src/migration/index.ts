import { Client } from "@elastic/elasticsearch";
import {
  Settings,
  GetSettingsResponse,
  Mappings,
  GetMappingsResponse,
} from "../es-types";

import { Config } from "../service";
import { deepEqual, deepPatch } from "../object/deep";

export class IndexManager {
  private esClient: Client;
  private esConfig: Config;
  private triggerUpdate: boolean;
  private allowLockdown: boolean;

  public constructor({
    esClient,
    esConfig,
    triggerUpdate = false,
    allowLockdown = false,
  }: {
    esClient: Client;
    esConfig: Config;
    triggerUpdate?: boolean;
    allowLockdown?: boolean;
  }) {
    this.esClient = esClient;
    this.esConfig = esConfig;
    this.triggerUpdate = triggerUpdate;
    this.allowLockdown = allowLockdown;
  }

  public async migrate(): Promise<void> {
    if (!(await this.existsIndex()) && !(await this.existsAlias())) {
      await this.migrateNewIndex();
    } else {
      await this.migrateOldIndex();
    }
  }

  private async migrateNewIndex(): Promise<void> {
    await this.createIndex();
    await this.assignAlias();
  }

  private async migrateOldIndex(): Promise<void> {
    try {
      if (!deepEqual(await this.getSettings(), this.esConfig.settings)) {
        await this.putSettings();
      }
      if (!deepEqual(await this.getMappings(), this.esConfig.mappings)) {
        await this.putMappings();
      }
    } catch (error) {
      if (this.allowLockdown) await this.migrateLockdown();
      else throw error;
    }
  }

  private async migrateLockdown(): Promise<void> {
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

  public async createIndex(name: string = this.esConfig.index): Promise<void> {
    await this.esClient.indices.create({
      index: name,
      include_type_name: false,
      body: {
        settings: this.esConfig.settings,
        mappings: this.esConfig.mappings,
      },
    });
  }

  public async existsIndex(
    index: string = this.esConfig.index
  ): Promise<boolean> {
    const { body: indexExists } = await this.esClient.indices.exists({ index });
    return indexExists;
  }

  public async getVersion(
    index: string = this.esConfig.index
  ): Promise<string> {
    const {
      body: {
        [index]: {
          settings: { index: settings },
        },
      },
    } = await this.esClient.indices.getSettings<GetSettingsResponse>({ index });
    return settings.version.created;
  }

  public async getSettings(
    index: string = this.esConfig.index
  ): Promise<Settings> {
    const {
      body: {
        [index]: {
          settings: { index: settings },
        },
      },
    } = await this.esClient.indices.getSettings<GetSettingsResponse>({ index });
    const readonlySettings: (keyof typeof settings)[] = [
      "uuid",
      "provided_name",
      "creation_date",
      "version",
    ];
    readonlySettings.forEach((key) => delete settings[key]);
    return settings;
  }

  public async putSettings(
    index: string = this.esConfig.index,
    settings: Settings = this.esConfig.settings
  ): Promise<void> {
    const settigsToPatch = deepPatch(await this.getSettings(index), settings);
    if (settigsToPatch instanceof Object) {
      await this.esClient.indices.putSettings({ index, body: settigsToPatch });
    }
  }

  public async getMappings(
    index: string = this.esConfig.index
  ): Promise<Mappings> {
    const {
      body: {
        [index]: { mappings },
      },
    } = await this.esClient.indices.getMapping<GetMappingsResponse>({
      index,
      include_type_name: false,
    });
    return mappings;
  }

  public async putMappings(
    index: string = this.esConfig.index,
    mappings: Mappings = this.esConfig.mappings
  ): Promise<void> {
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

  public async deleteIndex(name: string = this.esConfig.index): Promise<void> {
    await this.esClient.indices.delete({ index: name });
  }

  public async assignAlias(
    index: string = this.esConfig.index,
    alias: string = this.esConfig.alias
  ): Promise<void> {
    await this.esClient.indices.updateAliases({
      body: { actions: [{ add: { index, alias } }] },
    });
  }

  public async existsAlias(
    index: string = this.esConfig.index,
    name: string = this.esConfig.alias
  ): Promise<boolean> {
    const { body: aliasExists } = await this.esClient.indices.existsAlias({
      index,
      name,
    });
    return aliasExists;
  }

  public async retireAlias(
    index: string = this.esConfig.index,
    alias: string = this.esConfig.alias
  ): Promise<void> {
    await this.esClient.indices.updateAliases({
      body: { actions: [{ remove: { index, alias } }] },
    });
  }

  public async openIndex(name: string = this.esConfig.index): Promise<void> {
    await this.esClient.indices.putSettings({
      index: name,
      body: { index: { blocks: { write: false } } },
    });
  }

  public async closeIndex(name: string = this.esConfig.index): Promise<void> {
    await this.esClient.indices.putSettings({
      index: name,
      body: { index: { blocks: { write: true } } },
    });
  }

  public async duplicate(
    sourceName: string,
    targetname: string
  ): Promise<void> {
    await this.esClient.reindex({
      body: { source: { index: sourceName }, dest: { index: targetname } },
    });
  }

  public async swap(sourceName: string, targetName: string): Promise<void> {
    await this.esClient.indices.updateAliases({
      body: {
        actions: [
          { remove: { index: sourceName, alias: this.esConfig.alias } },
          { add: { index: targetName, alias: this.esConfig.alias } },
        ],
      },
    });
  }

  public async refreshIndex(name: string = this.esConfig.index): Promise<void> {
    await this.esClient.indices.refresh({ index: name });
  }
}
