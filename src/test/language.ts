import { describe, test, beforeAll, afterAll } from "@jest/globals";
import winston from "winston";
import { Config, Document, SearchService, SimpleQuery } from "../service";
import { IndexManager } from "../migration";
import * as utils from "./utils";

const logger = winston.createLogger({
  transports: [
    new winston.transports.Console({
      format: winston.format.simple(),
    }),
  ],
  silent: true,
  level: "debug",
});

interface TestDocument extends Document {
  id: string;
  title?: string;
  subtitle?: string;
  author?: {
    address?: {
      street?: string;
      country?: string;
    };
    contact?: {
      phone?: string;
      email?: string;
    };
  };
}

interface TestWorld {
  esConfig: Config;
  indexManager: IndexManager;
  searchService: SearchService<TestDocument>;
  document: TestDocument;
  count: number;
  context: string;
  contextSetup: (() => void | Promise<void>)[];
  contextTeardown: (() => void | Promise<void>)[];
  exercise: string;
  exerciseRoutines: (() => void | Promise<void>)[];
  expectation: string;
  expectationChecks: (() => void | Promise<void>)[];
}

class IndexManagerSteps {
  private testWorld: TestWorld;

  public constructor(testWorld: TestWorld) {
    this.testWorld = testWorld;
  }

  public performsMigration(): IndexManagerSteps {
    this.testWorld.exercise += " performs a migration";
    this.testWorld.exerciseRoutines.push(async () => {
      await this.testWorld.indexManager.migrate();
    });
    this.testWorld.contextTeardown.push(async () => {
      await this.testWorld.indexManager.deleteIndex();
    });
    return this;
  }

  public performsRefresh(): IndexManagerSteps {
    this.testWorld.exercise += " performs a refresh";
    this.testWorld.exerciseRoutines.push(async () => {
      await this.testWorld.indexManager.refreshIndex();
    });
    return this;
  }
}

class IndexSteps {
  private testWorld: TestWorld;

  public constructor(testWorld: TestWorld) {
    this.testWorld = testWorld;
  }

  public wasCreated(): IndexSteps {
    this.testWorld.context += " was created";
    this.testWorld.contextSetup.push(async () => {
      await this.testWorld.indexManager.migrate();
    });
    this.testWorld.contextTeardown.push(async () => {
      await this.testWorld.indexManager.deleteIndex();
    });
    return this;
  }

  public wasNotCreated(): IndexSteps {
    this.testWorld.context += " was not created";
    this.testWorld.contextSetup.push(async () => {
      expect(await this.testWorld.indexManager.existsIndex()).toBeFalse();
      expect(await this.testWorld.indexManager.existsAlias()).toBeFalse();
    });
    return this;
  }

  public shouldExist(): IndexSteps {
    this.testWorld.expectation += " should exist";
    this.testWorld.expectationChecks.push(async () => {
      expect(await this.testWorld.indexManager.existsIndex()).toBeTrue();
      expect(await this.testWorld.indexManager.existsAlias()).toBeTrue();
      expect(await this.testWorld.indexManager.getSettings()).toEqual(
        this.testWorld.esConfig.settings
      );
    });
    return this;
  }
}

class CountSteps {
  private testWorld: TestWorld;

  public constructor(testWorld: TestWorld) {
    this.testWorld = testWorld;
  }

  public shouldBe(count: number): CountSteps {
    this.testWorld.context += ` should count be equal to ${count}`;
    this.testWorld.expectationChecks.push(() =>
      expect(this.testWorld.count).toEqual(count)
    );
    return this;
  }
}

class DocumentSteps {
  private testWorld: TestWorld;

  public constructor(testWorld: TestWorld) {
    this.testWorld = testWorld;
  }

  public containing(parts: Partial<TestDocument>): DocumentSteps {
    this.testWorld.context += " containing some data";
    this.testWorld.document = { id: this.testWorld.document.id, ...parts };
    return this;
  }

  public wasCreated(): DocumentSteps {
    this.testWorld.context += " was created";
    this.testWorld.contextSetup.push(async () => {
      await this.testWorld.searchService.index(
        this.testWorld.document,
        "wait_for"
      );
    });
    return this;
  }

  public shouldContain(parts: Partial<TestDocument>): DocumentSteps {
    this.testWorld.expectation += " should contain the specified parts";
    this.testWorld.expectationChecks.push(() => {
      expect(this.testWorld.document).toContainEntries<Record<string, unknown>>(
        Object.entries(parts)
      );
    });
    return this;
  }
}

class ServiceSteps {
  private testWorld: TestWorld;

  public constructor(testWorld: TestWorld) {
    this.testWorld = testWorld;
  }

  public requestsToIndex(parts?: Partial<TestDocument>): ServiceSteps {
    this.testWorld.exercise += " requests to update";
    this.testWorld.exerciseRoutines.push(async () => {
      await this.testWorld.searchService.index(
        {
          id: this.testWorld.document.id,
          ...(parts || this.testWorld.document),
        },
        "wait_for"
      );
    });
    return this;
  }

  public retrievesTheDocument(): ServiceSteps {
    this.testWorld.exercise += " retrieves the document";
    this.testWorld.exerciseRoutines.push(async () => {
      this.testWorld.document = await this.testWorld.searchService.get(
        this.testWorld.document.id
      );
    });
    return this;
  }

  public requestCount(): ServiceSteps {
    this.testWorld.exercise += " request count";
    this.testWorld.exerciseRoutines.push(async () => {
      this.testWorld.count = await this.testWorld.searchService.count({
        query: { match_all: {} },
      });
    });
    return this;
  }

  public requestDeleteByQuery(query: SimpleQuery): ServiceSteps {
    this.testWorld.exercise += " request delete by query";
    this.testWorld.exerciseRoutines.push(async () => {
      await this.testWorld.searchService.deleteByQuery(query);
    });
    return this;
  }
}

class Scenario {
  private testWorld: TestWorld;
  private indexManagerSteps: IndexManagerSteps;
  private indexSteps: IndexSteps;
  private documentSteps: DocumentSteps;
  private operationSteps: ServiceSteps;
  private countSteps: CountSteps;

  public constructor() {
    const esClient = utils.getTestClient(logger);
    const esConfig = utils.getRandomConfig();

    this.testWorld = {
      esConfig,
      indexManager: new IndexManager({ esClient, esConfig }),
      searchService: new SearchService({
        esClient,
        esConfig,
        logger: logger,
      }),
      document: { id: utils.getRandomSnakeCase() },
      count: 0,
      context: "",
      contextSetup: [],
      contextTeardown: [],
      exercise: "",
      exerciseRoutines: [],
      expectation: "",
      expectationChecks: [],
    };
    this.indexManagerSteps = new IndexManagerSteps(this.testWorld);
    this.indexSteps = new IndexSteps(this.testWorld);
    this.documentSteps = new DocumentSteps(this.testWorld);
    this.operationSteps = new ServiceSteps(this.testWorld);
    this.countSteps = new CountSteps(this.testWorld);
  }

  public givenTheIndex(): IndexSteps {
    this.testWorld.context = "given the index";
    return this.indexSteps;
  }

  public givenTheDocument(): DocumentSteps {
    this.testWorld.context = "given the document";
    return this.documentSteps;
  }

  public whenTheManager(): IndexManagerSteps {
    this.testWorld.exercise = "when the manager";
    return this.indexManagerSteps;
  }

  public whenTheService(): ServiceSteps {
    this.testWorld.exercise = "when the service";
    return this.operationSteps;
  }

  public thenTheIndex(): IndexSteps {
    this.testWorld.expectation = "then the index";
    return this.indexSteps;
  }

  public thenTheDocument(): DocumentSteps {
    this.testWorld.expectation = "then the document";
    return this.documentSteps;
  }

  public thenTheCount(): CountSteps {
    this.testWorld.expectation = "then the count";
    return this.countSteps;
  }

  public build(): void {
    describe(this.testWorld.context, () => {
      describe(this.testWorld.exercise, () => {
        // TODO: remove eslint-disable after https://github.com/facebook/jest/issues/10066
        /* eslint-disable @typescript-eslint/no-floating-promises */
        /* eslint-disable @typescript-eslint/no-misused-promises */
        beforeAll(() =>
          this.testWorld.contextSetup.reduce(
            (chain, setUp) => chain.then(setUp),
            Promise.resolve()
          )
        );
        test(this.testWorld.expectation, async () => {
          await this.testWorld.exerciseRoutines.reduce(
            (chain, routine) => chain.then(routine),
            Promise.resolve()
          );
          await this.testWorld.expectationChecks.reduce(
            (chain, expectation) => chain.then(expectation),
            Promise.resolve()
          );
        });
        // TODO: remove eslint-disable after https://github.com/facebook/jest/issues/10066
        /* eslint-disable @typescript-eslint/no-floating-promises */
        /* eslint-disable @typescript-eslint/no-misused-promises */
        afterAll(() =>
          this.testWorld.contextTeardown.reduce(
            (chain, tearDown) => chain.then(tearDown),
            Promise.resolve()
          )
        );
      });
    });
  }
}

function testz(description: string, definition: (_: Scenario) => void): void {
  return describe(description, () => {
    const _ = new Scenario();
    definition(_);
    return _.build();
  });
}

export { describe as context } from "@jest/globals";
export { testz as test };
