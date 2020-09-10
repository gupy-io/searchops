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
Object.defineProperty(exports, "__esModule", { value: true });
exports.test = exports.context = void 0;
// plug Jest as testing framework
const jestGlobals = __importStar(require("@jest/globals"));
const context = jestGlobals.describe;
exports.context = context;
const exercise = jestGlobals.test;
const before = jestGlobals.beforeAll;
const after = jestGlobals.afterAll;
const expect = jestGlobals.expect;
const service_1 = require("../service");
const migration_1 = require("../migration");
const utils = __importStar(require("./utils"));
const fakeLogger = {
    error: () => ({}),
};
class IndexSteps {
    constructor(testWorld) {
        this.testWorld = testWorld;
    }
    wasCreated() {
        this.testWorld.context += " was created";
        this.testWorld.contextSetup.push(async () => {
            await this.testWorld.indexManager.migrate();
        });
        this.testWorld.contextTeardown.push(async () => {
            await this.testWorld.indexManager.deleteIndex();
        });
        return this;
    }
}
class CountSteps {
    constructor(testWorld) {
        this.testWorld = testWorld;
    }
    shouldBe(count) {
        this.testWorld.context += ` should count be equal to ${count}`;
        this.testWorld.expectationChecks.push(() => expect(this.testWorld.count).toEqual(count));
        return this;
    }
}
class DocumentSteps {
    constructor(testWorld) {
        this.testWorld = testWorld;
    }
    containing(parts) {
        this.testWorld.context += " containing some data";
        this.testWorld.document = { id: this.testWorld.document.id, ...parts };
        return this;
    }
    wasCreated() {
        this.testWorld.context += " was created";
        this.testWorld.contextSetup.push(async () => {
            await this.testWorld.searchService.index(this.testWorld.document, "wait_for");
        });
        return this;
    }
    shouldContain(parts) {
        this.testWorld.expectation += " should contain the specified parts";
        this.testWorld.expectationChecks.push(() => {
            const intersection = utils.collectDeepMembers(this.testWorld.document, parts);
            expect(intersection).toEqual(parts);
        });
        return this;
    }
}
class ServiceSteps {
    constructor(testWorld) {
        this.testWorld = testWorld;
    }
    requestsToIndex(parts) {
        this.testWorld.exercise += " requests to update";
        this.testWorld.exerciseRoutines.push(async () => {
            await this.testWorld.searchService.index({
                id: this.testWorld.document.id,
                ...(parts || this.testWorld.document),
            }, "wait_for");
        });
        return this;
    }
    retrievesTheDocument() {
        this.testWorld.exercise += " retrieves the document";
        this.testWorld.exerciseRoutines.push(async () => {
            this.testWorld.document = await this.testWorld.searchService.get(this.testWorld.document.id);
        });
        return this;
    }
    requestCount() {
        this.testWorld.exercise += " request count";
        this.testWorld.exerciseRoutines.push(async () => {
            this.testWorld.count = await this.testWorld.searchService.count({
                query: { match_all: {} },
            });
        });
        return this;
    }
}
class Scenario {
    constructor() {
        const esClient = utils.getTestClient();
        const esConfig = utils.getRandomConfig();
        this.testWorld = {
            searchService: new service_1.SearchService({
                esClient,
                esConfig,
                logger: fakeLogger,
            }),
            indexManager: new migration_1.IndexManager({ esClient, esConfig }),
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
        this.indexSteps = new IndexSteps(this.testWorld);
        this.documentSteps = new DocumentSteps(this.testWorld);
        this.operationSteps = new ServiceSteps(this.testWorld);
        this.countSteps = new CountSteps(this.testWorld);
    }
    givenTheIndex() {
        this.testWorld.context = "given the index";
        return this.indexSteps;
    }
    givenTheDocument() {
        this.testWorld.context = "given the document";
        return this.documentSteps;
    }
    whenTheService() {
        this.testWorld.exercise = "when the service";
        return this.operationSteps;
    }
    thenTheDocument() {
        this.testWorld.expectation = "then the document";
        return this.documentSteps;
    }
    thenTheCount() {
        this.testWorld.expectation = "then the count";
        return this.countSteps;
    }
    build() {
        context(this.testWorld.context, () => {
            // TODO: remove when jest>26.4.2 lands
            // eslint-disable-next-line @typescript-eslint/no-misused-promises
            this.testWorld.contextSetup.forEach((setUp) => before(setUp));
            context(this.testWorld.exercise, () => {
                exercise(this.testWorld.expectation, async () => {
                    await this.testWorld.exerciseRoutines.reduce((chain, routine) => chain.then(routine), Promise.resolve());
                    this.testWorld.expectationChecks.forEach((expectation) => expectation());
                });
                this.testWorld.contextTeardown.forEach(
                // TODO: remove when jest>26.4.2 lands
                // eslint-disable-next-line @typescript-eslint/no-misused-promises
                (tearDown) => after(tearDown));
            });
        });
    }
}
function test(description, definition) {
    return context(description, () => {
        const _ = new Scenario();
        definition(_);
        return _.build();
    });
}
exports.test = test;
