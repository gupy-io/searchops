declare const context: import("@jest/types/build/Global").Describe;
import { Document, SearchService } from "../service";
import { IndexManager } from "../migration";
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
    searchService: SearchService<TestDocument>;
    indexManager: IndexManager;
    document: TestDocument;
    count: number;
    context: string;
    contextSetup: (() => Promise<void>)[];
    contextTeardown: (() => Promise<void>)[];
    exercise: string;
    exerciseRoutines: (() => Promise<void>)[];
    expectation: string;
    expectationChecks: (() => void)[];
}
declare class IndexSteps {
    private testWorld;
    constructor(testWorld: TestWorld);
    wasCreated(): IndexSteps;
}
declare class CountSteps {
    private testWorld;
    constructor(testWorld: TestWorld);
    shouldBe(count: number): CountSteps;
}
declare class DocumentSteps {
    private testWorld;
    constructor(testWorld: TestWorld);
    containing(parts: Partial<TestDocument>): DocumentSteps;
    wasCreated(): DocumentSteps;
    shouldContain(parts: Partial<TestDocument>): DocumentSteps;
}
declare class ServiceSteps {
    private testWorld;
    constructor(testWorld: TestWorld);
    requestsToIndex(parts?: Partial<TestDocument>): ServiceSteps;
    retrievesTheDocument(): ServiceSteps;
    requestCount(): ServiceSteps;
}
declare class Scenario {
    private testWorld;
    private indexSteps;
    private documentSteps;
    private operationSteps;
    private countSteps;
    constructor();
    givenTheIndex(): IndexSteps;
    givenTheDocument(): DocumentSteps;
    whenTheService(): ServiceSteps;
    thenTheDocument(): DocumentSteps;
    thenTheCount(): CountSteps;
    build(): void;
}
declare function test(description: string, definition: (_: Scenario) => void): void;
export { context, test };
