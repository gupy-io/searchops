"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const globals_1 = require("@jest/globals");
const language_1 = require("./test/language");
globals_1.describe("SearchService @integration", () => {
    language_1.scenario("Creating new documents", (_) => {
        _.givenTheIndex().wasCreated();
        _.givenTheDocument().containing({ title: "Dr Who" });
        _.whenTheService().requestsToIndex().retrievesTheDocument();
        _.thenTheDocument().shouldContain({ title: "Dr Who" });
    });
    language_1.scenario("Changing nothing", (_) => {
        _.givenTheIndex().wasCreated();
        _.givenTheDocument().containing({ title: "Pokémon" }).wasCreated();
        _.whenTheService().requestsToIndex({}).retrievesTheDocument();
        _.thenTheDocument().shouldContain({ title: "Pokémon" });
    });
    language_1.scenario("Creating new fields", (_) => {
        _.givenTheIndex().wasCreated();
        _.givenTheDocument().containing({ title: "Pokémon" }).wasCreated();
        _.whenTheService()
            .requestsToIndex({ subtitle: "FireRed Version" })
            .retrievesTheDocument();
        _.thenTheDocument().shouldContain({
            title: "Pokémon",
            subtitle: "FireRed Version",
        });
    });
    language_1.scenario("Creating new deeply nested fields", (_) => {
        _.givenTheIndex().wasCreated();
        _.givenTheDocument()
            .containing({ author: { address: { street: "Sesame" } } })
            .wasCreated();
        _.whenTheService()
            .requestsToIndex({
            author: {
                address: { country: "Muppetland" },
                contact: { email: "jim@muppets.fun" },
            },
        })
            .retrievesTheDocument();
        _.thenTheDocument().shouldContain({
            author: {
                address: { street: "Sesame", country: "Muppetland" },
                contact: { email: "jim@muppets.fun" },
            },
        });
    });
    language_1.scenario("Updating old fields", (_) => {
        _.givenTheIndex().wasCreated();
        _.givenTheDocument()
            .containing({ title: "Pokémon", subtitle: "Green Version" })
            .wasCreated();
        _.whenTheService()
            .requestsToIndex({ subtitle: "LeafGreen Version" })
            .retrievesTheDocument();
        _.thenTheDocument().shouldContain({
            title: "Pokémon",
            subtitle: "LeafGreen Version",
        });
    });
    language_1.scenario("Updating old deeply nested fields", (_) => {
        _.givenTheIndex().wasCreated();
        _.givenTheDocument()
            .containing({
            author: {
                address: { street: "Sesame", country: "Muppetland" },
                contact: { email: "jim@muppets.fun" },
            },
        })
            .wasCreated();
        _.whenTheService()
            .requestsToIndex({
            author: {
                address: { country: "Puppetland" },
                contact: { email: "jim@muppets.org" },
            },
        })
            .retrievesTheDocument();
        _.thenTheDocument().shouldContain({
            author: {
                address: { street: "Sesame", country: "Puppetland" },
                contact: { email: "jim@muppets.org" },
            },
        });
    });
    language_1.scenario("Counting documents", (_) => {
        _.givenTheIndex().wasCreated();
        _.givenTheDocument().containing({ title: "Digimón" }).wasCreated();
        _.whenTheService().requestCount();
        _.thenTheCount().shouldBe(1);
    });
});
