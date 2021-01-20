import { context, test } from "./test/language";

context("SearchService", () => {
  test("Creating new documents", (_) => {
    _.givenTheIndex().wasCreated();
    _.givenTheDocument().containing({ title: "Dr Who" });
    _.whenTheService().requestsToIndex().retrievesTheDocument();
    _.thenTheDocument().shouldContain({ title: "Dr Who" });
  });

  test("Changing nothing", (_) => {
    _.givenTheIndex().wasCreated();
    _.givenTheDocument().containing({ title: "Pokémon" }).wasCreated();
    _.whenTheService().requestsToIndex({}).retrievesTheDocument();
    _.thenTheDocument().shouldContain({ title: "Pokémon" });
  });

  test("Creating new fields", (_) => {
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

  test("Creating new deeply nested fields", (_) => {
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

  test("Updating old fields", (_) => {
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

  test("Updating old deeply nested fields", (_) => {
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

  test("Counting documents", (_) => {
    _.givenTheIndex().wasCreated();
    _.givenTheDocument().wasCreated();
    _.whenTheService().requestCount();
    _.thenTheCount().shouldBe(1);
  });

  test("Deleting documents by query", (_) => {
    _.givenTheIndex().wasCreated();
    _.givenTheDocument().containing({ id: "1" }).wasCreated();
    _.whenTheService().requestDeleteByQuery({ ids: ["1"] });
    _.whenTheManager().performsRefresh();
    _.whenTheService().requestCount();
    _.thenTheCount().shouldBe(0);
  });
});
