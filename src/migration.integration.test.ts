import { context, test } from "./test/language";

context("Index Migrations", () => {
  test("Creating a new index", (_) => {
    _.givenTheIndex().wasNotCreated();
    _.whenTheManager().performsMigration();
    _.thenTheIndex().shouldExist();
  });
  test("Checking an existing index", (_) => {
    _.givenTheIndex().wasCreated();
    _.whenTheManager().performsMigration();
    _.thenTheIndex().shouldExist();
  });
  test("Updating dynamic index settings", (_) => {
    _.givenTheIndex().wasCreated();
    _.whenTheManager().performsMigration();
    _.thenTheIndex().shouldExist();
  });
  test("Updating dynamic index settings", (_) => {
    _.givenTheIndex().wasCreated();
    _.whenTheManager().performsMigration();
    _.thenTheIndex().shouldExist();
  });
  test("Updating dynamic index mappings", (_) => {
    _.givenTheIndex().wasCreated();
    _.whenTheManager().performsMigration();
    _.thenTheIndex().shouldExist();
  });
  test("Updating static index mappings", (_) => {
    _.givenTheIndex().wasCreated();
    _.whenTheManager().performsMigration();
    _.thenTheIndex().shouldExist();
  });
});
