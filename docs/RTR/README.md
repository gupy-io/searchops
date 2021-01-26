# Relocation Transparent Reindex

## Background

In a blog post from 2013, [Elastic explained how to perform a mapping migration
without downtime][1]. The process has been much facilitated by the [2016 release
of the Reindex API][2], but the overall strategy reproduced [here][3] and
[there][4] is basically the same:

1. Create an alias for the old index
2. Alter application clients to target the alias
3. Create the new index
4. Reindex data from old index to new index
5. Atomically update the alias to point to new index
6. Remove old index

"Zero Downtime" means you won't be getting `index_not_found_exception` errors,
but for some applications that's not enough. [Several][5] [others][6] [have][7]
[noticed][8] that this procedure does not take into account read and write
requests that arrive between and during each step. There's possibility of losing
new documents, corruption of existing documents and resurgence of deleted
documents, and given large indexes will take a while to complete the reindex
task, the probability of such indidents are high.

A more ambitious goal than "Zero Downtime" would be complete "Relocation
Transparency": *users should not be able to notice data relocation by inspecting
the system state*. This includes absence of 404 Resource Not Found responses,
but also of inconsistencies between query responses and inferences about
existing documents after any operations.

This analysis focus on system state snapshots but one should take note that
there are still other details that might affect user experience. For example,
operational aspects of the Elasticsearch cluster during the migration (as
reindex tasks can be resource intensive) can compromise complete transparency if
users notice application performance degrataion.

[1]: https://www.elastic.co/blog/changing-mapping-with-zero-downtime
[2]: https://www.elastic.co/blog/reindex-is-coming
[3]: https://medium.com/@aonrobot/elsaticsearch-reindex-zero-downtime-57edc01ba14f
[4]: https://stackoverflow.com/questions/42671187/rebuild-index-with-zero-downtime
[5]: https://blog.codecentric.de/en/2014/09/elasticsearch-zero-downtime-reindexing-problems-solutions/
[6]: https://engineering.carsguide.com.au/elasticsearch-zero-downtime-reindexing-e3a53000f0ac
[7]: https://summera.github.io/infrastructure/2016/07/04/reindexing-elasticsearch.html
[8]: https://stackoverflow.com/questions/48594229/elasticsearch-concurrent-updates-to-index-while-reindex-for-the-same-index-in

## Problem

Given a specified index in an Elasticsearch cluster, a client application that
may issue read requests targeting one alias and write requests targeting another
alias, and an existing set of documents, we want to find a sequence of index
management operations that migrates the old index to a new one, without users
perceiving inconsistencies between read responses and inferred states expected
as result of prior read and write requests.

## Nonsolutions

We will specify the system and proposed solutions in PlusCalc/[TLA+][]. If you
don't want to spin up the TLA Toolbox IDE, you can reproduce the findings with
Make.

[TLA+]: https://github.com/tlaplus/tlaplus

### Zero Downtime Reindex

We will start off with a system [specification](/docs/RTR/zdr.tla) for the
reindex procedure [presented by Elastic][1].

```
(* --algorithm ZDR
process ZDR = "Zero Downtime Reindex"
begin
    CreateTargetIndex:
        cluster := CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ]);
    CopyDocuments:
        cluster := Reindex(cluster, "idx_v1", "idx_v2");
    AtomicAliasSwap:
        cluster := UpdateAlias(cluster, {
            [ alias |-> "idx_r", index |-> "idx_v2" ],
            [ alias |-> "idx_w", index |-> "idx_v2" ]
        });
    DeleteSourceIndex:
        cluster := DeleteIndex(cluster, "idx_v1");
end process
end algorithm *)
```

If we want to check the "zero downtime" property of this system, we can add
another process that searches for documents and model check it to not terminate
with errors.

```
process search = "GET /_search"
variables response = {}
begin
    SearchRequest:
        response := Search(cluster, "idx_r");
end process
```

It indeed passes the check and can be said to have zero downtime. But if we want
to check the "relocation transparency" property, we can change the process to
create a new document and add an expectation about the state of existing
documents:

```
process create = "PUT /idx_w/_create/{id}"
variable doc = [ id |-> 10 ]
begin
    CreateRequest:
        known_documents := known_documents \union { doc };
        cluster := CreateDocument(cluster, "idx_w", doc);
    AssertCreated:
        assert StatesAreConsistent;
end process
```

The model checker spits an assertion error, as expected. More importantly, it
gives us the event history that lead to this violation:

```
$ tlc zdr1.tla | grep State
...
State 1: <Initial predicate>
State 2: <CreateTargetIndex line 73, col 22 to line 76, col 60 of module zdr1>
State 3: <CopyDocuments line 78, col 18 to line 81, col 56 of module zdr1>
State 4: <CreateRequest line 99, col 18 to line 103, col 30 of module zdr1>
State 5: <AtomicAliasSwap line 83, col 20 to line 89, col 58 of module zdr1>>
```

When a new document is created, it might be written to the old index after the
reindex copies existing documents to the new index but before the write alias is
swapped. This indeed leads to data loss because the new document lives only in
the old index and the whole index is later deleted.

### ZDR + Write To New

The immediate fix for the data loss scenario described on the zero downtime
reindex procedure is to perform writes in the new index. The expected drawback
is that until the read alias is changed to the new index, users will be served
with stale data, violating relocation transparency. Let's check it:

```
```

### ZDR + Write To New And Read From Both

### ZDR + Write To Both And Read From Old Until Reindex Is Done

One common addition to the standard ZDR procedure is to configure the
application to write to both indexes. This is often hand-waved as a solution,
but not immediately obvious on how to implement the dual write atomically and
how would the application know to engage on write duplication.

One way for the application to know a relocation is in progress would be to see
if the read alias is pointing to multiple indexes.

```
process create = "POST /idx_{v}/_create/{id}"
variable doc = [ id |-> 10, version |-> 1 ]
begin
    CheckIndexV1:
        if ExistsIndex(cluster, "idx_v1") then
    WriteIndexV1:
            cluster := CreateDocument(cluster, "idx_v1", doc);
        end if;
    CheckIndexV2:
        if ExistsIndex(cluster, "idx_v2") then
    WriteIndexV2:
            cluster := CreateDocument(cluster, "idx_v2", doc);
        end if;
    Check:
        known_documents := known_documents \union { doc };
        assert StatesAreConsistent;
end process
```

Sure enough, the model check errors because between the request that informs the
client that an index exists and the request to create the document on said
index, the index might have been deleted.

Elasticsearch
doesn't allow writing to an alias that points to multiple indexes, so the only
way to write to two indices in a single request is to use the [Bulk API][bulk].

If the application is to decide at runtime if it needs to dual write, there's
yet another atomocity problem.

Let's be generous
and suppose that the application is able to decide to and perform the dual write
in a single step.

With this method of creating new documents, the model checks successfully! This
means that if the application only appends new documents, duplicate writes will
achieve the desired relocation transparency. What happens if we want to update
existing documents? Let's try to peform duplicated updates, though this it's a
bit more convoluted than creates because we need to check if the document
already exists too:

```
```

[bulk]: https://www.elastic.co/guide/en/elasticsearch/reference/current/docs-bulk.html

## Proposal

## Proof

## FAQ

1. Reindexing is not an atomic operation, it takes a while to complete and can
   fail halfway through. Wouldn't you have to take this into account?

    There's no loss of generality on modeling it as atomic because the failure
    modes of a multi-step reindex are the same as those expected in "about to
    start" reindex (non-empty set of documents in old index but not in new
    index).
