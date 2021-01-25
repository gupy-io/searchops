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
but also inconsistencies between query responses and inferences about existing
documents after any operations.

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
reindex procedure presented [previously](#background).

```
(* --algorithm ZDR

variables
    known_documents = {[ id |-> 1 ], [ id |-> 2 ], [ id |-> 3 ]},
    cluster = NewCluster([
        aliases |-> {
            [ alias |-> "idx_r", index |-> "idx_v1" ],
            [ alias |-> "idx_w", index |-> "idx_v1" ]
        },
        indices |-> {[ name |-> "idx_v1", docs |-> known_documents ]}
    ]);

define
    ReadableDocuments == Search(cluster, "idx_r")
    StatesAreConsistent == ReadableDocuments = known_documents
    StatesAreEventuallyConsistent == <>[]StatesAreConsistent
end define;

process ZDR = "Zero Downtime Reindex"
begin
    CreateTarget:
        cluster := CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ]);
    CopyDocuments:
        cluster := Reindex(cluster, "idx_v1", "idx_v2");
    AtomicAliasSwap:
        cluster := UpdateAlias(cluster, {
            [ alias |-> "idx_r", index |-> "idx_v2" ],
            [ alias |-> "idx_w", index |-> "idx_v2" ]
        });
    DeleteSource:
        cluster := DeleteIndex(cluster, "idx_v1");
    Check:
        assert ~ExistsIndex(cluster, "idx_v1");
        assert ExistsIndex(cluster, "idx_v2");
        assert ExistsAlias(cluster, [ alias |-> "idx_r", index |-> "idx_v2" ]);
        assert ExistsAlias(cluster, [ alias |-> "idx_w", index |-> "idx_v2" ]);
end process
end algorithm *)
```

If we want to check the "zero downtime" property of this system, we can either
check for the temporal property `StatesAreConsistent` as an invariant or
manually add a searching user process that checks search results:

```
process search = "GET /_search"
begin
    SearchRequest:
        assert known_documents = Search(cluster, "idx_r");
end process
```

And indeed, with those verifications the model checks without errors. What if we
add a process that creates a document?

```
process create = "PUT /idx_w/_create/{id}"
variable doc = [ id |-> 10 ]
begin
    CreateRequest:
        known_documents := known_documents \union { doc };
        cluster := CreateDocument(cluster, "idx_w", doc);
end process
```

The model checker spits `Error: Invariant StatesAreConsistent is violated.`, as
expected. More importantly, it gives us the event history that lead this
violation:

```
$ tlc zdr1.tla
Error: Invariant StatesAreConsistent is violated.
State 1: <Initial predicate>
State 2: <CreateTargetIndex line 86, col 17 to line 89, col 55 of module zdr1>
State 3: <CopyDocuments line 91, col 18 to line 94, col 56 of module zdr1>
State 4: <CreateRequest line 124, col 18 to line 128, col 30 of module zdr1>
State 5: <AtomicAliasSwap line 96, col 20 to line 102, col 58 of module zdr1>
```

When a document is created, it might be written to the old index after the
reindex copies it to the new index but before the write alias is swapped. This
indeed leads to data loss.

## Proposal

## Proof
