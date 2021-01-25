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

## Nonsolutions

## Proposal

## Proof
