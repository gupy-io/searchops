---- MODULE Elasticsearch ----
LOCAL INSTANCE TLC

NewCluster(cluster) ==
    [
        aliases |-> cluster.aliases,
        indices |-> cluster.indices
    ]

ExistsIndex(cluster, index_name) ==
    index_name \in {idx.name : idx \in cluster.indices}

CreateIndex(cluster, index) ==
    IF ExistsIndex(cluster, index.name)
    THEN Assert(FALSE, "Index already exists") ELSE
    [
        aliases |-> cluster.aliases,
        indices |-> cluster.indices \union {index}
    ]

DeleteIndex(cluster, index_name) ==
    IF ~ExistsIndex(cluster, index_name)
    THEN Assert(FALSE, "Index does not exist") ELSE
    LET
        index == CHOOSE idx \in cluster.indices : idx.name = index_name
    IN
    [
        aliases |-> cluster.aliases,
        indices |-> cluster.indices \ { index }
    ]

ExistsAlias(cluster, alias) ==
    alias \in cluster.aliases

UpdateAlias(cluster, aliases) ==
    [
        aliases |-> aliases,
        indices |-> cluster.indices
    ]

IndexFromIndexOrAlias(cluster, index_or_alias) ==
    LET
        alias == CHOOSE als \in cluster.aliases : (als.index = index_or_alias \/ als.alias = index_or_alias)
    IN
    CHOOSE idx \in cluster.indices : idx.name = alias.index


Search(cluster, index_or_alias) ==
    LET
        index == IndexFromIndexOrAlias(cluster, index_or_alias)
    IN
    index.docs

CreateDocument(cluster, index_or_alias, doc) ==
    LET
        index == IndexFromIndexOrAlias(cluster, index_or_alias)
    IN
    [
        aliases |-> cluster.aliases,
        indices |-> (cluster.indices \ { index })
            \union {[ name |-> index.name, docs |-> index.docs \union { doc } ]}
    ]


Reindex(cluster, source_name, target_name) ==
    LET
        source_index == CHOOSE idx \in cluster.indices : idx.name = source_name
        target_index == CHOOSE idx \in cluster.indices : idx.name = target_name
    IN
    [
        aliases |-> cluster.aliases,
        indices |-> (cluster.indices \ { target_index })
            \union {[ name |-> target_name, docs |-> source_index.docs ]}
    ]

====
