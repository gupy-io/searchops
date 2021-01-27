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
    IF ExistsIndex(cluster, index.name) THEN
        Assert(FALSE, "Index already exists")
    ELSE
        [
            aliases |-> cluster.aliases,
            indices |-> cluster.indices \union {index}
        ]

DeleteIndex(cluster, index_name) ==
    IF ~ExistsIndex(cluster, index_name) THEN
        Assert(FALSE, "Index does not exist")
    ELSE
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
    IF ExistsIndex(cluster, index_or_alias) THEN
        CHOOSE idx \in cluster.indices : idx.name = index_or_alias
    ELSE
        LET
            alias == CHOOSE als \in cluster.aliases : (als.index = index_or_alias \/ als.alias = index_or_alias)
        IN
            CHOOSE idx \in cluster.indices : idx.name = alias.index


ExistsDocument(cluster, index_or_alias, doc_id) ==
    LET
        index == IndexFromIndexOrAlias(cluster, index_or_alias)
    IN
        doc_id \in { doc.id : doc \in index.docs }

CreateDocument(cluster, index_or_alias, doc) ==
    IF ExistsDocument(cluster, index_or_alias, doc.id) THEN
        Assert(FALSE, "Document already exists")
    ELSE
        LET
            index == IndexFromIndexOrAlias(cluster, index_or_alias)
        IN
            [
                aliases |-> cluster.aliases,
                indices |-> (cluster.indices \ { index })
                    \union {[ name |-> index.name, docs |-> index.docs \union { doc } ]}
            ]

UpdateDocument(cluster, index_or_alias, doc) ==
    IF ~ExistsDocument(cluster, index_or_alias, doc.id) THEN
        Assert(FALSE, "Document does not exist")
    ELSE
        LET
            index == IndexFromIndexOrAlias(cluster, index_or_alias)
            prevs == CHOOSE prevs \in index.docs : prevs.id = doc.id
        IN
            [
                aliases |-> cluster.aliases,
                indices |-> (cluster.indices \ { index })
                    \union {[ name |-> index.name, docs |-> (index.docs \ { prevs }) \union { doc } ]}
            ]

UpsertDocument(cluster, index_or_alias, doc) ==
    IF ExistsDocument(cluster, index_or_alias, doc.id) THEN
        UpdateDocument(cluster, index_or_alias, doc)
    ELSE
        CreateDocument(cluster, index_or_alias, doc)

Search(cluster, index_or_alias) ==
    IF ExistsIndex(cluster, index_or_alias) THEN
        LET
            index == CHOOSE idx \in cluster.indices : idx.name = index_or_alias
        IN
            index.docs
    ELSE
        LET
            aliases == { als \in cluster.aliases : (als.index = index_or_alias \/ als.alias = index_or_alias) }
            indices == { idx \in cluster.indices : idx.name \in { als.index : als \in aliases } }
        IN
            UNION { idx.docs : idx \in indices }

Reindex(cluster, source_name, target_name) ==
    LET
        source_index == CHOOSE idx \in cluster.indices : idx.name = source_name
        target_index == CHOOSE idx \in cluster.indices : idx.name = target_name
        intersection == { doc.id : doc \in source_index.docs } \intersect { doc.id : doc \in target_index.docs }
        merged_union == target_index.docs \union { doc \in source_index.docs : doc.id \notin intersection }
    IN
        [
            aliases |-> cluster.aliases,
            indices |-> (cluster.indices \ { target_index })
                \union {[ name |-> target_name, docs |-> merged_union ]}
        ]

====
