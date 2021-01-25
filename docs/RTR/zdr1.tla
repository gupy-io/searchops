---- MODULE zdr1 ----
EXTENDS TLC, Elasticsearch

(* --algorithm ZDR

variables
    documents = {},
    cluster = NewCluster([
        aliases |-> {
            [ alias |-> "idx_r", index |-> "idx_v1" ],
            [ alias |-> "idx_w", index |-> "idx_v1" ]
        },
        indices |-> {[ name |-> "idx_v1", docs |-> documents ]}
    ]);

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
        assert documents = Search(cluster, "idx_r");
end process

process search = "GET /_search"
begin
    SearchRequest:
        skip;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "fa09f57d" /\ chksum(tla) = "b80aeca9")
VARIABLES documents, cluster, pc

vars == << documents, cluster, pc >>

ProcSet == {"Zero Downtime Reindex"} \cup {"GET /_search"}

Init == (* Global variables *)
        /\ documents = {}
        /\ cluster =           NewCluster([
                         aliases |-> {
                             [ alias |-> "idx_r", index |-> "idx_v1" ],
                             [ alias |-> "idx_w", index |-> "idx_v1" ]
                         },
                         indices |-> {[ name |-> "idx_v1", docs |-> documents ]}
                     ])
        /\ pc = [self \in ProcSet |-> CASE self = "Zero Downtime Reindex" -> "CreateTarget"
                                        [] self = "GET /_search" -> "SearchRequest"]

CreateTarget == /\ pc["Zero Downtime Reindex"] = "CreateTarget"
                /\ cluster' = CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ])
                /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "CopyDocuments"]
                /\ UNCHANGED documents

CopyDocuments == /\ pc["Zero Downtime Reindex"] = "CopyDocuments"
                 /\ cluster' = Reindex(cluster, "idx_v1", "idx_v2")
                 /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "AtomicAliasSwap"]
                 /\ UNCHANGED documents

AtomicAliasSwap == /\ pc["Zero Downtime Reindex"] = "AtomicAliasSwap"
                   /\ cluster' =            UpdateAlias(cluster, {
                                     [ alias |-> "idx_r", index |-> "idx_v2" ],
                                     [ alias |-> "idx_w", index |-> "idx_v2" ]
                                 })
                   /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "DeleteSource"]
                   /\ UNCHANGED documents

DeleteSource == /\ pc["Zero Downtime Reindex"] = "DeleteSource"
                /\ cluster' = DeleteIndex(cluster, "idx_v1")
                /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Check"]
                /\ UNCHANGED documents

Check == /\ pc["Zero Downtime Reindex"] = "Check"
         /\ Assert(~ExistsIndex(cluster, "idx_v1"), 
                   "Failure of assertion at line 30, column 9.")
         /\ Assert(ExistsIndex(cluster, "idx_v2"), 
                   "Failure of assertion at line 31, column 9.")
         /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_r", index |-> "idx_v2" ]), 
                   "Failure of assertion at line 32, column 9.")
         /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_w", index |-> "idx_v2" ]), 
                   "Failure of assertion at line 33, column 9.")
         /\ Assert(documents = Search(cluster, "idx_r"), 
                   "Failure of assertion at line 34, column 9.")
         /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Done"]
         /\ UNCHANGED << documents, cluster >>

ZDR == CreateTarget \/ CopyDocuments \/ AtomicAliasSwap \/ DeleteSource
          \/ Check

SearchRequest == /\ pc["GET /_search"] = "SearchRequest"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["GET /_search"] = "Done"]
                 /\ UNCHANGED << documents, cluster >>

search == SearchRequest

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ZDR \/ search
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
