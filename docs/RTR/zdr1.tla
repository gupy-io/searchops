---- MODULE zdr1 ----
EXTENDS TLC, Elasticsearch

(* --algorithm ZDR

variables
    known_documents = {},
    cluster = NewCluster([
        aliases |-> {
            [ alias |-> "idx_r", index |-> "idx_v1" ],
            [ alias |-> "idx_w", index |-> "idx_v1" ]
        },
        indices |-> {[ name |-> "idx_v1", docs |-> known_documents ]}
    ]);

define
    StatesAreConsistent == Search(cluster, "idx_r") = known_documents
end define;

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
    Check:
        assert ~ExistsIndex(cluster, "idx_v1");
        assert ExistsIndex(cluster, "idx_v2");
        assert ExistsAlias(cluster, [ alias |-> "idx_r", index |-> "idx_v2" ]);
        assert ExistsAlias(cluster, [ alias |-> "idx_w", index |-> "idx_v2" ]);
end process

process create = "PUT /idx_w/_create/{id}"
variable doc = [ id |-> 10 ]
begin
    CreateRequest:
        known_documents := known_documents \union { doc };
        cluster := CreateDocument(cluster, "idx_w", doc);
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "10993988" /\ chksum(tla) = "356777bd")
VARIABLES known_documents, cluster, pc

(* define statement *)
StatesAreConsistent == Search(cluster, "idx_r") = known_documents

VARIABLE doc

vars == << known_documents, cluster, pc, doc >>

ProcSet == {"Zero Downtime Reindex"} \cup {"PUT /idx_w/_create/{id}"}

Init == (* Global variables *)
        /\ known_documents = {}
        /\ cluster =           NewCluster([
                         aliases |-> {
                             [ alias |-> "idx_r", index |-> "idx_v1" ],
                             [ alias |-> "idx_w", index |-> "idx_v1" ]
                         },
                         indices |-> {[ name |-> "idx_v1", docs |-> known_documents ]}
                     ])
        (* Process create *)
        /\ doc = [ id |-> 10 ]
        /\ pc = [self \in ProcSet |-> CASE self = "Zero Downtime Reindex" -> "CreateTargetIndex"
                                        [] self = "PUT /idx_w/_create/{id}" -> "CreateRequest"]

CreateTargetIndex == /\ pc["Zero Downtime Reindex"] = "CreateTargetIndex"
                     /\ cluster' = CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ])
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "CopyDocuments"]
                     /\ UNCHANGED << known_documents, doc >>

CopyDocuments == /\ pc["Zero Downtime Reindex"] = "CopyDocuments"
                 /\ cluster' = Reindex(cluster, "idx_v1", "idx_v2")
                 /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "AtomicAliasSwap"]
                 /\ UNCHANGED << known_documents, doc >>

AtomicAliasSwap == /\ pc["Zero Downtime Reindex"] = "AtomicAliasSwap"
                   /\ cluster' =            UpdateAlias(cluster, {
                                     [ alias |-> "idx_r", index |-> "idx_v2" ],
                                     [ alias |-> "idx_w", index |-> "idx_v2" ]
                                 })
                   /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "DeleteSourceIndex"]
                   /\ UNCHANGED << known_documents, doc >>

DeleteSourceIndex == /\ pc["Zero Downtime Reindex"] = "DeleteSourceIndex"
                     /\ cluster' = DeleteIndex(cluster, "idx_v1")
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Check"]
                     /\ UNCHANGED << known_documents, doc >>

Check == /\ pc["Zero Downtime Reindex"] = "Check"
         /\ Assert(~ExistsIndex(cluster, "idx_v1"), 
                   "Failure of assertion at line 34, column 9.")
         /\ Assert(ExistsIndex(cluster, "idx_v2"), 
                   "Failure of assertion at line 35, column 9.")
         /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_r", index |-> "idx_v2" ]), 
                   "Failure of assertion at line 36, column 9.")
         /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_w", index |-> "idx_v2" ]), 
                   "Failure of assertion at line 37, column 9.")
         /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Done"]
         /\ UNCHANGED << known_documents, cluster, doc >>

ZDR == CreateTargetIndex \/ CopyDocuments \/ AtomicAliasSwap
          \/ DeleteSourceIndex \/ Check

CreateRequest == /\ pc["PUT /idx_w/_create/{id}"] = "CreateRequest"
                 /\ known_documents' = (known_documents \union { doc })
                 /\ cluster' = CreateDocument(cluster, "idx_w", doc)
                 /\ pc' = [pc EXCEPT !["PUT /idx_w/_create/{id}"] = "Done"]
                 /\ doc' = doc

create == CreateRequest

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ZDR \/ create
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
