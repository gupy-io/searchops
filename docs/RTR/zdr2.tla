---- MODULE zdr2 ----
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

process ZDR = "Zero Downtime Reindex + Write To New"
begin
    CreateTargetIndex:
        cluster := CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ]);
    WritesToNewIndex:
        cluster := UpdateAlias(cluster, {
            [ alias |-> "idx_r", index |-> "idx_v1" ],
            [ alias |-> "idx_w", index |-> "idx_v2" ]
        });
    CopyDocuments:
        cluster := Reindex(cluster, "idx_v1", "idx_v2");
    ReadsToNewIndex:
        cluster := UpdateAlias(cluster, {
            [ alias |-> "idx_r", index |-> "idx_v2" ],
            [ alias |-> "idx_w", index |-> "idx_v2" ]
        });
    DeleteSourceIndex:
        cluster := DeleteIndex(cluster, "idx_v1");
end process

process create = "PUT /idx_w/_create/{id}"
variable doc = [ id |-> 10 ]
begin
    CreateRequest:
        known_documents := known_documents \union { doc };
        cluster := CreateDocument(cluster, "idx_w", doc);
    AssertCreated:
        assert StatesAreConsistent;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "64126a2e" /\ chksum(tla) = "ecf18e98")
VARIABLES known_documents, cluster, pc

(* define statement *)
StatesAreConsistent == Search(cluster, "idx_r") = known_documents

VARIABLE doc

vars == << known_documents, cluster, pc, doc >>

ProcSet == {"Zero Downtime Reindex + Write To New"} \cup {"PUT /idx_w/_create/{id}"}

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
        /\ pc = [self \in ProcSet |-> CASE self = "Zero Downtime Reindex + Write To New" -> "CreateTargetIndex"
                                        [] self = "PUT /idx_w/_create/{id}" -> "CreateRequest"]

CreateTargetIndex == /\ pc["Zero Downtime Reindex + Write To New"] = "CreateTargetIndex"
                     /\ cluster' = CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ])
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write To New"] = "WritesToNewIndex"]
                     /\ UNCHANGED << known_documents, doc >>

WritesToNewIndex == /\ pc["Zero Downtime Reindex + Write To New"] = "WritesToNewIndex"
                    /\ cluster' =            UpdateAlias(cluster, {
                                      [ alias |-> "idx_r", index |-> "idx_v1" ],
                                      [ alias |-> "idx_w", index |-> "idx_v2" ]
                                  })
                    /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write To New"] = "CopyDocuments"]
                    /\ UNCHANGED << known_documents, doc >>

CopyDocuments == /\ pc["Zero Downtime Reindex + Write To New"] = "CopyDocuments"
                 /\ cluster' = Reindex(cluster, "idx_v1", "idx_v2")
                 /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write To New"] = "ReadsToNewIndex"]
                 /\ UNCHANGED << known_documents, doc >>

ReadsToNewIndex == /\ pc["Zero Downtime Reindex + Write To New"] = "ReadsToNewIndex"
                   /\ cluster' =            UpdateAlias(cluster, {
                                     [ alias |-> "idx_r", index |-> "idx_v2" ],
                                     [ alias |-> "idx_w", index |-> "idx_v2" ]
                                 })
                   /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write To New"] = "DeleteSourceIndex"]
                   /\ UNCHANGED << known_documents, doc >>

DeleteSourceIndex == /\ pc["Zero Downtime Reindex + Write To New"] = "DeleteSourceIndex"
                     /\ cluster' = DeleteIndex(cluster, "idx_v1")
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write To New"] = "Done"]
                     /\ UNCHANGED << known_documents, doc >>

ZDR == CreateTargetIndex \/ WritesToNewIndex \/ CopyDocuments
          \/ ReadsToNewIndex \/ DeleteSourceIndex

CreateRequest == /\ pc["PUT /idx_w/_create/{id}"] = "CreateRequest"
                 /\ known_documents' = (known_documents \union { doc })
                 /\ cluster' = CreateDocument(cluster, "idx_w", doc)
                 /\ pc' = [pc EXCEPT !["PUT /idx_w/_create/{id}"] = "AssertCreated"]
                 /\ doc' = doc

AssertCreated == /\ pc["PUT /idx_w/_create/{id}"] = "AssertCreated"
                 /\ Assert(StatesAreConsistent, 
                           "Failure of assertion at line 47, column 9.")
                 /\ pc' = [pc EXCEPT !["PUT /idx_w/_create/{id}"] = "Done"]
                 /\ UNCHANGED << known_documents, cluster, doc >>

create == CreateRequest \/ AssertCreated

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ZDR \/ create
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
