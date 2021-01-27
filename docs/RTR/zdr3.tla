---- MODULE zdr3 ----
EXTENDS TLC, Elasticsearch

(* --algorithm ZDR

variables
    known_documents = {[ id |-> 1, version |-> 1]},
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

process ZDR = "Zero Downtime Reindex + Write to New + Read From Both"
begin
    CreateTargetIndex:
        cluster := CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ]);
    ReadFromBothWriteToNew:
        cluster := UpdateAlias(cluster, {
            [ alias |-> "idx_r", index |-> "idx_v1" ],
            [ alias |-> "idx_r", index |-> "idx_v2" ],
            [ alias |-> "idx_w", index |-> "idx_v2" ]
        });
    CopyDocuments:
        cluster := Reindex(cluster, "idx_v1", "idx_v2");
    DeleteSourceIndex:
        cluster := DeleteIndex(cluster, "idx_v1");
end process

process create = "PUT /idx_w/_create/{id}"
variable doc10 = [ id |-> 10, version |-> 1 ]
begin
    CreateRequest:
        known_documents := known_documents \union { doc10 };
        cluster := CreateDocument(cluster, "idx_w", doc10);
    AssertCreated:
        assert StatesAreConsistent;
end process

process update = "POST /idx_w/_update/{id}"
variables
    doc1_v1 = [ id |-> 1, version |-> 1 ],
    doc1_v2 = [ id |-> 1, version |-> 2 ]
begin
    UpdateRequest:
        known_documents := (known_documents \ { doc1_v1 }) \union { doc1_v2 };
        cluster := UpdateDocument(cluster, "idx_w", doc1_v2);
    AssertUpdated:
        assert StatesAreConsistent;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "f6d61366" /\ chksum(tla) = "aac19a56")
VARIABLES known_documents, cluster, pc

(* define statement *)
StatesAreConsistent == Search(cluster, "idx_r") = known_documents

VARIABLES doc10, doc1_v1, doc1_v2

vars == << known_documents, cluster, pc, doc10, doc1_v1, doc1_v2 >>

ProcSet == {"Zero Downtime Reindex + Write to New + Read From Both"} \cup {"PUT /idx_w/_create/{id}"} \cup {"POST /idx_w/_update/{id}"}

Init == (* Global variables *)
        /\ known_documents = {[ id |-> 1, version |-> 1]}
        /\ cluster =           NewCluster([
                         aliases |-> {
                             [ alias |-> "idx_r", index |-> "idx_v1" ],
                             [ alias |-> "idx_w", index |-> "idx_v1" ]
                         },
                         indices |-> {[ name |-> "idx_v1", docs |-> known_documents ]}
                     ])
        (* Process create *)
        /\ doc10 = [ id |-> 10, version |-> 1 ]
        (* Process update *)
        /\ doc1_v1 = [ id |-> 1, version |-> 1 ]
        /\ doc1_v2 = [ id |-> 1, version |-> 2 ]
        /\ pc = [self \in ProcSet |-> CASE self = "Zero Downtime Reindex + Write to New + Read From Both" -> "CreateTargetIndex"
                                        [] self = "PUT /idx_w/_create/{id}" -> "CreateRequest"
                                        [] self = "POST /idx_w/_update/{id}" -> "UpdateRequest"]

CreateTargetIndex == /\ pc["Zero Downtime Reindex + Write to New + Read From Both"] = "CreateTargetIndex"
                     /\ cluster' = CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ])
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write to New + Read From Both"] = "ReadFromBothWriteToNew"]
                     /\ UNCHANGED << known_documents, doc10, doc1_v1, doc1_v2 >>

ReadFromBothWriteToNew == /\ pc["Zero Downtime Reindex + Write to New + Read From Both"] = "ReadFromBothWriteToNew"
                          /\ cluster' =            UpdateAlias(cluster, {
                                            [ alias |-> "idx_r", index |-> "idx_v1" ],
                                            [ alias |-> "idx_r", index |-> "idx_v2" ],
                                            [ alias |-> "idx_w", index |-> "idx_v2" ]
                                        })
                          /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write to New + Read From Both"] = "CopyDocuments"]
                          /\ UNCHANGED << known_documents, doc10, doc1_v1, 
                                          doc1_v2 >>

CopyDocuments == /\ pc["Zero Downtime Reindex + Write to New + Read From Both"] = "CopyDocuments"
                 /\ cluster' = Reindex(cluster, "idx_v1", "idx_v2")
                 /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write to New + Read From Both"] = "DeleteSourceIndex"]
                 /\ UNCHANGED << known_documents, doc10, doc1_v1, doc1_v2 >>

DeleteSourceIndex == /\ pc["Zero Downtime Reindex + Write to New + Read From Both"] = "DeleteSourceIndex"
                     /\ cluster' = DeleteIndex(cluster, "idx_v1")
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex + Write to New + Read From Both"] = "Done"]
                     /\ UNCHANGED << known_documents, doc10, doc1_v1, doc1_v2 >>

ZDR == CreateTargetIndex \/ ReadFromBothWriteToNew \/ CopyDocuments
          \/ DeleteSourceIndex

CreateRequest == /\ pc["PUT /idx_w/_create/{id}"] = "CreateRequest"
                 /\ known_documents' = (known_documents \union { doc10 })
                 /\ cluster' = CreateDocument(cluster, "idx_w", doc10)
                 /\ pc' = [pc EXCEPT !["PUT /idx_w/_create/{id}"] = "AssertCreated"]
                 /\ UNCHANGED << doc10, doc1_v1, doc1_v2 >>

AssertCreated == /\ pc["PUT /idx_w/_create/{id}"] = "AssertCreated"
                 /\ Assert(StatesAreConsistent, 
                           "Failure of assertion at line 43, column 9.")
                 /\ pc' = [pc EXCEPT !["PUT /idx_w/_create/{id}"] = "Done"]
                 /\ UNCHANGED << known_documents, cluster, doc10, doc1_v1, 
                                 doc1_v2 >>

create == CreateRequest \/ AssertCreated

UpdateRequest == /\ pc["POST /idx_w/_update/{id}"] = "UpdateRequest"
                 /\ known_documents' = ((known_documents \ { doc1_v1 }) \union { doc1_v2 })
                 /\ cluster' = UpdateDocument(cluster, "idx_w", doc1_v2)
                 /\ pc' = [pc EXCEPT !["POST /idx_w/_update/{id}"] = "AssertUpdated"]
                 /\ UNCHANGED << doc10, doc1_v1, doc1_v2 >>

AssertUpdated == /\ pc["POST /idx_w/_update/{id}"] = "AssertUpdated"
                 /\ Assert(StatesAreConsistent, 
                           "Failure of assertion at line 55, column 9.")
                 /\ pc' = [pc EXCEPT !["POST /idx_w/_update/{id}"] = "Done"]
                 /\ UNCHANGED << known_documents, cluster, doc10, doc1_v1, 
                                 doc1_v2 >>

update == UpdateRequest \/ AssertUpdated

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ZDR \/ create \/ update
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
