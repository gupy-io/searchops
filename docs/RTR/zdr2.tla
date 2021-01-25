---- MODULE zdr2 ----
EXTENDS TLC, Elasticsearch

(* --algorithm ZDR

variables
    known_documents = {[ id |-> 1, version |-> 1 ]},
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

process create = "POST /idx_{v}/_create/{id}"
variable doc = [ id |-> 10, version |-> 1 ]
begin
    WriteIndexV1:
        if ExistsIndex(cluster, "idx_v1") then
            cluster := CreateDocument(cluster, "idx_v1", doc);
        end if;
    WriteIndexV2:
        if ExistsIndex(cluster, "idx_v2") then
            cluster := CreateDocument(cluster, "idx_v2", doc);
        end if;
    Check:
        known_documents := known_documents \union { doc };
        assert StatesAreConsistent;
end process

\*process update = "PUT /idx_"
\*variable doc = [ id |-> 1, version |-> 2 ]
\*begin
\*    UpdateRequest:
\*        known_documents := (known_documents \ {[ id |-> 1, version |-> 1 ]}) \union { doc };
\*        if ExistsIndex(cluster, "idx_v1")
\*            /\ ExistsDocument(cluster, "idx_v1", doc.id)
\*            /\ ExistsIndex(cluster, "idx_v2")
\*            /\ ExistsDocument(cluster, "idx_v2", doc.id)
\*        then
\*            cluster := UpdateDocument(UpdateDocument(cluster, "idx_v1", doc), "idx_v2", doc);
\*        elsif ExistsIndex(cluster, "idx_v1") then
\*            cluster := UpdateDocument(cluster, "idx_v1", doc);
\*        elsif ExistsIndex(cluster, "idx_v2") then
\*            cluster := UpdateDocument(cluster, "idx_v2", doc);
\*        end if;
\*end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "937e2fd8" /\ chksum(tla) = "8eb07c77")
\* Label Check of process ZDR at line 35 col 9 changed to Check_
VARIABLES known_documents, cluster, pc

(* define statement *)
ReadableDocuments == Search(cluster, "idx_r")
StatesAreConsistent == ReadableDocuments = known_documents

VARIABLE doc

vars == << known_documents, cluster, pc, doc >>

ProcSet == {"Zero Downtime Reindex"} \cup {"POST /idx_{v}/_create/{id}"}

Init == (* Global variables *)
        /\ known_documents = {[ id |-> 1, version |-> 1 ]}
        /\ cluster =           NewCluster([
                         aliases |-> {
                             [ alias |-> "idx_r", index |-> "idx_v1" ],
                             [ alias |-> "idx_w", index |-> "idx_v1" ]
                         },
                         indices |-> {[ name |-> "idx_v1", docs |-> known_documents ]}
                     ])
        (* Process create *)
        /\ doc = [ id |-> 10, version |-> 1 ]
        /\ pc = [self \in ProcSet |-> CASE self = "Zero Downtime Reindex" -> "CreateTargetIndex"
                                        [] self = "POST /idx_{v}/_create/{id}" -> "WriteIndexV1"]

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
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Check_"]
                     /\ UNCHANGED << known_documents, doc >>

Check_ == /\ pc["Zero Downtime Reindex"] = "Check_"
          /\ Assert(~ExistsIndex(cluster, "idx_v1"), 
                    "Failure of assertion at line 35, column 9.")
          /\ Assert(ExistsIndex(cluster, "idx_v2"), 
                    "Failure of assertion at line 36, column 9.")
          /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_r", index |-> "idx_v2" ]), 
                    "Failure of assertion at line 37, column 9.")
          /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_w", index |-> "idx_v2" ]), 
                    "Failure of assertion at line 38, column 9.")
          /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Done"]
          /\ UNCHANGED << known_documents, cluster, doc >>

ZDR == CreateTargetIndex \/ CopyDocuments \/ AtomicAliasSwap
          \/ DeleteSourceIndex \/ Check_

WriteIndexV1 == /\ pc["POST /idx_{v}/_create/{id}"] = "WriteIndexV1"
                /\ IF ExistsIndex(cluster, "idx_v1")
                      THEN /\ cluster' = CreateDocument(cluster, "idx_v1", doc)
                      ELSE /\ TRUE
                           /\ UNCHANGED cluster
                /\ pc' = [pc EXCEPT !["POST /idx_{v}/_create/{id}"] = "WriteIndexV2"]
                /\ UNCHANGED << known_documents, doc >>

WriteIndexV2 == /\ pc["POST /idx_{v}/_create/{id}"] = "WriteIndexV2"
                /\ IF ExistsIndex(cluster, "idx_v2")
                      THEN /\ cluster' = CreateDocument(cluster, "idx_v2", doc)
                      ELSE /\ TRUE
                           /\ UNCHANGED cluster
                /\ pc' = [pc EXCEPT !["POST /idx_{v}/_create/{id}"] = "Check"]
                /\ UNCHANGED << known_documents, doc >>

Check == /\ pc["POST /idx_{v}/_create/{id}"] = "Check"
         /\ known_documents' = (known_documents \union { doc })
         /\ Assert(StatesAreConsistent, 
                   "Failure of assertion at line 54, column 9.")
         /\ pc' = [pc EXCEPT !["POST /idx_{v}/_create/{id}"] = "Done"]
         /\ UNCHANGED << cluster, doc >>

create == WriteIndexV1 \/ WriteIndexV2 \/ Check

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ZDR \/ create
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
