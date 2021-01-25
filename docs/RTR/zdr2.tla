---- MODULE zdr2 ----
EXTENDS TLC, Elasticsearch

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
variable doc = [ id |-> 10 ]
begin
    CreateRequest:
        known_documents := known_documents \union { doc };
        if ExistsIndex(cluster, "idx_v1") /\ ExistsIndex(cluster, "idx_v2") then
            cluster := CreateDocument(CreateDocument(cluster, "idx_v1", doc), "idx_v2", doc);
        elsif ExistsIndex(cluster, "idx_v1") then
            cluster := CreateDocument(cluster, "idx_v1", doc);
        elsif ExistsIndex(cluster, "idx_v2") then
            cluster := CreateDocument(cluster, "idx_v2", doc);
        end if;
end process

process update = "PUT /idx_"
variable doc = [ id |-> 1 ]
begin
    UpdateRequest:
        known_documents := known_documents \union { doc };
        if ExistsIndex(cluster, "idx_v1") /\ ExistsIndex(cluster, "idx_v2") then
            cluster := CreateDocument(CreateDocument(cluster, "idx_v1", doc), "idx_v2", doc);
        elsif ExistsIndex(cluster, "idx_v1") then
            cluster := CreateDocument(cluster, "idx_v1", doc);
        elsif ExistsIndex(cluster, "idx_v2") then
            cluster := CreateDocument(cluster, "idx_v2", doc);
        end if;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "6c68e98f" /\ chksum(tla) = "624618eb")
\* Process variable doc of process create at line 42 col 10 changed to doc_
VARIABLES known_documents, cluster, pc

(* define statement *)
ReadableDocuments == Search(cluster, "idx_r")
StatesAreConsistent == ReadableDocuments = known_documents

VARIABLES doc_, doc

vars == << known_documents, cluster, pc, doc_, doc >>

ProcSet == {"Zero Downtime Reindex"} \cup {"POST /idx_{v}/_create/{id}"} \cup {"PUT /idx_"}

Init == (* Global variables *)
        /\ known_documents = {[ id |-> 1 ], [ id |-> 2 ], [ id |-> 3 ]}
        /\ cluster =           NewCluster([
                         aliases |-> {
                             [ alias |-> "idx_r", index |-> "idx_v1" ],
                             [ alias |-> "idx_w", index |-> "idx_v1" ]
                         },
                         indices |-> {[ name |-> "idx_v1", docs |-> known_documents ]}
                     ])
        (* Process create *)
        /\ doc_ = [ id |-> 10 ]
        (* Process update *)
        /\ doc = [ id |-> 1 ]
        /\ pc = [self \in ProcSet |-> CASE self = "Zero Downtime Reindex" -> "CreateTargetIndex"
                                        [] self = "POST /idx_{v}/_create/{id}" -> "CreateRequest"
                                        [] self = "PUT /idx_" -> "UpdateRequest"]

CreateTargetIndex == /\ pc["Zero Downtime Reindex"] = "CreateTargetIndex"
                     /\ cluster' = CreateIndex(cluster, [ name |-> "idx_v2", docs |-> {} ])
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "CopyDocuments"]
                     /\ UNCHANGED << known_documents, doc_, doc >>

CopyDocuments == /\ pc["Zero Downtime Reindex"] = "CopyDocuments"
                 /\ cluster' = Reindex(cluster, "idx_v1", "idx_v2")
                 /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "AtomicAliasSwap"]
                 /\ UNCHANGED << known_documents, doc_, doc >>

AtomicAliasSwap == /\ pc["Zero Downtime Reindex"] = "AtomicAliasSwap"
                   /\ cluster' =            UpdateAlias(cluster, {
                                     [ alias |-> "idx_r", index |-> "idx_v2" ],
                                     [ alias |-> "idx_w", index |-> "idx_v2" ]
                                 })
                   /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "DeleteSourceIndex"]
                   /\ UNCHANGED << known_documents, doc_, doc >>

DeleteSourceIndex == /\ pc["Zero Downtime Reindex"] = "DeleteSourceIndex"
                     /\ cluster' = DeleteIndex(cluster, "idx_v1")
                     /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Check"]
                     /\ UNCHANGED << known_documents, doc_, doc >>

Check == /\ pc["Zero Downtime Reindex"] = "Check"
         /\ Assert(~ExistsIndex(cluster, "idx_v1"), 
                   "Failure of assertion at line 35, column 9.")
         /\ Assert(ExistsIndex(cluster, "idx_v2"), 
                   "Failure of assertion at line 36, column 9.")
         /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_r", index |-> "idx_v2" ]), 
                   "Failure of assertion at line 37, column 9.")
         /\ Assert(ExistsAlias(cluster, [ alias |-> "idx_w", index |-> "idx_v2" ]), 
                   "Failure of assertion at line 38, column 9.")
         /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Done"]
         /\ UNCHANGED << known_documents, cluster, doc_, doc >>

ZDR == CreateTargetIndex \/ CopyDocuments \/ AtomicAliasSwap
          \/ DeleteSourceIndex \/ Check

CreateRequest == /\ pc["POST /idx_{v}/_create/{id}"] = "CreateRequest"
                 /\ known_documents' = (known_documents \union { doc_ })
                 /\ IF ExistsIndex(cluster, "idx_v1") /\ ExistsIndex(cluster, "idx_v2")
                       THEN /\ cluster' = CreateDocument(CreateDocument(cluster, "idx_v1", doc_), "idx_v2", doc_)
                       ELSE /\ IF ExistsIndex(cluster, "idx_v1")
                                  THEN /\ cluster' = CreateDocument(cluster, "idx_v1", doc_)
                                  ELSE /\ IF ExistsIndex(cluster, "idx_v2")
                                             THEN /\ cluster' = CreateDocument(cluster, "idx_v2", doc_)
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED cluster
                 /\ pc' = [pc EXCEPT !["POST /idx_{v}/_create/{id}"] = "Done"]
                 /\ UNCHANGED << doc_, doc >>

create == CreateRequest

UpdateRequest == /\ pc["PUT /idx_"] = "UpdateRequest"
                 /\ known_documents' = (known_documents \union { doc })
                 /\ IF ExistsIndex(cluster, "idx_v1") /\ ExistsIndex(cluster, "idx_v2")
                       THEN /\ cluster' = CreateDocument(CreateDocument(cluster, "idx_v1", doc), "idx_v2", doc)
                       ELSE /\ IF ExistsIndex(cluster, "idx_v1")
                                  THEN /\ cluster' = CreateDocument(cluster, "idx_v1", doc)
                                  ELSE /\ IF ExistsIndex(cluster, "idx_v2")
                                             THEN /\ cluster' = CreateDocument(cluster, "idx_v2", doc)
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED cluster
                 /\ pc' = [pc EXCEPT !["PUT /idx_"] = "Done"]
                 /\ UNCHANGED << doc_, doc >>

update == UpdateRequest

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ZDR \/ create \/ update
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
