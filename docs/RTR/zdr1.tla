---- MODULE zdr1 ----
EXTENDS TLC, Elasticsearch

(* --algorithm ZDR

process ZDR = "Zero Downtime Reindex"
begin
    CreateTarget:
        assert target_index_name \notin existing_indices;
        existing_indices := existing_indices \union { target_index_name };
    Reindex:
        assert source_index_name \in existing_indices;
        assert target_index_name \in existing_indices;
        target_index_docs := source_index_docs;
    UpdateAliases:
        write_alias := target_index_name;
        read_alias := target_index_name;
    DeleteSource:
        existing_indices := existing_indices \ { source_index_name };
    Check:
        assert target_index_name \in existing_indices;
        assert source_index_name \notin existing_indices;
        assert read_alias = target_index_name;
        assert write_alias = target_index_name;
        assert target_index_docs = documents;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "7b16f75f" /\ chksum(tla) = "e268b457")
VARIABLES documents, source_index_name, source_index_docs, target_index_name, 
          target_index_docs, write_alias, read_alias, existing_indices, pc

(* define statement *)
ReadAvailableDocs ==
    CASE read_alias = source_index_name -> source_index_docs
     []  read_alias = target_index_name -> target_index_docs
DocumentsAreConsistent == ReadAvailableDocs = documents


vars == << documents, source_index_name, source_index_docs, target_index_name, 
           target_index_docs, write_alias, read_alias, existing_indices, pc
        >>

ProcSet == {"Zero Downtime Reindex"}

Init == (* Global variables *)
        /\ documents = {[id |-> 1], [id |-> 2], [id |-> 3]}
        /\ source_index_name = "source"
        /\ source_index_docs = documents
        /\ target_index_name = "target"
        /\ target_index_docs = {}
        /\ write_alias = source_index_name
        /\ read_alias = source_index_name
        /\ existing_indices = { source_index_name }
        /\ pc = [self \in ProcSet |-> "CreateTarget"]

CreateTarget == /\ pc["Zero Downtime Reindex"] = "CreateTarget"
                /\ Assert(target_index_name \notin existing_indices, 
                          "Failure of assertion at line 32, column 9.")
                /\ existing_indices' = (existing_indices \union { target_index_name })
                /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Reindex"]
                /\ UNCHANGED << documents, source_index_name, 
                                source_index_docs, target_index_name, 
                                target_index_docs, write_alias, read_alias >>

Reindex == /\ pc["Zero Downtime Reindex"] = "Reindex"
           /\ Assert(source_index_name \in existing_indices, 
                     "Failure of assertion at line 35, column 9.")
           /\ Assert(target_index_name \in existing_indices, 
                     "Failure of assertion at line 36, column 9.")
           /\ target_index_docs' = source_index_docs
           /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "UpdateAliases"]
           /\ UNCHANGED << documents, source_index_name, source_index_docs, 
                           target_index_name, write_alias, read_alias, 
                           existing_indices >>

UpdateAliases == /\ pc["Zero Downtime Reindex"] = "UpdateAliases"
                 /\ write_alias' = target_index_name
                 /\ read_alias' = target_index_name
                 /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "DeleteSource"]
                 /\ UNCHANGED << documents, source_index_name, 
                                 source_index_docs, target_index_name, 
                                 target_index_docs, existing_indices >>

DeleteSource == /\ pc["Zero Downtime Reindex"] = "DeleteSource"
                /\ existing_indices' = existing_indices \ { source_index_name }
                /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Check"]
                /\ UNCHANGED << documents, source_index_name, 
                                source_index_docs, target_index_name, 
                                target_index_docs, write_alias, read_alias >>

Check == /\ pc["Zero Downtime Reindex"] = "Check"
         /\ Assert(target_index_name \in existing_indices, 
                   "Failure of assertion at line 44, column 9.")
         /\ Assert(source_index_name \notin existing_indices, 
                   "Failure of assertion at line 45, column 9.")
         /\ Assert(read_alias = target_index_name, 
                   "Failure of assertion at line 46, column 9.")
         /\ Assert(write_alias = target_index_name, 
                   "Failure of assertion at line 47, column 9.")
         /\ Assert(target_index_docs = documents, 
                   "Failure of assertion at line 48, column 9.")
         /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Done"]
         /\ UNCHANGED << documents, source_index_name, source_index_docs, 
                         target_index_name, target_index_docs, write_alias, 
                         read_alias, existing_indices >>

ZDR == CreateTarget \/ Reindex \/ UpdateAliases \/ DeleteSource \/ Check

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ZDR
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
