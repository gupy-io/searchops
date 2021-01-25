---- MODULE zdr ----
EXTENDS TLC

(* --algorithm ZDR

variables
    documents = {[id |-> 1], [id |-> 2], [id |-> 3]},
    source_index_name = "source", source_index = documents,
    write_alias = source_index_name, read_alias = source_index_name,
    existing_indices = { source_index_name },
    target_index_name = "target", target_index = {};


process ZDR = "Zero Downtime Reindex"
begin
    CreateTarget:
        assert target_index_name \notin existing_indices;
        existing_indices := existing_indices \union { target_index_name };
    Reindex:
        assert source_index_name \in existing_indices;
        assert target_index_name \in existing_indices;
        target_index := source_index;
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
        assert target_index = documents;
end process

process create = "PUT /_create_/{id}"
variable doc = [id|->10]
begin
    CreateRequest:
        documents := documents \union {doc};
        if write_alias = source_index_name then
            source_index := source_index \union {doc};
        elsif write_alias = target_index_name then
            target_index := target_index \union {doc};
        end if;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "c0595f72" /\ chksum(tla) = "a988defd")
VARIABLES documents, source_index_name, source_index, write_alias, read_alias, 
          existing_indices, target_index_name, target_index, pc, doc

vars == << documents, source_index_name, source_index, write_alias, 
           read_alias, existing_indices, target_index_name, target_index, pc, 
           doc >>

ProcSet == {"Zero Downtime Reindex"} \cup {"PUT /_create_/{id}"}

Init == (* Global variables *)
        /\ documents = {[id |-> 1], [id |-> 2], [id |-> 3]}
        /\ source_index_name = "source"
        /\ source_index = documents
        /\ write_alias = source_index_name
        /\ read_alias = source_index_name
        /\ existing_indices = { source_index_name }
        /\ target_index_name = "target"
        /\ target_index = {}
        (* Process create *)
        /\ doc = [id|->10]
        /\ pc = [self \in ProcSet |-> CASE self = "Zero Downtime Reindex" -> "CreateTarget"
                                        [] self = "PUT /_create_/{id}" -> "CreateRequest"]

CreateTarget == /\ pc["Zero Downtime Reindex"] = "CreateTarget"
                /\ Assert(target_index_name \notin existing_indices, 
                          "Failure of assertion at line 17, column 9.")
                /\ existing_indices' = (existing_indices \union { target_index_name })
                /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Reindex"]
                /\ UNCHANGED << documents, source_index_name, source_index, 
                                write_alias, read_alias, target_index_name, 
                                target_index, doc >>

Reindex == /\ pc["Zero Downtime Reindex"] = "Reindex"
           /\ Assert(source_index_name \in existing_indices, 
                     "Failure of assertion at line 20, column 9.")
           /\ Assert(target_index_name \in existing_indices, 
                     "Failure of assertion at line 21, column 9.")
           /\ target_index' = source_index
           /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "UpdateAliases"]
           /\ UNCHANGED << documents, source_index_name, source_index, 
                           write_alias, read_alias, existing_indices, 
                           target_index_name, doc >>

UpdateAliases == /\ pc["Zero Downtime Reindex"] = "UpdateAliases"
                 /\ write_alias' = target_index_name
                 /\ read_alias' = target_index_name
                 /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "DeleteSource"]
                 /\ UNCHANGED << documents, source_index_name, source_index, 
                                 existing_indices, target_index_name, 
                                 target_index, doc >>

DeleteSource == /\ pc["Zero Downtime Reindex"] = "DeleteSource"
                /\ existing_indices' = existing_indices \ { source_index_name }
                /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Check"]
                /\ UNCHANGED << documents, source_index_name, source_index, 
                                write_alias, read_alias, target_index_name, 
                                target_index, doc >>

Check == /\ pc["Zero Downtime Reindex"] = "Check"
         /\ Assert(target_index_name \in existing_indices, 
                   "Failure of assertion at line 29, column 9.")
         /\ Assert(source_index_name \notin existing_indices, 
                   "Failure of assertion at line 30, column 9.")
         /\ Assert(read_alias = target_index_name, 
                   "Failure of assertion at line 31, column 9.")
         /\ Assert(write_alias = target_index_name, 
                   "Failure of assertion at line 32, column 9.")
         /\ Assert(target_index = documents, 
                   "Failure of assertion at line 33, column 9.")
         /\ pc' = [pc EXCEPT !["Zero Downtime Reindex"] = "Done"]
         /\ UNCHANGED << documents, source_index_name, source_index, 
                         write_alias, read_alias, existing_indices, 
                         target_index_name, target_index, doc >>

ZDR == CreateTarget \/ Reindex \/ UpdateAliases \/ DeleteSource \/ Check

CreateRequest == /\ pc["PUT /_create_/{id}"] = "CreateRequest"
                 /\ documents' = (documents \union {doc})
                 /\ IF write_alias = source_index_name
                       THEN /\ source_index' = (source_index \union {doc})
                            /\ UNCHANGED target_index
                       ELSE /\ IF write_alias = target_index_name
                                  THEN /\ target_index' = (target_index \union {doc})
                                  ELSE /\ TRUE
                                       /\ UNCHANGED target_index
                            /\ UNCHANGED source_index
                 /\ pc' = [pc EXCEPT !["PUT /_create_/{id}"] = "Done"]
                 /\ UNCHANGED << source_index_name, write_alias, read_alias, 
                                 existing_indices, target_index_name, doc >>

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
