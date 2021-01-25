---- MODULE rtr ----
EXTENDS Naturals, TLC

(* --algorithm RTR

variables
    documents = {[id |-> 1], [id |-> 2], [id |-> 3]},
    source_index_name = "source", source_index = documents,
    target_index_name = "target", target_index = {},
    write_alias = source_index_name, read_alias = source_index_name,
    indexes = { source_index_name };


process RTR = "Relocation Transparent Reindex"
begin
    CreateTarget:
        assert target_index_name \notin indexes;
        indexes := indexes \union { target_index_name };
    Reindex:
        assert source_index_name \in indexes;
        assert target_index_name \in indexes;
        target_index := source_index;
    UpdateAliases:
        write_alias := target_index_name;
        read_alias := target_index_name;
    DeleteSource:
        indexes := indexes \ { source_index_name };
    Check:
        assert target_index_name \in indexes;
        assert source_index_name \notin indexes;
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

process update = "GET /_search"
begin
    UpdateRequest:
        skip;
end process

process read = "GET /_doc/{id}"
begin
    GetByIdRequest:
        skip;
end process

process delete = "GET /_search"
begin
    DeleteRequest:
        skip;
end process

process search = "GET /_search"
begin
    SearchRequest:
        skip;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "4a3bbf50" /\ chksum(tla) = "caafcf3d")
VARIABLES documents, source_index_name, source_index, target_index_name,
          target_index, write_alias, read_alias, indexes, pc, doc

vars == << documents, source_index_name, source_index, target_index_name,
           target_index, write_alias, read_alias, indexes, pc, doc >>

ProcSet == {"Relocation Transparent Reindex"} \cup {"PUT /_create_/{id}"} \cup {"GET /_search"} \cup {"GET /_doc/{id}"} \cup {"GET /_search"} \cup {"GET /_search"}

Init == (* Global variables *)
        /\ documents = {[id |-> 1], [id |-> 2], [id |-> 3]}
        /\ source_index_name = "source"
        /\ source_index = documents
        /\ target_index_name = "target"
        /\ target_index = {}
        /\ write_alias = source_index_name
        /\ read_alias = source_index_name
        /\ indexes = { source_index_name }
        (* Process create *)
        /\ doc = [id|->10]
        /\ pc = [self \in ProcSet |-> CASE self = "Relocation Transparent Reindex" -> "CreateTarget"
                                        [] self = "PUT /_create_/{id}" -> "CreateRequest"
                                        [] self = "GET /_search" -> "UpdateRequest"
                                        [] self = "GET /_doc/{id}" -> "GetByIdRequest"
                                        [] self = "GET /_search" -> "DeleteRequest"
                                        [] self = "GET /_search" -> "SearchRequest"]

CreateTarget == /\ pc["Relocation Transparent Reindex"] = "CreateTarget"
                /\ Assert(target_index_name \notin indexes,
                          "Failure of assertion at line 17, column 9.")
                /\ indexes' = (indexes \union { target_index_name })
                /\ pc' = [pc EXCEPT !["Relocation Transparent Reindex"] = "Reindex"]
                /\ UNCHANGED << documents, source_index_name, source_index,
                                target_index_name, target_index, write_alias,
                                read_alias, doc >>

Reindex == /\ pc["Relocation Transparent Reindex"] = "Reindex"
           /\ Assert(source_index_name \in indexes,
                     "Failure of assertion at line 20, column 9.")
           /\ Assert(target_index_name \in indexes,
                     "Failure of assertion at line 21, column 9.")
           /\ target_index' = source_index
           /\ pc' = [pc EXCEPT !["Relocation Transparent Reindex"] = "UpdateAliases"]
           /\ UNCHANGED << documents, source_index_name, source_index,
                           target_index_name, write_alias, read_alias, indexes,
                           doc >>

UpdateAliases == /\ pc["Relocation Transparent Reindex"] = "UpdateAliases"
                 /\ write_alias' = target_index_name
                 /\ read_alias' = target_index_name
                 /\ pc' = [pc EXCEPT !["Relocation Transparent Reindex"] = "DeleteSource"]
                 /\ UNCHANGED << documents, source_index_name, source_index,
                                 target_index_name, target_index, indexes, doc >>

DeleteSource == /\ pc["Relocation Transparent Reindex"] = "DeleteSource"
                /\ indexes' = indexes \ { source_index_name }
                /\ pc' = [pc EXCEPT !["Relocation Transparent Reindex"] = "Check"]
                /\ UNCHANGED << documents, source_index_name, source_index,
                                target_index_name, target_index, write_alias,
                                read_alias, doc >>

Check == /\ pc["Relocation Transparent Reindex"] = "Check"
         /\ Assert(target_index_name \in indexes,
                   "Failure of assertion at line 29, column 9.")
         /\ Assert(source_index_name \notin indexes,
                   "Failure of assertion at line 30, column 9.")
         /\ Assert(read_alias = target_index_name,
                   "Failure of assertion at line 31, column 9.")
         /\ Assert(write_alias = target_index_name,
                   "Failure of assertion at line 32, column 9.")
         /\ Assert(target_index = documents,
                   "Failure of assertion at line 33, column 9.")
         /\ pc' = [pc EXCEPT !["Relocation Transparent Reindex"] = "Done"]
         /\ UNCHANGED << documents, source_index_name, source_index,
                         target_index_name, target_index, write_alias,
                         read_alias, indexes, doc >>

RTR == CreateTarget \/ Reindex \/ UpdateAliases \/ DeleteSource \/ Check

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
                 /\ UNCHANGED << source_index_name, target_index_name,
                                 write_alias, read_alias, indexes, doc >>

create == CreateRequest

UpdateRequest == /\ pc["GET /_search"] = "UpdateRequest"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["GET /_search"] = "Done"]
                 /\ UNCHANGED << documents, source_index_name, source_index,
                                 target_index_name, target_index, write_alias,
                                 read_alias, indexes, doc >>

update == UpdateRequest

GetByIdRequest == /\ pc["GET /_doc/{id}"] = "GetByIdRequest"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT !["GET /_doc/{id}"] = "Done"]
                  /\ UNCHANGED << documents, source_index_name, source_index,
                                  target_index_name, target_index, write_alias,
                                  read_alias, indexes, doc >>

read == GetByIdRequest

DeleteRequest == /\ pc["GET /_search"] = "DeleteRequest"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["GET /_search"] = "Done"]
                 /\ UNCHANGED << documents, source_index_name, source_index,
                                 target_index_name, target_index, write_alias,
                                 read_alias, indexes, doc >>

delete == DeleteRequest

SearchRequest == /\ pc["GET /_search"] = "SearchRequest"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["GET /_search"] = "Done"]
                 /\ UNCHANGED << documents, source_index_name, source_index,
                                 target_index_name, target_index, write_alias,
                                 read_alias, indexes, doc >>

search == SearchRequest

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == RTR \/ create \/ update \/ read \/ delete \/ search
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
