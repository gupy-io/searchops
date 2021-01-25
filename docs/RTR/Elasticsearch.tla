---- MODULE Elasticsearch ----

(* --algorithm Elasticsearch

variables
    documents = {[id |-> 1], [id |-> 2], [id |-> 3]},
    source_index_name = "source",
    source_index_docs = documents,
    target_index_name = "target",
    target_index_docs = {},
    write_alias = source_index_name,
    read_alias = source_index_name,
    existing_indices = { source_index_name };
begin
end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "16abd820" /\ chksum(tla) = "f1adbdb8")
VARIABLES documents, source_index_name, source_index_docs, target_index_name, 
          target_index_docs, write_alias, read_alias, existing_indices

vars == << documents, source_index_name, source_index_docs, target_index_name, 
           target_index_docs, write_alias, read_alias, existing_indices >>

Init == (* Global variables *)
        /\ documents = {[id |-> 1], [id |-> 2], [id |-> 3]}
        /\ source_index_name = "source"
        /\ source_index_docs = documents
        /\ target_index_name = "target"
        /\ target_index_docs = {}
        /\ write_alias = source_index_name
        /\ read_alias = source_index_name
        /\ existing_indices = { source_index_name }

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

====
