
open RocqSharingAnalyser.SharingAnalyser

val constr_descr : type_descr

val analyse_constr : Constr.t -> analysis

val analyse_econstr : EConstr.t -> analysis

val iter_ltr : (Constr.t -> unit) -> Constr.t -> unit

val map_kind_ltr : ('a -> 'b) ->
  ('a, 'a, 'c, 'd, 'e) Constr.kind_of_term ->
  ('b, 'b, 'c, 'd, 'e) Constr.kind_of_term

type 'a kind_gen = ('a,'a,Sorts.t,UVars.Instance.t,Sorts.relevance) Constr.kind_of_term

type annotated = {
  self : Constr.t;
  kind : annotated kind_gen;
  uid : int;
}

type 'a annotation_result = {
  (* for each subterm the actual constr, the annotated constr and the refcount *)
  subterms : (Constr.t * 'a * int) Int.Map.t;
  (* uids in bottomup order *)
  order : int list;
  root : 'a;
}

val annotate_constr : analysis -> Constr.t ->
  analysis * annotated annotation_result

val debug_annotate_constr : verbose:bool -> analysis -> Constr.t ->
  analysis * Constr.t annotation_result

val tree_size : Constr.t -> int

val graph_size : analysis -> Constr.t -> int
