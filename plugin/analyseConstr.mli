
open RocqSharingAnalyser.SharingAnalyser

val constr_descr : type_descr

val analyse_constr : Constr.t -> analysis

val analyse_econstr : EConstr.t -> analysis

val iter_ltr : (Constr.t -> unit) -> Constr.t -> unit

(** The Int.Map contains for each subterm the actual constr, the annotated constr and the refcount *)
val annotate_constr : verbose:bool -> analysis -> Constr.t ->
  analysis * (Constr.t * Constr.t * int) Int.Map.t * Constr.t

val tree_size : Constr.t -> int

val graph_size : analysis -> Constr.t -> int
