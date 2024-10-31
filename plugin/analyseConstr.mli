
open RocqSharingAnalyser.SharingAnalyser

val constr_descr : type_descr

val analyse_constr : Constr.t -> analysis

val analyse_econstr : EConstr.t -> analysis

val iter_ltr : (Constr.t -> unit) -> Constr.t -> unit

val map_ltr : (Constr.t -> Constr.t) -> Constr.t -> Constr.t

val annotate_constr : verbose:bool -> analysis -> Constr.t -> analysis * (Constr.t * Constr.t) Int.Map.t * Constr.t

val tree_size : Constr.t -> int

val graph_size : analysis -> Constr.t -> int
