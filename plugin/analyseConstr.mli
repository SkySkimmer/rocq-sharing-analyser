
open RocqSharingAnalyser.SharingAnalyser

val constr_descr : type_descr

val analyse_constr : Constr.t -> analysis

val analyse_econstr : EConstr.t -> analysis

val annotate_constr : analysis -> Constr.t -> analysis * Constr.t Int.Map.t * Constr.t
