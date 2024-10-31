
open RocqSharingAnalyser.SharingAnalyser

val constr_descr : type_descr

val pr_rec_analysis : analysis -> Pp.t

val do_constr_analysis : pstate:Declare.Proof.t option -> Constrexpr.constr_expr -> unit

val do_ltac2_constr_analysis : pstate:Declare.Proof.t option -> Ltac2_plugin.Tac2expr.raw_tacexpr -> unit
