
open RocqSharingAnalyser.SharingAnalyser

val pr_rec_analysis : analysis -> Pp.t

val do_constr_analysis : pstate:Declare.Proof.t option -> Constrexpr.constr_expr -> unit

val do_ltac2_constr_analysis : pstate:Declare.Proof.t option -> Ltac2_plugin.Tac2expr.raw_tacexpr -> unit

val do_proof_analysis : pstate:Declare.Proof.t -> unit

val do_def_body_analysis : opaque_access:Global.indirect_accessor -> Libnames.qualid -> unit
