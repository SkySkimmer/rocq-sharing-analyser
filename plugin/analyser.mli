
open RocqSharingAnalyser.SharingAnalyser

type output_mode

val output_mode_attr : output_mode Attributes.attribute

val pr_rec_analysis : analysis -> Pp.t

val do_constr_analysis : pstate:Declare.Proof.t option -> output_mode -> Constrexpr.constr_expr -> unit

val do_proof_analysis : pstate:Declare.Proof.t -> output_mode -> unit

val do_def_body_analysis : opaque_access:Global.indirect_accessor -> output_mode -> Libnames.qualid -> unit
