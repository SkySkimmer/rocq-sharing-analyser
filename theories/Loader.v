From Ltac2 Require Import Init.

Declare ML Module "rocq-sharing-analyser.plugin".

Ltac2 @external hcons : constr -> constr := "rocq-sharing-analyser.plugin" "hcons".

Ltac2 Type output_mode := [ Full | Stats | Ltac2 | Annotate (bool) ].

Ltac2 @external analyse : output_mode -> constr -> unit :=
  "rocq-sharing-analyser.plugin" "analyse".
