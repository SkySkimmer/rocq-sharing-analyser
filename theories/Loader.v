From Ltac2 Require Import Init.

Declare ML Module "rocq-sharing-analyser.plugin".

Ltac2 @external hcons : constr -> constr := "rocq-sharing-analyser.plugin" "hcons".
