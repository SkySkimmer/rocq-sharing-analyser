From Ltac2 Require Import Ltac2.
From SharingAnalyser Require Import Loader.

Sharing Analysis Term 0.

Sharing Analysis Ltac2 '(0,0).
Sharing Analysis Ltac2 let x := '0 in '($x,$x).

Goal nat * nat.
  exact (0,0).
  Sharing Analysis Proof.
Abort.

Definition foo := (0,0).

Sharing Analysis Definition Body foo.

Definition bar := (0,0,0,0,0,0).

Sharing Analysis Definition Body bar.

Inductive is_nat : nat -> Prop :=
| Is_nat_Z : is_nat 0
| Is_nat_S : forall n, is_nat n -> is_nat (S n).

Lemma is_nat_5 : is_nat 5.
Proof.
  repeat constructor.
  Sharing Analysis Proof.
  (* tree size = 36
     graph size = 26
     the 0 nodes are shared, some of the S nodes are shared
     (but incompletely: 4 nodes equal to [S] with refcounts 1, 2, 3 and 4) ) *)
Qed.

Sharing Analysis Definition Body is_nat_5.
(* tree size = 36
   graph size = 13 *)

Lemma is_nat_10 : is_nat 10.
Proof.
  repeat constructor.
  #[display(stats)] Sharing Analysis Proof.
  (* tree size = 121
     graph size = 76 *)
Qed.

#[display(stats)] Sharing Analysis Definition Body is_nat_10.
(* tree size = 121
   graph size = 23 *)

#[display(annotate)] Sharing Analysis Definition Body is_nat_10.
(* pretty unreadable *)

#[display(verbose_annotate)] Sharing Analysis Definition Body is_nat_10.
(* not too terrible I guess *)

Lemma is_nat_500 : is_nat 500.
Proof.
  repeat constructor.
  #[display(stats)] Sharing Analysis Proof.
  (* tree size = 251_001,
     graph size = 126_251 *)
Time Qed. (* 0.1 seconds *)

#[display(stats)] Sharing Analysis Definition Body is_nat_500.
(* tree size = 250k, graph size = 1003
   graph size 1k is still too big to print the annotated version *)
