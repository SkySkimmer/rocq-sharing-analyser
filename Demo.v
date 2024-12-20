From Ltac2 Require Import Ltac2.
From SharingAnalyser Require Import Loader.

Sharing Analysis Term 0.

Ltac2 default_mode := [Debug true;Stats].

Ltac2 Eval analyse default_mode '(0,0).
Ltac2 Eval analyse default_mode (let x := '0 in '($x,$x)).
Ltac2 Eval analyse [Debug true] (let x := '0 in '($x,$x)).

(* the "nat" aren't shared because hcons operates on the non evar normalized term
   XXX maybe we should be printing the evars instead of their definitions? *)
Ltac2 Eval analyse [Ltac2] (hcons '(0,0)).

(* here we can see that the analysis did not recurse into evar
   definitions as there's a raw "(nat * nat)%type" term *)
Ltac2 Eval analyse [Ltac2] (hcons '(0,0,0)).

(* "constr:($c)" is optimized to "c" skipping the evar normalization *)
Ltac2 nf_evar c := Constr.pretype preterm:($c).

(* now hcons is operating on the final constr *)
Ltac2 Eval analyse [Ltac2] (hcons (nf_evar '(0,0))).

Goal nat * nat.
  exact (0,0).
  #[display(debug,stats)] Sharing Analysis Proof.
Abort.

Definition foo := (0,0).

#[display(debug,stats)] Sharing Analysis Definition Body foo.

Definition bar := (0,0,0,0,0,0).

#[display(debug)] Sharing Analysis Definition Body bar.

#[display(ltac2,stats)] Sharing Analysis Definition Body bar.

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
     graph size = 76
     edge sharing factor = 0% (ie only leaves are shared)
   *)
Qed.

#[display(stats)] Sharing Analysis Definition Body is_nat_10.
(* tree size = 121
   graph size = 23
   edge count = 49 *)

#[display(ltac2)] Sharing Analysis Definition Body is_nat_10.
(* mostly applications so kinda hard to read
   maybe if we inlined refcount = 1 subterms?
   and somehow improved the binding names so that eg we get
   "let xIsnat_S := 'Isnat_S in"
   instead of
   "let x1 := 'Isnat_S in"
   ??
*)

#[display(short_debug)] Sharing Analysis Definition Body is_nat_10.
(* pretty unreadable *)

#[display(debug)] Sharing Analysis Definition Body is_nat_10.
(* not too terrible I guess *)

Lemma is_nat_500 : is_nat 500.
Proof.
  repeat constructor.
  #[display(stats)] Sharing Analysis Proof.
  (* tree size = 251_001,
     graph size = 126_251 *)
Time Qed. (* 0.1 seconds *)

#[display(stats)] Sharing Analysis Definition Body is_nat_500.
(* tree size = 250k, graph size = 1003, edge count = 2499
   graph size 1k is still too big to print the annotated version *)

#[display(ltac2)] Sharing Analysis Definition Body is_nat_500.
(* ltac2 is O(graph_size) so can be printed, debug is O(tree_size) so can't
   short_debug should be O(graph_size) but seems to blow the printing depth limit

   for ltac2 display, inlining refcount = 1 subterms seems like it would be good
   o this example about half the subterms are refcount = 1, another half refcount = 2
   (and the leaves "Is_nat_S" and "S" are refcount 500 and 499 respectively)
*)

(* XXX ltac2 and debug displays fail because we broke the "fix" invariants *)
#[display(stats)] Sharing Analysis Definition Body Nat.add.

(* bound variables are fine though (we have some custom printing in ltac2 mode) *)
Sharing Analysis Definition Body plus_n_O.

#[display(debug)] Sharing Analysis Definition Body plus_n_O.

(* NB: shared "nat" subterms *)
Ltac2 Eval
  let c := constr:(let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

(* lazy, cbv, vm_compute, unfold reductions destroy sharing (and unshare the let binding) *)
Ltac2 Eval
  let c := eval lazy in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

Ltac2 Eval
  let c := eval cbv in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

Ltac2 Eval
  let c := eval vm_compute in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

(* unfold destroys sharing even when the constant to unfold does not appear *)
Ltac2 Eval
  let c := eval unfold Nat.add in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

(* simpl, cbn manage to keep a little sharing but only on leaves *)
Ltac2 Eval
  let c := eval simpl in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

Ltac2 Eval
  let c := eval cbn in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

(* lazy head, hnf are fine (at least on this example) *)
Ltac2 Eval
  let c := eval lazy head zeta in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.

Ltac2 Eval
  let c := eval hnf in (let x := 1 in (x, x)) in
  analyse [Ltac2;Stats] c.
