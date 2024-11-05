# Rocq sharing analyser

A term like `nat -> nat` can be expressed as 2 different graphs in memory:

~~~
  (->)
  /  \
nat  nat
~~~

and

~~~
  (->)
  /  \
  \  /
   nat
~~~

In the second graph the occurrences of `nat` are shared, so it takes less memory.

When the terms get deeper the size of the graph with maximal sharing
can be logarithmic in the size of the term seen as a tree (the tree has no sharing).
For instance `(nat -> nat) -> (nat -> nat)` can be shared as

~~~
  (->)
  /  \
  \  /
  (->)
  /  \
  \  /
   nat
~~~

taking 3 nodes instead of 7.

This project provides a plugin to print debug information about how
Rocq's terms are structured in memory.

# Build and install

Build with `dune build`.

Install with `opam install .` (it will do a separate build).

# Entry points

The entry points are

- `Sharing Analysis Term c.` where `c` is a [term](https://coq.inria.fr/doc/master/refman/language/core/basic.html#grammar-token-term).
  `c` will be typechecked and any defined evars will be expanded before doing the analysis.

- `Sharing Analysis Proof.` while inside a proof. An approximation of
  the proof term which will be sent to the kernel will be analysed.
  The term is essentially what is printed by `Show Proof`.
  (multi-statement proofs such as from `Derive` are currently not supported)

- `Sharing Analysis Definition Body c` where `c` is the name of a constant.
  Its body as stored in the kernel will be analysed.
  `Qed` constants are supported.

- Ltac2 function `analyse` (from [Loader.v](theories/Loader.v)).
  The provided term will be analysed.
  Defined evars present in it will not be expanded for the analysis
  but may be expanded when printing the results.

# Display controls

The results are printed according to the `display` attribute
(according to the output mode argument in Ltac2), which is a list of
the following (by default `#[display(ltac2,stats)]`):

- `stats` (`Stats` in Ltac2): print some stats about the amount of sharing in the analysed term.

- `ltac2` (`Ltac2` in Ltac2): print a pseudo-Ltac2 representation of the term.
  For instance the most shared `(nat -> nat) -> (nat -> nat)` is

~~~
let x2 (* refcount = 2 *) := 'nat in
let x1 (* refcount = 2 *) := '($x2 -> $x2) in
let x0 (* refcount = 1 *) := '($x1 -> $x1) in
x0
~~~

- `debug` (`Debug true` in Ltac2): print the term with annotations about sharing.
  For instance the most shared `(nat -> nat) -> (nat -> nat)` is
  `((* fresh 0 *) ((* fresh 1 *) ((* fresh 2 *) nat -> (* seen 2 *) nat) -> (* seen 1 *) (nat -> nat)))`.

  The subterms of already seen subterms are not annotated, for
  instance we have `(* seen 1 *) (nat -> nat)` instead of
  `(* seen 1 *) ((* fresh 2 *) nat -> (* seen 2 *) nat)`.

  Additionally each subterm is reprinted.

- `short_debug` (`Debug false` in Ltac2): like `debug` but
  already-seen subterms are not printed, ie we get
  `((* fresh 0 *) ((* fresh 1 *) ((* fresh 2 *) nat -> (* seen 2 *)) -> (* seen 1 *)))`.

# Known issues

## Ltac2 display is not real Ltac2

The Ltac2 display mode cannot always be copy-pasted. In particular
when a subterm contains bound variables they will be represented using
pseudocode `mkRel`. Defining `mkRel` using `Constr.Unsafe` could be
done but would still lead to failures at the use site, eg `fun a b : nat => a` is

~~~
let x1 (* refcount = 2 *) := 'nat in
let x3 (* refcount = 1 *) := mkRel 2 in
let x2 (* refcount = 1 *) := '(fun _ : $x1 => $x3) in
let x0 (* refcount = 1 *) := '(fun _ : $x1 => $x2) in
x0
~~~

and `let x2 (* refcount = 1 *) := '(fun _ : $x1 => $x3) in` would fail.

## Display is broken for some terms

In particular attempting to print `fix` terms will produce anomalies.
