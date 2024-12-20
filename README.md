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

(Note: currently Rocq only uses in-memory sharing to reduce memory usage and
shortcut some equality tests.)

See [Demo.v](Demo.v) for examples.

## Build and install

Supported Coq versions: 8.20, maybe master. If it compiles then it should work.

Build with `dune build`.

Install with `opam install .` (it will do a separate build).

## Entry points

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

## Display controls

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
  For instance on the most shared `(nat -> nat) -> (nat -> nat)` it prints

  ~~~
  ((* fresh 0 *) ((* fresh 1 *) ((* fresh 2 *) nat -> (* seen 2 *) nat) -> (* seen 1 *) (nat -> nat)))

  subterms:
  0 (refcount = 1) ==>
    ((* fresh 0 *) ((* fresh 1 *) ((* fresh 2 *) nat -> (* seen 2 *) nat) -> (* seen 1 *) (nat -> nat)))
  1 (refcount = 2) ==> ((* fresh 1 *) ((* fresh 2 *) nat -> (* seen 2 *) nat))
  2 (refcount = 2) ==> ((* fresh 2 *) nat)
  ~~~

  The subterms of already seen subterms are not annotated, for
  instance we have `(* seen 1 *) (nat -> nat)` instead of
  `(* seen 1 *) ((* fresh 2 *) nat -> (* seen 2 *) nat)`.

- `short_debug` (`Debug false` in Ltac2): like `debug` but
  already-seen subterms are not printed, ie we get
  `((* fresh 0 *) ((* fresh 1 *) ((* fresh 2 *) nat -> (* seen 2 *)) -> (* seen 1 *)))`.

## Implementation

Sharing analysis cannot be implemented in OCaml because there is no
way while traversing a value to efficiently tell whether it was
previously encountered.

Instead we do a first traversal in C, using a modified version of
OCaml's marshalling code. Since the C code does not call the GC while
traversing, pointer values of traversed OCaml values are stable and
can be used as keys in a hashtable for quick recognition.

An OCaml wrapper is exposed at
[lib/sharingAnalyser.mli](lib/sharingAnalyser.mli).

The function `analyse` traverses (depth-first, left to right) the
given value according to a `type_descr`, and for specified nodes
records whether they have been previously encountered in the
traversal. The traversal can then be replayed in OCaml code, doing a
`step` at each recorded node to get sharing information.

The code in `lib/` is independent of Rocq.

[plugin/analyseConstr.ml](plugin/analyseConstr.ml) then uses the core
analysis library to annotate Rocq terms,
[plugin/analyser.ml](plugin/analyser.ml) prints the result and defines the entry points,
and [plugin/g_analyser.mlg](plugin/g_analyser.mlg) declares the grammar.

[theories/Loader.v](theories/Loader.v) contains the `Declare ML Module`
and Ltac2 declarations.

## Known issues

### Ltac2 display is not real Ltac2

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

### Debug display is incorrect when implicits or coercions are involved

For instance on `id 0` we get `((* fresh 0 *) ((* fresh 1 *) id ((* fresh 2 *) nat) ((* fresh 3 *) 0)))`.

Debug display should be read as though there were no implicit arguments or coercions declared.

### Display is broken for some terms

In particular attempting to print `fix` terms will produce anomalies.
