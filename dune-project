(lang dune 3.8)
(name rocq-sharing-analyser)

(using coq 0.8)

(package
 (name rocq-sharing-analyser)
 (depends
  (dune (>= 3.8.0))
  (ocaml (>= 4.09.0))
  (coq-core (= dev))
  (coq-stdlib (= dev)))
  (synopsis "Memory sharing analyser for Rocq"))
