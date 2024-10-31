(lang dune 3.8)
(name rocq-sharing-analyser)

(using coq 0.8)

(generate_opam_files true)

(package
 (name rocq-sharing-analyser)
 (depends
  (dune (>= 3.8.0))
  (ocaml (>= 4.09.0))
  (coq-core (= 8.20.0))
  (coq-stdlib (= 8.20.0)))
  (synopsis "Memory sharing analyser for Rocq"))
