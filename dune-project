(lang dune 2.0)
(name l2)
(source (github jfeser/l2))
(license Apache2.0)
(authors "Jack Feser <feser@mit.edu>")
(maintainers "Jack Feser <feser@mit.edu>")

(package
  (name l2)
  (synopsis "Enumerative program synthesizer")
  (depends
    (ocaml (>= 4.08))
    (dune (>= 2))
    (menhir (>= 20190924))
    (core (and (>= v0.13) (< v0.14)))
    (yojson (>= 1.7))
    (hashcons (>= 1.3))

    (ppx_compare (and (>= v0.13) (< v0.14)))
    (ppx_hash (and (>= v0.13) (< v0.14)))
    (ppx_let (and (>= v0.13) (< v0.14)))
    (ppx_sexp_conv (and (>= v0.13) (< v0.14)))

    (ounit (and :with-test (>= 2.2)))))

(generate_opam_files true)
(using menhir 2.0)
