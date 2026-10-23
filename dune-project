(lang dune 3.23)

(name cocotreelo)

(generate_opam_files true)

(source
 (uri git+https://github.com/Sarius121/CocoTreeLo))

(authors "Christopher Cohnen")

(maintainers "Christopher Cohnen")

; TODO:
; (license LICENSE)
; (documentation https://url/to/documentation)

(package
 (name cocotreelo)
 (synopsis "Model-Checking First-Order CTL in Multiset Rewrite Systems")
 (description "")
 (depends ocaml z3 ocamlgraph (alcotest :with-test) (ppx_expect :with-test))
 (tags
  ("first-order ctl", "ctl", "first-order", "multiset", "rewriting")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
