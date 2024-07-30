(lang dune 3.16)

(name dolmen_skolemize)

(generate_opam_files true)

(source
 (github Lorocas/dolmen_skolemize))

(authors "Lorenzo LUCAS -- ROBLOT, Quentin PEPE")

(maintainers "Lorenzo LUCAS -- ROBLOT, Quentin PEPE")

; (license LICENSE)

; (documentation https://url/to/documentation)

(package
 (name dolmen_skolemize)
 (synopsis "Skolemization of a TPTP problem using Dolmen")
 (description "This project provides a tool that skolemize a TPTP problem using Dolmen and creates a new file with more information named 'signature.lp'. It works with SKonverto.")
 (depends ocaml dune)
 (tags
  ("Dolmen" "Skolemization" "Skolem")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
