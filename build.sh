opam switch create . ocaml-system --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add -n -y coq 8.15.0
opam install coq-stdpp
