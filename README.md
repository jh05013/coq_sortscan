# coq_sortscan
Formal verification of sort-based query execution in Coq

# Building
This may be enough to run the codes for this project but it's untested. I'll check soon.

Run

```
opam switch create . ocaml-system --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add -n -y coq 8.15.0
opam install coq-stdpp
```

Then run `eval $(opam env)`.
