## A Short Course on Interactive Proofs in Coq/Ssreflect

This project contains the Coq sources, the lectures and the exercises
for the course

**"Programs and Proofs: Mechanizing Mathematics with Dependent Types"**.

The latest draft of the accompanying lecture notes can be downloaded
from the official course page:

http://ilyasergey.net/pnp

Initial release: August 2014

* [Coq 8.7](https://coq.inria.fr/coq-87)
* [Mathematical Components 1.6.4](http://math-comp.github.io/math-comp/) (`ssreflect`)

### Building

We recommend installing the requirements via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

Then, run `make clean; make` from the root folder. This will compile
all lecture files, solutions and create the file `latex/pnp.pdf` with
lecture notes.
