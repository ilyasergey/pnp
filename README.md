# Programs and Proofs

A Short Course on Interactive Proofs in Coq/Ssreflect. This project
contains the Coq sources, the lectures and the exercises for the
course

**"Programs and Proofs: Mechanizing Mathematics with Dependent Types"**.

The latest draft of the accompanying lecture notes can be downloaded
from the official course page:

http://ilyasergey.net/pnp

Initial release: August 2014

## Building the Project

### Requirements

* [Coq 8.7](https://coq.inria.fr/coq-87) or [Coq 8.8](https://github.com/coq/coq/releases/tag/V8.8.2)
* [Mathematical Components 1.6.4 or 1.7.0](http://math-comp.github.io/math-comp/) (`ssreflect`)
* [FCSL PCM 1.0.0](https://github.com/imdea-software/fcsl-pcm)

### Building

We recommend installing the requirements via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-fcsl-pcm
```

Then, run `make clean; make` from the root folder. This will compile
all lecture files, solutions and create the file `latex/pnp.pdf` with
lecture notes.
