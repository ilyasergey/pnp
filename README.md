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

* [Coq](https://coq.inria.fr/download), versions from 8.7 to 8.11.1
* [Mathematical Components](http://math-comp.github.io/math-comp/), versions from 1.6.2 to 1.10.0 (`ssreflect` package)
* [FCSL-PCM](https://github.com/imdea-software/fcsl-pcm), versions 1.0.0, 1.1.0, or 1.2.0

### Building

We recommend installing the requirements via [opam](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-fcsl-pcm
```

Then, run `make clean; make` from the root folder. This will compile
all lecture files, solutions and create the file `latex/pnp.pdf` with
lecture notes.
