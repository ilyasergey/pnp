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

* [Coq](https://coq.inria.fr/download) (>= "8.10.0" & < "8.12~")
* [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.12~")
* [FCSL-PCM](https://github.com/imdea-software/fcsl-pcm) (>= "1.0.0" & < "1.3~")
* [Hoare Type Theory](https://github.com/TyGuS/htt)

### Building

We recommend installing the requirements via [opam](https://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-htt git+https://github.com/TyGuS/htt\#master --no-action --yes
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-htt
```

Then, run `make clean; make` from the root folder. This will compile
all lecture files, solutions and create the file `latex/pnp.pdf` with
lecture notes.
