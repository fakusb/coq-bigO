## coq-bigO

This library is described in the paper "A Fistful of Dollars: Formalizing
Asymptotic Complexity Claims via Deductive Program Verification" (under
submission:
[preprint](http://gallium.inria.fr/~agueneau/publis/gueneau-chargueraud-pottier-coq-bigO.pdf)).

[This page](http://gallium.inria.fr/~agueneau/bigO/) describes quick setup
instructions for building the examples presented.

-----------

Installation instructions (using [opam](https://opam.ocaml.org)):

- Install Coq 8.6
- Install TLC: `opam pin add coq-tlc https://gitlab.inria.fr/charguer/tlc.git#coq-8.6`
- Install CFML (required to build the examples): `opam pin add coq-cfml https://gitlab.inria.fr/charguer/cfml.git#coq-8.6`
- Run `make` to compile the library
- Run `make examples` to compile the examples
