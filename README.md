## coq-bigO

This library is described in the paper "A Fistful of Dollars: Formalizing
Asymptotic Complexity Claims via Deductive Program Verification" (at
ESOP'18:
[preprint](http://gallium.inria.fr/~agueneau/publis/gueneau-chargueraud-pottier-coq-bigO.pdf)).

[This page](http://gallium.inria.fr/~agueneau/bigO/) describes quick setup
instructions for building the examples presented.

-----------

Installation instructions (using [opam](https://opam.ocaml.org) and
the [opam coq repository](https://github.com/coq/opam-coq-archive)):

- Install Coq >= 8.6
- Install TLC, CFML, and Procrastination: `opam install coq-tlc coq-cfml coq-procrastination`
- Run `make` to compile the library
- Run `make examples` to compile the examples
