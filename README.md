Verdi Cheerios
==============

[![Build Status](https://api.travis-ci.org/DistributedComponents/verdi-cheerios.svg?branch=master)](https://travis-ci.org/DistributedComponents/verdi-cheerios)

A verified system transformer for serialization of Verdi systems using the Cheerios library.

Requirements
------------

- [`Coq 8.5`](https://coq.inria.fr/coq-85) or [`Coq 8.6`](https://coq.inria.fr/coq-86)
- [`mathcomp-ssreflect 1.6`](http://math-comp.github.io/math-comp/) or [`mathcomp-ssreflect 1.6.1`](http://math-comp.github.io/math-comp/)
- [`Verdi`](https://github.com/uwplse/verdi)
- [`Cheerios`](https://github.com/uwplse/cheerios)

Building
--------

The recommended way of installing Verdi Cheerios is via [OPAM](http://opam.ocaml.org/doc/Install.html),
which will automatically build and install its dependencies.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install verdi-cheerios
```

To build Verdi Cheerios manually, run `./configure` in the root directory.  This will check for the appropriate version of Coq and ensure all necessary dependencies can be located.

By default, the script assumes that `Verdi`, `StructTact`, and `Cheerios` are installed in Coq's `user-contrib` directory, but this can be overridden by setting the `Verdi_PATH`, `StructTact_PATH`, and `Cheerios_PATH` environment variables.

Finally, run `make` in the root directory.
