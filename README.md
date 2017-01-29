Verdi Cheerios
==============

[![Build Status](https://api.travis-ci.org/DistributedComponents/verdi-cheerios.svg?branch=master)](https://travis-ci.org/DistributedComponents/verdi-cheerios)

A verified system transformer for serialization of Verdi systems using the Cheerios library.

Requirements
------------

- [`Coq 8.5`](https://coq.inria.fr/download)
- [`Verdi`](https://github.com/uwplse/verdi)
- [`Cheerios`](https://github.com/uwplse/cheerios)
- [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/) (`ssreflect` library)

Building
--------

The recommended way to install Verdi Cheerios is via [OPAM](https://coq.inria.fr/opam/www/using.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install verdi-cheerios
```

To build Verdi Cheerios manually, run `./configure` in the root directory.  This will check for the appropriate version of Coq and ensure all necessary dependencies can be located.

By default, the script assumes that `Verdi`, `StructTact`, and `Cheerios` are installed in Coq's `user-contrib` directory, but this can be overridden by setting the `Verdi_PATH`, `StructTact_PATH`, and `Cheerios_PATH` environment variables.

Finally, run `make` in the root directory.
