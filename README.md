Herbie support for complex numbers
===

This repository contains a plugin for
[Herbie](https://herbie.uwplse.org) to support complex numbers. So
far, `+`, `-`, `*`, `/`, `sqrt`, `pow`, `exp`, and `log` are all
supported, as is the new constant `I` and the new operator `conj`.
Create complex numbers with `complex`, `re`, and `im`.

This package contains:

+ Definitions of complex numbers and their operators for Herbie
+ Teach Herbie rewrite rules for these operators

However, you cannot yet have complex inputs to Herbie cores. You will
need to take two real arguments and package them into a complex number
via `complex`

The best way to install this package is using the Racket package manager:

    raco pkg install complex-herbie
