# A Formalization of Parts of Rewriting Theory, based on Term Rewriting and All That

A rough and tumble formalization of Rewriting theory in Lean, based on the now [classic book](https://www.cambridge.org/core/books/term-rewriting-and-all-that/71768055278D0DEF4FFC74722DE0D707?utm_campaign=shareaholic&utm_medium=copy_link&utm_source=bookmark).

## Chapter 1

Abstract reduction systems.

Mostly follows the book, sadly does not use much existing machinery from Mathlib (e.g. reflexive transitive closures etc).

Goes up to roughly the Neumann Lemma, with some simple things around commuting relations.

Notations are defined using type classes.

## Chapter 2

The basics of term rewriting, up to the Birkhoff Completeness Theorem for equational logic.

The main design choice here is that we use applicative terms, so `f @@ x @@ (g @@ y)` instead of `f(x, g(y))`.
This simplifies proofs a bit, and opens the door to some slightly more powerful theorem statements, if we allow variables in "application position".

## Chapter 3

Soundness and completeness of syntactic unification.

The proofs are a bit of a mess, but the theorem should be relatively convenient to use. Some slight departure from the book proof, but nothing crazy.

