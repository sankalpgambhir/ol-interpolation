## ol-interpolation

Simple implementation of the Orthologic proof system from 

> Guilloud, S., & Kuncak, V. (2023). Orthologic with Axioms. arXiv preprint arXiv:2307.07569.

with a naive proof search (without axioms). After proof search, also provides a
utility for computing the interpolant of a sequent from a proof.

The interpolation (and the interpolant) is linear in the size of the proof,
which is itself guaranteed to be quadratic in the size of the sequent.

### Usage

This is a pretty simple `sbt` project. All relevant files are in
`./src/main/scala/`. Basic definitions of formulas and proofs are in
`definitions/`, alongside code for Latex output. The proof search is in
`proving/`, and interpolation is in `interpolation/`.

The file `Main.scala` and function `test` shows the basic usage of functions and
Latex output.
