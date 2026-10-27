# Radical pilot

Read the shared pilot contract.  Work in `RoundTwoRadical.lean`.

First prove the frozen `RelativeNormCancellation` target and refute the frozen
`UniformSiblingLoss` target.  Check the explicit positive control a=0.

The exact identity is
`(2-sqrt(2+a))*(2+sqrt(2+a))=2-a` for a>=-2.
It says that a reduction in the chosen branch's factor is exactly compensated by
its sibling.  A fixed loss c<1 in their whole product is therefore impossible.

Then determine whether iterating relative norms adds ANY restriction beyond the
initial seed and quadratic recursion.  Useful target: a depth-N product identity
over all signed square-root branches, valid for an arbitrary seed in (-2,2).
If it is a formal telescoping identity for every seed, say precisely so.  The
seed 0 (and its algebraicity) is special; changing it is not a counterexample to
the exact pi sequence.  Do not claim that generic compensation rules out every
word-dependent inequality involving that seed.

The genuine frontier is a word-dependent inequality that retains both the chosen
embedding and the seed's arithmetic.  Do not substitute the polygon error bound,
an ordinary height estimate, or the old disk-residue covering premise.

Deliver exact theorem names and scope, checks, and a proposed Maze entry for the
specific norm-loss mechanism actually excluded.  Stop at the first coherent
checkpoint once the compensation test is settled.
