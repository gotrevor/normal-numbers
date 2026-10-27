# Radical pilot result

Module: `src/NormalNumbers/PiDisjunctiveRoutes/RoundTwoRadical.lean`
(not imported from the root; the parent integrates).

## Results (all proved, axioms: propext, Classical.choice, Quot.sound)

- `relativeNormCancellation : RelativeNormCancellation` — frozen target proved.
- `relativeNorm_zero` — positive control a = 0: `(2-√2)(2+√2) = 2`.
- `not_uniformSiblingLoss : ¬ UniformSiblingLoss` — refuted at a = 0.
- `branchNorm n x` — product of `2 - y` over all `2^n` signed branches
  `y = ±√(2 + ·)` iterated n times from seed x.
- `branchNorm_eq n : ∀ x ∈ [-2,2], branchNorm n x = 2 - x` — the depth-n product
  is a formal telescoping identity for every seed in [-2,2], not only in (-2,2).
- `not_uniform_branchLoss n` — no constant c < 1 bounds the full depth-n branch
  product by c·(2 - a) uniformly in the seed.

Scope: iterated relative norms (full products over all sign branches) add no
information beyond `2 - seed`.  This says nothing about word-dependent inequalities
on a single chosen branch that use seed 0's arithmetic (e.g. its algebraic
conjugate structure); that frontier was not stated as a Prop because no
non-vacuous formulation was settled in this lap.

## Proposed Maze entry

- Mechanism: "relative-norm / sibling-loss" — bounding the chosen radical branch
  by a uniform factor loss of the product with its sibling(s), at any depth.
- Aliases: norm compensation, Galois-conjugate loss, nested-radical norm descent.
- Crux: `branchNorm_eq` — the full branch product is identically `2 - seed`, so
  any loss in the chosen factor is exactly compensated by siblings.
- Obstruction theorems: `not_uniformSiblingLoss`, `not_uniform_branchLoss`.
- Reopen requirement: an inequality that depends on the specific word (chosen
  embedding) and on seed 0's arithmetic, and is not a function of the full
  product alone; also not the polygon error bound, a plain height bound, or the
  disk-residue covering premise.
