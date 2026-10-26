# Route 1 (triple return) — direction notes and false starts

Lean home: `src/NormalNumbers/PiDisjunctiveRoutes/TripleReturn.lean`.

## Structural finding
`tripleReturn_iff_disjunctive` and `mem_circleOmegaLimit_oddMul_iff_disjunctive` (both proved):
for irrational x, `q x ∈ K := ω₂(x)` for one odd q ≥ 3 is *equivalent* to binary disjunctivity.
So no single-odd-multiple target is weaker than the sink.  The first proof used
(i) a non-torsion point of K and (ii) ×q-invariance of K.

## Review correction, 2026-10-26

Here K is the **ω-limit set**, not the full orbit closure.  The full closure always
contains x itself.  The Liouville example has an all-torsion ω-limit set but an
irrational point in its full closure.

More substantially, non-torsion in K is unnecessary: K is infinite for every
irrational x.  Compactness turns a finite ω-limit set into a finite attractor,
which the existing `MasterConjectures.not_irrational_of_hasFiniteAttractor_base`
excludes.  The statements and proof are in `TripleReturnReview.lean`:
`circleOmegaLimit_infinite_of_irrational`, `pi_disjunctive_iff_oddInvariant`.
Thus `PiSelfReturn` is not needed to supply a missing prerequisite.  The open
arithmetic target is odd invariance alone.  The abstract counterexample excludes
deriving odd invariance from doubling invariance; it does not refute the π target.

## False starts
| idea | why promising | why it fails | witness |
|---|---|---|---|
| "a cheaper return target qπ, q odd" | q free to choose | each is equivalent to the sink | `mem_circleOmegaLimit_oddMul_iff_disjunctive` |

## Probe: first return n_k (scripts/pi_route1_first_return.py, K=9)
Target: n_k ≤ C·4^k with small C.  Control 1/3: returns only at k=1 (as predicted).
π: n_k = 1,2,5,16,16,16,101,240,240 for k=1..9 — at or below 2^k throughout, C = 1 suffices.
√2: 1,3,3,5,5,13,13,120,120.  Verdict: premise constant not refuted; consistent with ~2^k heuristic.
| "irrationality suffices for a non-torsion point of K" | a sufficient Furstenberg premise | `∑2^{-i!}` has ω-limit set all torsion; review: infinitude is automatic and already sufficient | `liouvilleTwo_irrational_and_orbitClosure_torsion`, `circleOmegaLimit_infinite_of_irrational` |
| "a ×2-closed set with an irrational point is ×3-invariant" | would close (ii) from (i) | false | `exists_closed_two_invariant_nonTorsion_not_three_invariant` |
