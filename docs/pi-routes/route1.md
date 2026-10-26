# Route 1 (triple return) — direction notes and false starts

Lean home: `src/NormalNumbers/PiDisjunctiveRoutes/TripleReturn.lean`.

## Structural finding
`tripleReturn_iff_disjunctive` and `mem_circleOmegaLimit_oddMul_iff_disjunctive` (both proved):
for irrational x, `q x ∈ K := ω₂(x)` for one odd q ≥ 3 is *equivalent* to binary disjunctivity.
So no single-odd-multiple target is weaker than the sink.  The Furstenberg step only uses
(i) a non-torsion point of K and (ii) ×q-invariance of K; (ii) is the whole difficulty.

## False starts
| idea | why promising | why it fails | witness |
|---|---|---|---|
| "a cheaper return target qπ, q odd" | q free to choose | each is equivalent to the sink | `mem_circleOmegaLimit_oddMul_iff_disjunctive` |

## Probe: first return n_k (scripts/pi_route1_first_return.py, K=9)
Target: n_k ≤ C·4^k with small C.  Control 1/3: returns only at k=1 (as predicted).
π: n_k = 1,2,5,16,16,16,101,240,240 for k=1..9 — at or below 2^k throughout, C = 1 suffices.
√2: 1,3,3,5,5,13,13,120,120.  Verdict: premise constant not refuted; consistent with ~2^k heuristic.
| "irrationality suffices for a non-torsion point of K" | Furstenberg needs only one | `∑2^{-i!}` has K all torsion | `liouvilleTwo_irrational_and_orbitClosure_torsion` |
