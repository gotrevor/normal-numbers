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
