# HANDOFF 2026-10-07 — c⋆ (Bugeaud 10.36 optimal exponent), lap 1

Branch `proof/uniformbad-threshold`.  HEAD after this commit.  Tree clean.

## Done (all axiom-clean)
* `twelve_fifths_le_cStar` (frozen headline, UniformBadThreshold.lean): 25-window exact rational
  cover (bases 2,3,5,10), generic checker `not_admissible_of_cert p q`.  BarrierAudit crux link removed.
* `UniformBadPowerEngine.lean`: `exists_avoid_powPot` (α-power weights, threshold ρ^α, children
  averaged new charges, Good-children predicate with K' good children), `sum_children_powPot_le`.
* `UniformBadTwelve.lean`: `cStar_le_twelve` (K=4096, α=1/4, ρ=1/81, g=1050; per-base 3886/b³).

## Open: `cStar_le_four` (scoped target file still has this one sorry)
See PENDING_WORK.md top section: engines with base 2 inside stall ~c≈7; exact base 2 + engine fails
at c=4 (needs ≥60% good children, run-avoidance gives ≤50%).  Need joint exact handling of bases
≤~16.  Lead: countable Newhouse-thickness gap lemma (τ_b≈b⁴/2, Σ 1/(1+τ_b)≈0.165).  Online request
filed for Falconer–Yavicoli Thm 6 statement.

## Next
1. Check ON-LINE-FINDINGS for the thickness theorem; if usable, state as hypothesis Prop and look
   for a self-contained proof of the d=1 case (Newhouse-style linking for countably many sets).
2. State the thickness route as def-Prop nodes in UniformBadThreshold.lean.
3. Side: c ≤ 11 with the engine (K=1024, α=1/5, margin ~25%).
Scripts: scripts/uniformbad_cstar_cover.py (exact cover generator).
