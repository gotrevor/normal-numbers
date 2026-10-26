# HANDOFF — pi route 1 (triple return), lane 1

## Node graph (`src/NormalNumbers/PiDisjunctiveRoutes/TripleReturn.lean`)
- `PiQuantitativeTripleReturn` (premise, open, 90% heuristic) —proved→ `TripleReturn π`
  (`pi_disjunctive_of_quantitativeTripleReturn`, sorry-free).
- `TripleReturn x ↔ (3x : 𝕋) ∈ circleOmegaLimit 2 x` (`tripleReturn_iff_mem_circleOmegaLimit`).
- `Irrational x → (TripleReturn x ↔ IsDisjunctive 2 x)` (`tripleReturn_iff_disjunctive`, sorry-free;
  axioms propext/choice/Quot.sound).  Mechanism: 3x ∈ K ⇒ 3K ⊆ K (`mapsTo_three_circleOmegaLimit`);
  K contains non-torsion 3x ⇒ infinite; Furstenberg ×2×3 ⇒ K = 𝕋.
- Costume audit: TripleReturn is the sink in a costume (proved equivalence).

## This lap
Bridges green (both lane-1 "first" theorems proved).

## Next move
Research question: which single target t (tied to π) can be shown in K = ω₂(π)?  Note the proof
only used "some non-torsion y with y ∈ K and 3K ⊆ K"; next, state the weaker node
"∃ m, 3·2^m π-type target or any q·π (q odd ≥3) in K" — K ∋ qπ ⇒ qK ⊆ K, and Furstenberg needs
only MultIndep 2 q, so any odd q ≥ 3 works.  State that generalisation as a theorem, then run
the probe `scripts/pi_route1_first_return.py` (first-return n_k of ‖(2^n−3)π‖<2^-k, control: a
rational, e.g. 1/3, and a known-normal-ish surrogate).
