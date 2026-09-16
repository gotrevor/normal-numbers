# HANDOFF 2026-09-16 — campaign B: both axes closed; the `a`-side opened

Branch `wip/g5-prime-subset`, HEAD `680d4ed`, tree clean, `lake build` 🟢 **9085 jobs**.
`src/` = the two pre-expedition forbidden-drift `sorry`s (`phaseOscillation`,
`exists_prime_nonresidue`); **zero `axiom`s**.

## Proved this session (all `#print axioms` → `[propext, Classical.choice, Quot.sound]`)

| theorem | content |
|---|---|
| `SchedB.isDisjunctive_subsetWeight_logLog` / `isDisjunctive_residueClass_weight_logLog` | **the merge**: a divergent prime subset `S` (Mertens rate) *and* unbounded `c ≤ log₂log₂` |
| `SchedB.isDisjunctive_weight_logLogPow` | the whole growth class `c_p ≤ A₀(1 + log₂log₂ p)^s` |
| `SchedB.isDisjunctive_subsetWeight_logLogPow`, `isDisjunctive_residueClass_weight_logLogPow` | the merge at that class |
| `audit_isDisjunctive_{weight,subsetWeight,residueClass_weight}_logLogPow` (`G4WeightStatement`) | the audit surface, every abbreviation unwound |

### The two structural moves that did it

1. **The far-field `hW` is a domination, not an equality.**  `sum_abs_farPartW_le_of_layer` /
   `farAvgW_le_of_layer` only used `hW` to bound a sample sum from above, so relaxing it to
   `W.wN m ≤ weightW c m` lets the unbounded §4D apply to `w_{c,S} ≤ w_c`.  That is what made
   the merge cheap (`G4SubsetCTW` → `CFrame` → `CWitness` → `CAssembly`).
2. **One `k₄` for both parameter choices.**  Subset side needs `Dc ≤ k₄` (Mertens inflation),
   unbounded side needs `k₄ = 2^t`; `exists_good_k₄_poly(Gen)` takes an arbitrary `a ≤ k₄`, so
   `a = max ⌈A⌉₊ Dc` buys both.  `exists_good_k₄_polyGen` (`G4PolySched`) does it at any
   polynomial degree, via `exists_lin_le_two_pow (m D) : ∃ T, ∀ t ≥ T, m + Dt ≤ 2^t`.

Supporting: `tame_of_affine_natLog`, `tame_of_logLog_pow`, `one_add_pow_le_mul_two_pow`
(`(1+ℓ)^s ≤ (s+1)^s 2^ℓ`), `effC_mono`, `effC_numerator_le`, `hbudget_holdsΩE_gen`.

## Where the work now stands

Campaign B's stated objective is `w(n) = ∑_{p∣n}(a_p + c_p(v_p(n)−1))`.  The **`c`-side is
finished** (unbounded, whole polylog class, on a prime subset).  The **`a`-side is the one
piece left**: a general *bounded* `a`, not just `a = 1` or `a = 1_S`.

* **Done**: the arithmetic layer, `G4WeightA` — `weightAW`, `weightAN`, integrality
  (`weightAW_eq_cast`), transport (`weightAW_mul`), `TWeight.weightA a c hCa hT`, and the two
  sanity instances (`weightAW_one`, `weightAW_indicator`).  None of it touches §4C.
* **The crux (next lap)**: §4C's `Sval` is the *indicator* vector `omegaOn sm`.  For a general
  `a` the local phase at `p` is `a_p · localPhase p ρ x n` (`G4PhaseDecomp.phase_eq_sum_local`
  goes through verbatim), so `norm_localSum_le` runs at the **scaled frequency** `a_p·q`.
  Attack, in order:
  1. `SvalA a` and `totalPhaseA`, with `phase_eq_sum_localA : totalPhaseA = ∑_p a_p·localPhase p`;
  2. the good-prime gain at `a_p q`: nonzero because `1 ≤ a_p` on the active set
     `S = {p : a_p ≥ 1}`, with the frequency box enlarged `D → Ca·D` (check `freqSeed`'s
     separation hypothesis is stated for the enlarged box — this is the decisive step);
  3. everything downstream is the subset proof at `S = {p : a_p ≥ 1}`, whose divergence is the
     hypothesis, so `isDisjunctive_weightA` should follow with no new §4D work.
* The `c_p ≍ log p` boundary stays a **proved obstruction** of this schedule family
  (`DESIGN-2026-09-16-prime-subset.md`): `cMax ≈ 2^{21K²}` against an exponential junk budget.

`PENDING_WORK.md` §B6 carries the same plan in table form.  `DIRECTION.md` is unchanged
(altitude laps own it).
