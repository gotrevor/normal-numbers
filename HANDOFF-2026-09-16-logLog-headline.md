# HANDOFF 2026-09-16 — campaign B headline PROVED: unbounded coefficients

Branch `wip/g5-prime-subset`, HEAD `720b723`, tree clean, `lake build` 🟢 **9076 jobs**.
`src/` carries exactly the two pre-expedition forbidden-drift `sorry`s (`phaseOscillation`,
`exists_prime_nonresidue`); **zero `axiom`s**.

## The headline

```lean
theorem NormalNumbers.G4.SchedB.isDisjunctive_weight_logLog (c : ℕ → ℕ)
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (PrimeLambert.weightLambert b c)
```

`#print axioms` → `[propext, Classical.choice, Quot.sound]`.  First **unbounded** coefficient
vector: `w(n) = ω(n) + ∑_{p∣n} c_p(v_p(n)−1)` with `c_p → ∞`.

## What landed this lap (in order, each its own green commit)

| commit | content |
|---|---|
| `3a0e748` | **B2d**: §4D frame plumbing generic in the `TWeight` (`gridFrameW_weightC_Ffull_decomp`, `farAvgC → farAvgW`, `gridFrameW_weightC_propD` take `(W, hW)`). |
| `056072e` | **B2d/B2e**: `G4UnboundedFrame` — `farAvgW_le_of_layer`, `farAvgW_le_effC`, `gridFrameW_weightU_propD_of_bounds`.  **`effC` sharpened**: the `frozenCap` branch (size `log P₀`) was fatal — replaced by `cMax = max_{p∣P₀} c_p` via `frozenCap_le_cMax_mul`. |
| `4ed94b7` | **B2e**: `G4UnboundedEffC` — `effC ≤ A + cMax·(1 + log ω(P₀))`. |
| `c57286f` | `prime_le_of_dvd_P₀`: every prime dividing `P₀ = (∏ d_α²)·freezeQ` is `≤ max(Dm, 2T, ρmax)`; hence `effC_le_sched`. |
| `7772846` | **DESIGN**: the junk budget binds (`rowL1 ≤ 3(2/3)^K`), so `effC ≤ 2^{Θ(K)}`; `c_p ≍ log p` is a *proved obstruction* of this schedule, `c_p ≍ log log p` fits. |
| `8757750` | **B3**: `G4LogTame` — `tame_of_natLog_le` (prefix by primorial, tail by the `#{j : 2^j ≤ p}` swap + `sum_inv_mul_pred_Icc_eq`). |
| `7f8675a` | `cMax_le_of_logLog`, `effC_le_of_logLog`. |
| `77fa516` | `G4SchedLogLog.sched_prime_size`: the prime bound at `gridOf K (N K)` is `≤ 2^{2^{23K²}}`. |
| `0f9127d` | `G4UnboundedWitness`: `ScheduleWitnessU` + `isDisjunctive_weightU_of_witness`. |
| `6bb1618` | `exists_good_k₄_poly`: `k₄ = 2^t` breaks the circularity (`effC ← K ← k₄ ← C`), since the budget is exponential and `effC` only polynomial (`34 + 7t ≤ 2^t`). |
| `720b723` | `scheduleWitnessUE` + `exists_scheduleWitnessU` + **the headline**. |

## Where the boundary is (machine-checked reasoning, `DESIGN-2026-09-16-prime-subset.md`)

* junk budget: `C ≲ 2^{0.58K}` (binding, via `rowL1 b K ≤ 3(2/3)^K`); far budget: `κ ≲ 2^{Θ(K²)}`.
* `log₂ pMax ≈ 2^{21K²}` (`Sched.gridDm_le_two_pow`), so `c_p = ⌊log₂ p⌋` ⇒ `cMax ≈ 2^{21K²}` — **past** the budget; `c_p = ⌊log₂log₂ p⌋` ⇒ `cMax ≤ 23K²` — fits.
* Reaching `c_p ≍ log p` would require re-engineering the junk budget (the `(2/3)^K` row-mass factor), not better estimates.

## Resume here

1. **Generalize the class** from `c ≤ log₂log₂` to `c_p ≤ A(1+log₂log₂ p)^s`: only
   `cMax_le_of_logLog` and the `C`-polynomial in `exists_scheduleWitnessU` change
   (`(23K²)^s` is still polynomial; `exists_good_k₄_poly` needs the degree bumped to `3+4s`).
2. **The merge `w_{c,S}`** (`G4SubsetCWeight` §4D): with the `TWeight` instance already there,
   the tame route should now apply verbatim at `a = 1_S`.
3. Optional: state the headline in the audit surface (`Statement.lean`) and add it to
   `STATUS.md`'s trust-triple list.
