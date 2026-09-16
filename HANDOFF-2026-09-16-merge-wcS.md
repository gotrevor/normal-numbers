# HANDOFF 2026-09-16 — campaign B merge PROVED: `w_{c,S}` with unbounded `c`

Branch `wip/g5-prime-subset`, `lake build` 🟢 9080 jobs, `src/` unchanged at the two
pre-expedition forbidden-drift `sorry`s, zero `axiom`s.

## The headline

```lean
theorem NormalNumbers.G4.SchedB.isDisjunctive_subsetWeight_logLog (c : ℕ → ℕ)
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {cm Cm : ℝ}
    (hmert : MertensAP.MertensRate S cm Cm) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetWeightLambert S c b)

theorem NormalNumbers.G4.isDisjunctive_residueClass_weight_logLog {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) (c : ℕ → ℕ)
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetWeightLambert (fun p => (p : ZMod q) = a) c b)
```

Both `#print axioms` → `[propext, Classical.choice, Quot.sound]`.  This is the campaign's
declared endpoint: both axes at once — a divergent **prime subset** `S` *and* an **unbounded**
coefficient vector `c`.

## What landed, in order (each its own green commit)

| commit | content |
|---|---|
| `574c79b` | `TWeight.weightSU S c hT`.  Plus the structural move that made the merge possible: `sum_abs_farPartW_le_of_layer` / `farAvgW_le_of_layer` now take `hW` as a **pointwise domination** `W.wN m ≤ weightW c m`, not an equality.  `hW` was only ever used to bound a sample sum from above, so the far field applies to any weight dominated by `w_c`. |
| `e2d8c7f` | `G4SubsetCFrame`: the merged four-way split `weightSC_split`, `frozenGammaSC`, `gridFrameW_weightSC_Ffull_decomp`, `gridFrameW_weightSC_propD`, and `gridFrameW_weightSU_propD_of_bounds` at `effC`.  `effC_mono` lets §4D consume the schedule's bound stated at `c` rather than at `c·1_S`. |
| `4ed4aac` | `ScheduleWitnessSU` + `isDisjunctive_weightSU_of_witness`. |
| `53d1869` → this | `hbudget_holdsΩE_gen` (Ω-shaped budget over an arbitrary sub-family of small primes), `scheduleWitnessSUE`, `exists_scheduleWitnessSU`, the two headlines. |

## Why the two parameter choices do not collide

The subset side needs `Dc ≤ k₄` (`Dc ≈ 1/(cm log 2)`, the Mertens-rate inflation of the cutoff
exponent `e`); the unbounded side needs `k₄ = 2^t` so `100000·C(k₄)·k₄³ ≤ 2^{k₄}` survives the
`effC`-polynomial `C(k₄) = ⌈A⌉₊ + 368k₄² + 88320k₄⁴`.  `exists_good_k₄_poly` already accepts an
arbitrary `a ≤ k₄`; passing `a = max ⌈A⌉₊ Dc` buys both.  No new estimate was needed.

## Resume here

1. Generalize the coefficient class from `c ≤ log₂log₂` to `c_p ≤ A(1+log₂log₂ p)^s`: only
   `cMax_le_of_logLog` and the `C`-polynomial change (`exists_good_k₄_poly` needs degree `3+4s`).
   This now automatically upgrades the merge too, since the merge consumes `effC` abstractly.
2. Audit surface: state the three campaign-B headlines in `Statement.lean` and add them to
   `STATUS.md`'s trust-triple list.
3. The `S = univ` sanity instance for the merged weight (`weightSW_univ` + `mertensRate_univ`
   should re-derive `isDisjunctive_weight_logLog`).

## Addendum (same session): B4 — the growth class, and the merge at the growth class

`lake build` 🟢 9083 jobs.  New, all `[propext, Classical.choice, Quot.sound]`:

* `tame_of_logLog_pow` (`G4LogLogPow`): `c_p ≤ A₀(1 + log₂log₂ p)^s` is tame at
  `A = 5A₀(s+1)^s + 1`.  Ingredients: `one_add_pow_le_mul_two_pow : (1+ℓ)^s ≤ (s+1)^s 2^ℓ`
  (write `q = ℓ/s`; `1+ℓ ≤ (s+1)(q+1)` and `(q+1)^s ≤ 2^{sq} ≤ 2^ℓ`) and the new
  `tame_of_affine_natLog` (an affine-in-`log₂` bound is tame).
* `exists_good_k₄_polyGen` (`G4PolySched`): a `k₄` for `100000(a + γk₄^d)k₄³ ≤ 2^{k₄}` at any
  degree `d ≥ 1`, via `exists_lin_le_two_pow (m D) : ∃ T, ∀ t ≥ T, m + Dt ≤ 2^t` (threshold
  `T = 8·max(m+D,2)`, base case `9a² ≤ a^8`).
* `isDisjunctive_weight_logLogPow` and `isDisjunctive_subsetWeight_logLogPow` /
  `isDisjunctive_residueClass_weight_logLogPow` (`G4LogLogPowSched`): the headline and the
  merge for the whole class, with `cMax ≤ A₀(1+V)^s`, `effC` numerator
  `≤ 256A₀384^s·k₄^{2s+2}` (`effC_numerator_le`), degree `d = 2s+2`.

**Still the boundary** (`DESIGN-2026-09-16-prime-subset.md`): `c_p ≍ log p` needs
`cMax ≈ 2^{21K²}`, past the exponential junk budget — no power of `log log` reaches it.
