/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRuns

/-!
# The abstract kicked-orbit dichotomy (R2, the general lemma)

Companion to `docs/alien-review-2026-08-29.md` (transmission 2, move R2) and
`docs/lit-sweep-2026-08-29.md`.  The τ-floor/sliver mechanism proved for
`ln 2` (`LnTwoRuns.lean`) used nothing about `ln 2` except: the true orbit
is the surrogate perturbed by a tail trapped in `[lo, hi]` with `lo > 0`.
This file extracts the mechanism at that generality, for **any base `b` and
any BBP-type decomposition `x = s + tail`**:

* `orbit_eq_fract_add_tail`: the generic bracket
  `orbit b x n = fract (fract (bⁿ·s) + bⁿ·(x − s))`;
* `blockNatVal_replicate_max`: the max-digit run value `b^k − 1`
  (generalizing the base-2 `blockNatVal_replicate_one`);
* `occursAt_replicate_zero_iff'` / `occursAt_replicate_max_iff`: base-`b`
  run dictionary — a run of `k` zeros (max digits `b−1`) at position `n` is
  an orbit visit to `[0, b⁻ᵏ)` (`[1 − b⁻ᵏ, 1)`);
* **the dichotomy core** `top_sliver_of_fract_small` /
  `top_sliver_of_fract_large`: one-position real lemmas — if the perturbed
  point lands within `ε < lo` of the wrap and the perturbation is trapped
  in `[lo, hi]`, the base point sits in the top sliver;
* **the packaged dichotomy** `top_sliver_of_zeroRun_tail` /
  `top_sliver_of_maxRun_tail`: a digit run deeper than the tail floor
  forces the surrogate `fract (bⁿ·s)` into the top sliver.

🚨 **Lagarias guardrail** (sweep doc): a magnitude-only kick/tail floor can
never yield an equidistribution-or-finite conclusion — his adversarial
family `θ = Σ ε_n b^{−n}` survives any `ε_n ≥ c/n` floor.  Every conclusion
here is deliberately at the **forcing level** (run ⟹ sliver ride), which is
what survives that acid.

Instances: `ln 2` (base 2, kick `1/(n+1)`; the frozen statements stay in
`LnTwoRuns.lean` — an `example` below re-derives one from the abstract core
as a sanity anchor) and π (base 16, BBP kick, `PiBBP.lean`).  Sweep verdict
2026-08-29: kick-floor-as-resource and the run-forcing direction NOT FOUND
in the literature; Bailey–Borwein 2012 (Stoneham nonnormality) proves the
converse (easy, bottom-sliver) direction for an engineered constant and is
the compare-against citation.
-/

namespace NormalNumbers

/-! ### The dichotomy core: one-position real lemmas -/

/-- **Zero-side dichotomy core.**  If the perturbed point `u + τ` has
fractional part below `ε`, and the perturbation is trapped in
`[lo, hi] ⊆ (ε, 1]`, then `u` sits in the top sliver `[1 − hi, 1)`: the
no-wraparound branch is impossible because there `fract (u + τ) ≥ τ ≥ lo > ε`. -/
theorem top_sliver_of_fract_small {u τ lo hi ε : ℝ}
    (hu0 : 0 ≤ u) (hlo : lo ≤ τ) (hτhi : τ ≤ hi)
    (hε : ε < lo) (hfr : Int.fract (u + τ) < ε) :
    1 - hi ≤ u := by
  have h0 : (0 : ℝ) ≤ Int.fract (u + τ) := Int.fract_nonneg _
  have hτ0 : 0 ≤ τ := by linarith
  rcases lt_or_ge (u + τ) 1 with hlt | hge
  · exfalso
    rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩] at hfr
    linarith
  · linarith

/-- **Max-side dichotomy core.**  If the perturbed point `u + τ` has
fractional part within `ε` of `1`, with the perturbation trapped in
`[lo, hi]`, `ε < lo`, and `hi, ε ≤ 1/2`, then `u ∈ [1 − hi − ε, 1)`: the
wraparound branch would force `u ≥ 2 − ε − τ ≥ 1`. -/
theorem top_sliver_of_fract_large {u τ lo hi ε : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hlo : lo ≤ τ) (hτhi : τ ≤ hi) (hhi : hi ≤ 1 / 2)
    (hε : ε < lo)
    (hfr : 1 - ε ≤ Int.fract (u + τ)) :
    1 - hi - ε ≤ u := by
  have h1 : Int.fract (u + τ) < 1 := Int.fract_lt_one _
  have hε0 : 0 < ε := by linarith
  have hτ0 : 0 ≤ τ := by linarith
  rcases lt_or_ge (u + τ) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩] at hfr
    linarith
  · exfalso
    have hfr2 : Int.fract (u + τ) = u + τ - 1 := by
      have h2 : u + τ - 1 + ((1 : ℤ) : ℝ) = u + τ := by push_cast; ring
      rw [← h2, Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      push_cast
      ring
    rw [hfr2] at hfr
    linarith

/-! ### The generic bracket -/

private lemma fract_fract_add' (y d : ℝ) :
    Int.fract (Int.fract y + d) = Int.fract (y + d) := by
  have h : Int.fract y + d = y + d - ((⌊y⌋ : ℤ) : ℝ) := by
    have h2 := Int.floor_add_fract y
    linarith
  rw [h, Int.fract_sub_intCast]

/-- **Generic bracket**: for any decomposition `x = s + (x − s)`, the true
orbit is the surrogate `fract (bⁿ·s)` perturbed by the scaled tail. -/
theorem orbit_eq_fract_add_tail (b : ℕ) (x s : ℝ) (n : ℕ) :
    orbit b x n
      = Int.fract (Int.fract ((b : ℝ) ^ n * s) + (b : ℝ) ^ n * (x - s)) := by
  rw [orbit, fract_fract_add']
  congr 1
  ring

/-! ### Base-`b` run dictionary -/

theorem blockNatVal_replicate_max (b k : ℕ) (hb : 1 ≤ b) :
    blockNatVal b (List.replicate k (b - 1)) = b ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, blockNatVal_cons, ih, List.length_replicate, pow_succ]
      have h1 : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
      have h3 : (b - 1) * b ^ k = b * b ^ k - 1 * b ^ k := Nat.sub_mul b 1 (b ^ k)
      have h5 : b ^ k ≤ b * b ^ k := Nat.le_mul_of_pos_left _ (by omega)
      rw [h3, one_mul, Nat.mul_comm (b ^ k) b]
      generalize hM : b * b ^ k = M at h5 ⊢
      generalize b ^ k = A at h1 h5 ⊢
      omega

/-- Base-`b` zero-run dictionary: a run of `k` zeros at position `n` is an
orbit visit to `[0, b⁻ᵏ)`. -/
theorem occursAt_replicate_zero_iff' (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n k : ℕ) :
    OccursAt b x (List.replicate k 0) n ↔
      orbit b x n ∈ Set.Ico (0 : ℝ) (1 / (b : ℝ) ^ k) := by
  rw [occursAt_iff_orbit_mem b hb x _
      (fun e he => by rw [List.eq_of_mem_replicate he]; omega) n,
    blockNatVal_replicate_zero, List.length_replicate]
  norm_num

/-- Base-`b` max-digit run dictionary: a run of `k` copies of the top digit
`b − 1` at position `n` is an orbit visit to `[1 − b⁻ᵏ, 1)`. -/
theorem occursAt_replicate_max_iff (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n k : ℕ) :
    OccursAt b x (List.replicate k (b - 1)) n ↔
      orbit b x n ∈ Set.Ico (1 - 1 / (b : ℝ) ^ k) 1 := by
  rw [occursAt_iff_orbit_mem b hb x _
      (fun e he => by rw [List.eq_of_mem_replicate he]; omega) n,
    blockNatVal_replicate_max b k (by omega), List.length_replicate]
  have h1 : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
  have hcast : ((b ^ k - 1 : ℕ) : ℝ) = (b : ℝ) ^ k - 1 := by
    push_cast [h1]
    ring
  have hbpos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [hcast]
  have e1 : ((b : ℝ) ^ k - 1) / (b : ℝ) ^ k = 1 - 1 / (b : ℝ) ^ k := by
    field_simp
  have e2 : (((b : ℝ) ^ k - 1) + 1) / (b : ℝ) ^ k = 1 := by
    rw [sub_add_cancel]
    exact div_self hbpos.ne'
  rw [e1, e2]

/-! ### The packaged dichotomy -/

/-- **Abstract zero-run dichotomy**: if `x = s + tail` with the scaled tail
`bⁿ·(x − s)` trapped in `[lo, hi] ⊆ (b⁻ᵏ, 1]`, then a run of `k` zeros at
position `n` in base `b` forces the surrogate `fract (bⁿ·s)` into the top
sliver `[1 − hi, 1)`. -/
theorem top_sliver_of_zeroRun_tail {b : ℕ} (hb : 2 ≤ b) {x s : ℝ} {n k : ℕ}
    {lo hi : ℝ} (hlo : lo ≤ (b : ℝ) ^ n * (x - s))
    (hhi : (b : ℝ) ^ n * (x - s) ≤ hi)
    (hε : (1 : ℝ) / (b : ℝ) ^ k < lo)
    (h : OccursAt b x (List.replicate k 0) n) :
    1 - hi ≤ Int.fract ((b : ℝ) ^ n * s) := by
  rw [occursAt_replicate_zero_iff' b hb, orbit_eq_fract_add_tail b x s n] at h
  exact top_sliver_of_fract_small (Int.fract_nonneg _) hlo hhi hε h.2

/-- **Abstract max-run dichotomy**: same decomposition, `hi, b⁻ᵏ ≤ 1/2` —
a run of `k` top digits `b − 1` at position `n` forces the surrogate into
`[1 − hi − b⁻ᵏ, 1)`. -/
theorem top_sliver_of_maxRun_tail {b : ℕ} (hb : 2 ≤ b) {x s : ℝ} {n k : ℕ}
    {lo hi : ℝ} (hlo : lo ≤ (b : ℝ) ^ n * (x - s))
    (hhi : (b : ℝ) ^ n * (x - s) ≤ hi) (hhi2 : hi ≤ 1 / 2)
    (hε : (1 : ℝ) / (b : ℝ) ^ k < lo)
    (h : OccursAt b x (List.replicate k (b - 1)) n) :
    1 - hi - 1 / (b : ℝ) ^ k ≤ Int.fract ((b : ℝ) ^ n * s) := by
  rw [occursAt_replicate_max_iff b hb, orbit_eq_fract_add_tail b x s n] at h
  exact top_sliver_of_fract_large (Int.fract_nonneg _) (Int.fract_lt_one _)
    hlo hhi hhi2 hε h.1

/-! ### Sanity anchor: the ln-2 instance -/

/-- The frozen `lnTwoOrbit_top_sliver_of_zeroRun` conclusion re-derived from
the abstract core, confirming the abstraction subsumes the ln-2 case
(`lo = 1/(2(n+1))`, `hi = 1/(n+1)`). -/
example {n k : ℕ} (hk : 2 * ((n : ℝ) + 1) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n) :
    1 - 1 / ((n : ℝ) + 1) ≤ lnTwoOrbit n := by
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have htail : ((2 : ℕ) : ℝ) ^ n * (Real.log 2 - lnTwoPartial n)
      = 2 ^ n * lnTwoTail n := by
    rw [hcast, lnTwoTail]
  have hlo : 1 / (2 * ((n : ℝ) + 1)) ≤ ((2 : ℕ) : ℝ) ^ n * (Real.log 2 - lnTwoPartial n) := by
    rw [htail]; exact lnTwoTail_ge n
  have hhi : ((2 : ℕ) : ℝ) ^ n * (Real.log 2 - lnTwoPartial n) ≤ 1 / ((n : ℝ) + 1) := by
    rw [htail]; exact lnTwoTail_le n
  have hε : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ k < 1 / (2 * ((n : ℝ) + 1)) := by
    rw [hcast]
    exact one_div_lt_one_div_of_lt (by positivity) hk
  have hcore := top_sliver_of_zeroRun_tail (le_refl 2) hlo hhi hε h
  rw [lnTwoOrbit_eq_fract]
  rwa [hcast] at hcore

end NormalNumbers
