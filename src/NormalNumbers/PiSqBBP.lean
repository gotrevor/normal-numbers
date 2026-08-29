/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickedOrbit

/-!
# π² through a signed-kick machine (batch-2 target 2)

Lane-2 batch-2 target 2 (operator brief v2).  π² is BBP in base 16 —
Bailey, *A Compendium of BBP-Type Formulas for Mathematical Constants*
(2023-04-08), **Formula 29**:

  `π² = Σ_{k≥0} 16⁻ᵏ (16/(8k+1)² − 16/(8k+2)² − 8/(8k+3)² − 16/(8k+4)²
        − 4/(8k+5)² − 4/(8k+6)² + 2/(8k+7)²)`.

Probe: `experiments/pi_sq_bbp.py` (2026-08-29) — identity verified to 88
digits AND the block-sign fact confirmed: the per-digit block is positive
at `k = 0` and NEGATIVE for every `1 ≤ k < 30` (coefficient sum `−30`,
asymptotically `−30/(64k²)`).  So the nonneg-kick machine
(`top_sliver_of_zeroRun_kicked`) does NOT apply; this file builds the
honest SIGNED variant and instantiates it:

* **abstract signed layer** (mirrors the summed-kick machine of
  `KickedOrbit.lean`): a two-sided cap `|r m| ≤ A` for `m > n` gives the
  two-sided tail bracket `|bⁿ·(x − sₙ)| ≤ A/(b−1)`
  (`kicked_tail_abs_le`), and the run theorems are BOUNDARY-shaped, not
  top-sliver-shaped: a long run of zeros (or of top digits) pins the
  surrogate `fract (bⁿ·sₙ)` within `b⁻ᵏ + A/(b−1)` of the wrap point
  from EITHER side — `min (fract u, 1 − fract u)` is small
  (`boundary_of_zeroRun_kickedAbs` / `boundary_of_maxRun_kickedAbs`);
* **elementary signed kick bounds**: `|piSqKick j| ≤ 48/(8j+1)²` for
  `j ≥ 1` (`abs_piSqKick_le`).  The `j = 0` block (the only positive
  one, ≈ 9.88) is folded into the machine by the SHIFTED kick
  `piSqShiftKick m = 16·piSqKick (m−1)`, whose kicked series
  `Σ_{m≥1} piSqShiftKick m / 16^m = Σ_{j≥0} piSqKick j / 16^j` is
  exactly π² — this is why the draft surrogate
  `kickedPartial 16 piSqKick n` was unusable (it missed the j = 0 term)
  and the landed headline uses `kickedPartial 16 piSqShiftKick n`
  (= `Σ_{j<n} piSqKick j / 16^j`, the honest partial sum of Formula 29);
* **the headlines** `piSq_boundary_of_zeroRun` /
  `piSq_boundary_of_maxRun`, conditional on the frozen node `PiSqBBP`:
  for `n ≥ 1`, a length-`k` run of hex digit 0 (resp. 15) of π² at
  position `n` pins the surrogate within `16⁻ᵏ + 52/(8n+1)²` of the
  wrap point from either side — the window is quadratically thin in `n`
  (machine constant: `A = 768/(8n+1)²`, sliver `A/15 = 51.2/(8n+1)²`,
  stated as `52`).

The node statement `PiSqBBP` is FROZEN (probe-verified, CITED-class,
lane-2 discharge owed like `PiBBP` was); everything else here is proved.
-/

namespace NormalNumbers

/-- The signed per-digit block of Formula 29. -/
noncomputable def piSqKick (j : ℕ) : ℝ :=
  16 / (8 * (j : ℝ) + 1) ^ 2 - 16 / (8 * (j : ℝ) + 2) ^ 2
    - 8 / (8 * (j : ℝ) + 3) ^ 2 - 16 / (8 * (j : ℝ) + 4) ^ 2
    - 4 / (8 * (j : ℝ) + 5) ^ 2 - 4 / (8 * (j : ℝ) + 6) ^ 2
    + 2 / (8 * (j : ℝ) + 7) ^ 2

/-- The π² BBP summand: `16⁻ʲ · piSqKick j`. -/
noncomputable def piSqTerm (j : ℕ) : ℝ := (1 / 16 ^ j) * piSqKick j

/-- **Node (frozen, CITED-class): the π² BBP formula** — Bailey's
compendium (2023-04-08) Formula 29, presented in the original 1997 BBP
paper.  Probe-verified to 88 digits (`experiments/pi_sq_bbp.py`).
Lane-2 discharge owed, like `PiBBP` was. -/
def PiSqBBP : Prop := HasSum piSqTerm (Real.pi ^ 2)

/-! ### The signed-kick abstract layer

Signed analogue of the summed-kick machine in `KickedOrbit.lean`: the
kick sequence carries no sign information, only a magnitude cap, so the
tail bracket is two-sided and the run conclusion is a boundary event
(the surrogate is near the wrap point from one side or the other),
rather than a one-sided top-sliver ride. -/

/-- **Signed kicked tail cap**: kicks past `n` capped in magnitude by
`A` put the scaled tail within `A/(b−1)` of zero, two-sidedly. -/
theorem kicked_tail_abs_le {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ} {x A : ℝ} (n : ℕ)
    (hsum : HasSum (fun k : ℕ => r (k + 1) / (b : ℝ) ^ (k + 1)) x)
    (hcap : ∀ m, n + 1 ≤ m → |r m| ≤ A) :
    |(b : ℝ) ^ n * (x - kickedPartial b r n)| ≤ A / ((b : ℝ) - 1) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hinv0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hinv1 : (b : ℝ)⁻¹ < 1 := by
    rw [← one_div, div_lt_one hb0]
    linarith
  set f : ℕ → ℝ := fun k => r (k + 1) / (b : ℝ) ^ (k + 1) with hf
  have hsummable : Summable f := hsum.summable
  have key := hsummable.sum_add_tsum_nat_add n
  have htail : x - kickedPartial b r n = ∑' i : ℕ, f (i + n) := by
    have hx : x = ∑' i, f i := hsum.tsum_eq.symm
    rw [kickedPartial, hx, ← key]
    ring
  have hg : HasSum (fun i : ℕ => (A * (b : ℝ)⁻¹) * ((b : ℝ)⁻¹) ^ i)
      ((A * (b : ℝ)⁻¹) * (1 - (b : ℝ)⁻¹)⁻¹) :=
    (hasSum_geometric_of_lt_one hinv0 hinv1).mul_left _
  -- per-term norm comparison against the geometric series `(A·b⁻¹)·(b⁻¹)^i`
  have hle : ∀ i : ℕ, ‖(b : ℝ) ^ n * f (i + n)‖ ≤ (A * (b : ℝ)⁻¹) * ((b : ℝ)⁻¹) ^ i := by
    intro i
    have hsplit : (b : ℝ) ^ (i + n + 1) = (b : ℝ) ^ n * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have heq : (b : ℝ) ^ n * f (i + n) = r (i + n + 1) * ((b : ℝ) ^ (i + 1))⁻¹ := by
      show (b : ℝ) ^ n * (r (i + n + 1) / (b : ℝ) ^ (i + n + 1)) = _
      rw [hsplit]
      have hbn : ((b : ℝ) ^ n) ≠ 0 := by positivity
      have hbi : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
      field_simp
    have hgeq : (A * (b : ℝ)⁻¹) * ((b : ℝ)⁻¹) ^ i = A * ((b : ℝ) ^ (i + 1))⁻¹ := by
      rw [← inv_pow, pow_succ]
      ring
    rw [heq, hgeq, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((b : ℝ) ^ (i + 1))⁻¹)]
    exact mul_le_mul_of_nonneg_right (hcap _ (by omega)) (by positivity)
  have hbig : ‖∑' i : ℕ, (b : ℝ) ^ n * f (i + n)‖
      ≤ (A * (b : ℝ)⁻¹) * (1 - (b : ℝ)⁻¹)⁻¹ :=
    tsum_of_norm_bounded hg hle
  have hkey : (1 - (b : ℝ)⁻¹) * b = (b : ℝ) - 1 := by
    rw [sub_mul, one_mul, inv_mul_cancel₀ hb0.ne']
  have hfin : (A * (b : ℝ)⁻¹) * (1 - (b : ℝ)⁻¹)⁻¹ = A / ((b : ℝ) - 1) := by
    rw [← hkey, div_eq_mul_inv, mul_inv]
    ring
  rw [htail]
  calc |(b : ℝ) ^ n * ∑' i : ℕ, f (i + n)|
      = ‖∑' i : ℕ, (b : ℝ) ^ n * f (i + n)‖ := by
        rw [tsum_mul_left, Real.norm_eq_abs]
    _ ≤ (A * (b : ℝ)⁻¹) * (1 - (b : ℝ)⁻¹)⁻¹ := hbig
    _ = A / ((b : ℝ) - 1) := hfin

/-- **Boundary core, zero side**: if the perturbed point `u + τ` has
fractional part below `ε` and the perturbation is only known two-sidedly
(`|τ| ≤ D`), then `u` is within `ε + D` of the wrap point from one side
or the other: `min u (1 − u) ≤ ε + D`. -/
theorem boundary_of_fract_lt {u τ D ε : ℝ}
    (hτ : |τ| ≤ D) (hfr : Int.fract (u + τ) < ε) :
    min u (1 - u) ≤ ε + D := by
  obtain ⟨hτlo, hτhi⟩ := abs_le.mp hτ
  have hε0 : 0 < ε := lt_of_le_of_lt (Int.fract_nonneg _) hfr
  rcases lt_or_ge (u + τ) 0 with hneg | hpos
  · exact le_trans (min_le_left _ _) (by linarith)
  rcases lt_or_ge (u + τ) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨hpos, hlt⟩] at hfr
    exact le_trans (min_le_left _ _) (by linarith)
  · exact le_trans (min_le_right _ _) (by linarith)

/-- **Boundary core, max side**: if the perturbed point `u + τ` has
fractional part within `ε` of `1` and `|τ| ≤ D`, then again
`min u (1 − u) ≤ ε + D`. -/
theorem boundary_of_fract_ge {u τ D ε : ℝ}
    (hτ : |τ| ≤ D) (hfr : 1 - ε ≤ Int.fract (u + τ)) :
    min u (1 - u) ≤ ε + D := by
  obtain ⟨hτlo, hτhi⟩ := abs_le.mp hτ
  have hε0 : 0 < ε := by
    have := Int.fract_lt_one (u + τ)
    linarith
  rcases lt_or_ge (u + τ) 0 with hneg | hpos
  · exact le_trans (min_le_left _ _) (by linarith)
  rcases lt_or_ge (u + τ) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨hpos, hlt⟩] at hfr
    exact le_trans (min_le_right _ _) (by linarith)
  · exact le_trans (min_le_right _ _) (by linarith)

/-- **The signed machine, zero-run side**: for a constant
`x = Σ_{k≥1} r(k)/bᵏ` with kicks past `n` capped in magnitude by `A`, a
run of `k` zeros at position `n` pins the surrogate
`fract (bⁿ·(partial sum))` within `b⁻ᵏ + A/(b−1)` of the wrap point from
one side or the other. -/
theorem boundary_of_zeroRun_kickedAbs {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    {x A : ℝ} {n k : ℕ}
    (hsum : HasSum (fun m : ℕ => r (m + 1) / (b : ℝ) ^ (m + 1)) x)
    (hcap : ∀ m, n + 1 ≤ m → |r m| ≤ A)
    (h : OccursAt b x (List.replicate k 0) n) :
    min (Int.fract ((b : ℝ) ^ n * kickedPartial b r n))
        (1 - Int.fract ((b : ℝ) ^ n * kickedPartial b r n))
      ≤ 1 / (b : ℝ) ^ k + A / ((b : ℝ) - 1) := by
  rw [occursAt_replicate_zero_iff' b hb,
    orbit_eq_fract_add_tail b x (kickedPartial b r n) n] at h
  exact boundary_of_fract_lt (kicked_tail_abs_le hb n hsum hcap) h.2

/-- **The signed machine, max-run side**: same data, for a run of `k`
top digits `b − 1`. -/
theorem boundary_of_maxRun_kickedAbs {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    {x A : ℝ} {n k : ℕ}
    (hsum : HasSum (fun m : ℕ => r (m + 1) / (b : ℝ) ^ (m + 1)) x)
    (hcap : ∀ m, n + 1 ≤ m → |r m| ≤ A)
    (h : OccursAt b x (List.replicate k (b - 1)) n) :
    min (Int.fract ((b : ℝ) ^ n * kickedPartial b r n))
        (1 - Int.fract ((b : ℝ) ^ n * kickedPartial b r n))
      ≤ 1 / (b : ℝ) ^ k + A / ((b : ℝ) - 1) := by
  rw [occursAt_replicate_max_iff b hb,
    orbit_eq_fract_add_tail b x (kickedPartial b r n) n] at h
  exact boundary_of_fract_ge (kicked_tail_abs_le hb n hsum hcap) h.1

/-! ### The π² instance -/

/-- The shifted π² kick: `piSqShiftKick m = 16·piSqKick (m−1)`, so that
the kicked series `Σ_{m≥1} piSqShiftKick m / 16^m` starts at the `j = 0`
block of Formula 29 and sums to π² exactly. -/
noncomputable def piSqShiftKick (m : ℕ) : ℝ := 16 * piSqKick (m - 1)

/-- The kicked-series form of the frozen node: `PiSqBBP` says exactly
that the shifted kick series sums to π². -/
theorem hasSum_piSqShiftKick (hπ : PiSqBBP) :
    HasSum (fun m : ℕ => piSqShiftKick (m + 1) / ((16 : ℕ) : ℝ) ^ (m + 1))
      (Real.pi ^ 2) := by
  have hfun : (fun m : ℕ => piSqShiftKick (m + 1) / ((16 : ℕ) : ℝ) ^ (m + 1))
      = piSqTerm := by
    funext m
    simp only [piSqShiftKick, piSqTerm, Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    have h16 : ((16 : ℝ) ^ m) ≠ 0 := by positivity
    field_simp
  rw [hfun]
  exact hπ

/-- **Elementary signed kick bound**: for `j ≥ 1` every denominator of
`piSqKick j` is at least `8j+1`, the positive coefficients sum to 18 and
the negative ones to 48, so `|piSqKick j| ≤ 48/(8j+1)²`. -/
theorem abs_piSqKick_le {j : ℕ} (hj : 1 ≤ j) :
    |piSqKick j| ≤ 48 / (8 * (j : ℝ) + 1) ^ 2 := by
  have hy : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h1 : (0 : ℝ) < 8 * (j : ℝ) + 1 := by linarith
  have hu : (0 : ℝ) ≤ 1 / (8 * (j : ℝ) + 1) ^ 2 := by positivity
  -- all comparisons as multiples of the single atom `1/(8j+1)²`, so
  -- `linarith` can combine them
  have c2 : 16 / (8 * (j : ℝ) + 2) ^ 2 ≤ 16 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
    gcongr
    linarith
  have c3 : 8 / (8 * (j : ℝ) + 3) ^ 2 ≤ 8 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
    gcongr
    linarith
  have c4 : 16 / (8 * (j : ℝ) + 4) ^ 2 ≤ 16 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
    gcongr
    linarith
  have c5 : 4 / (8 * (j : ℝ) + 5) ^ 2 ≤ 4 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
    gcongr
    linarith
  have c6 : 4 / (8 * (j : ℝ) + 6) ^ 2 ≤ 4 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
    gcongr
    linarith
  have c7 : 2 / (8 * (j : ℝ) + 7) ^ 2 ≤ 2 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
    gcongr
    linarith
  have p7 : (0 : ℝ) ≤ 2 / (8 * (j : ℝ) + 7) ^ 2 := by positivity
  have n2 : (0 : ℝ) ≤ 16 / (8 * (j : ℝ) + 2) ^ 2 := by positivity
  have n3 : (0 : ℝ) ≤ 8 / (8 * (j : ℝ) + 3) ^ 2 := by positivity
  have n4 : (0 : ℝ) ≤ 16 / (8 * (j : ℝ) + 4) ^ 2 := by positivity
  have n5 : (0 : ℝ) ≤ 4 / (8 * (j : ℝ) + 5) ^ 2 := by positivity
  have n6 : (0 : ℝ) ≤ 4 / (8 * (j : ℝ) + 6) ^ 2 := by positivity
  have e16 : 16 / (8 * (j : ℝ) + 1) ^ 2 = 16 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
  have e48 : 48 / (8 * (j : ℝ) + 1) ^ 2 = 48 * (1 / (8 * (j : ℝ) + 1) ^ 2) := by
    rw [mul_one_div]
  rw [abs_le, piSqKick, e16, e48]
  constructor
  · linarith
  · linarith

/-- Magnitude cap for the shifted kick past position `n ≥ 1`:
`|piSqShiftKick m| ≤ 768/(8n+1)²` for every `m ≥ n+1`. -/
theorem abs_piSqShiftKick_le {n m : ℕ} (hn : 1 ≤ n) (hm : n + 1 ≤ m) :
    |piSqShiftKick m| ≤ 768 / (8 * (n : ℝ) + 1) ^ 2 := by
  have hm1 : 1 ≤ m - 1 := by omega
  have hb := abs_piSqKick_le hm1
  have hmn : (n : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    have : n ≤ m - 1 := by omega
    exact_mod_cast this
  have hstep : 48 / (8 * ((m - 1 : ℕ) : ℝ) + 1) ^ 2
      ≤ 48 / (8 * (n : ℝ) + 1) ^ 2 := by
    gcongr
  rw [piSqShiftKick, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
  calc 16 * |piSqKick (m - 1)|
      ≤ 16 * (48 / (8 * ((m - 1 : ℕ) : ℝ) + 1) ^ 2) := by linarith
    _ ≤ 16 * (48 / (8 * (n : ℝ) + 1) ^ 2) := by linarith
    _ = 768 / (8 * (n : ℝ) + 1) ^ 2 := by ring

/-- **Headline, zero-run side**: conditional on the frozen node, a
length-`k` run of hex digit 0 of π² at position `n ≥ 1` pins the BBP
surrogate `fract (16ⁿ · Σ_{j<n} piSqKick j / 16ʲ)` within
`16⁻ᵏ + 52/(8n+1)²` of the wrap point from one side or the other:
boundary forcing with a quadratically thin window. -/
theorem piSq_boundary_of_zeroRun (hπ : PiSqBBP) {n k : ℕ} (hn : 1 ≤ n)
    (h : OccursAt 16 (Real.pi ^ 2) (List.replicate k 0) n) :
    min (Int.fract ((16 : ℝ) ^ n * kickedPartial 16 piSqShiftKick n))
        (1 - Int.fract ((16 : ℝ) ^ n * kickedPartial 16 piSqShiftKick n))
      ≤ 1 / 16 ^ k + 52 / (8 * (n : ℝ) + 1) ^ 2 := by
  have hcast : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
  have hcore := boundary_of_zeroRun_kickedAbs (b := 16) (by norm_num)
    (hasSum_piSqShiftKick hπ) (fun m hm => abs_piSqShiftKick_le hn hm) h
  rw [hcast] at hcore
  have hbound : 768 / (8 * (n : ℝ) + 1) ^ 2 / ((16 : ℝ) - 1)
      ≤ 52 / (8 * (n : ℝ) + 1) ^ 2 := by
    have heq : 768 / (8 * (n : ℝ) + 1) ^ 2 / ((16 : ℝ) - 1)
        = (768 / 15) / (8 * (n : ℝ) + 1) ^ 2 := by ring
    rw [heq]
    gcongr
    norm_num
  linarith

/-- **Headline, max-run side**: same conclusion for a length-`k` run of
the top hex digit 15. -/
theorem piSq_boundary_of_maxRun (hπ : PiSqBBP) {n k : ℕ} (hn : 1 ≤ n)
    (h : OccursAt 16 (Real.pi ^ 2) (List.replicate k 15) n) :
    min (Int.fract ((16 : ℝ) ^ n * kickedPartial 16 piSqShiftKick n))
        (1 - Int.fract ((16 : ℝ) ^ n * kickedPartial 16 piSqShiftKick n))
      ≤ 1 / 16 ^ k + 52 / (8 * (n : ℝ) + 1) ^ 2 := by
  have hcast : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
  have hcore := boundary_of_maxRun_kickedAbs (b := 16) (by norm_num)
    (hasSum_piSqShiftKick hπ) (fun m hm => abs_piSqShiftKick_le hn hm)
    (by simpa using h)
  rw [hcast] at hcore
  have hbound : 768 / (8 * (n : ℝ) + 1) ^ 2 / ((16 : ℝ) - 1)
      ≤ 52 / (8 * (n : ℝ) + 1) ^ 2 := by
    have heq : 768 / (8 * (n : ℝ) + 1) ^ 2 / ((16 : ℝ) - 1)
        = (768 / 15) / (8 * (n : ℝ) + 1) ^ 2 := by ring
    rw [heq]
    gcongr
    norm_num
  linarith

end NormalNumbers
