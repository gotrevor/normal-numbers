/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import NormalNumbers.LnTwoRuns

/-!
# True vs surrogate digits of `ln 2` (the Lagarias footnote-1 problem)

Lagarias 2001 (*On the normality of arithmetical constants*, footnote 1)
asks whether the true binary digits of `ln 2` and the digits read off the
Bailey–Crandall surrogate orbit `x_{n+1} = fract (2·x_n + 1/(n+1))` agree
at density one.  This file settles the *pointwise mechanism* of that
question from the tail bracket `orbit_log_two_eq`
(`τ_n ∈ [1/(2(n+1)), 1/(n+1)]`), and wires it to the repo's separation
and equidistribution interfaces:

* **Window forcing** (`lnTwoOrbit_window_of_digit_mismatch`, sorry-free,
  unconditional): a digit disagreement at position `n` forces the
  surrogate into the boundary window
  `[1/2 − 1/(n+1), 1/2) ∪ [1 − 1/(n+1), 1)` — total width `≤ 2/(n+1)`.
  Probe (`experiments/lntwo_digit_agreement.py`, 2026-08-29, 200 000
  positions, exact fixed-point arithmetic): 18 disagreements total,
  every one inside the predicted window, cumulative count tracking
  `2·ln N` at ratio 0.7–0.9 — the random-like log rate.
* **Costume identification** (`lnTwoNorm_small_of_digit_mismatch`): the
  mismatch event COLLAPSES onto the dyadic separation family — a
  disagreement at `n` means `‖2ⁿ·ln 2‖ < 1/(n+1)` (wraparound) or
  `‖2ⁿ⁺¹·ln 2‖ < 2/(n+1)` (boundary straddle).  Same finding shape as
  the lattice re-coordinatization (`LnTwoLattice.lean`): the footnote-1
  problem for `ln 2` is not a new wall, it is the separation wall in a
  density costume.
* **Separation edge** (`eventually_digit_agree_of_polySep`): under
  `LnTwoPolySep C` with `C < 1` the disagreement set is FINITE — the
  Tier-2-minus hypothesis settles footnote 1 for `ln 2` in a form far
  stronger than the density-one asked for.  (Tier 1 / `LnTwoExpSep` is
  too weak: its windows shrink exponentially, the mismatch windows only
  like `1/n`.)
* **Equidistribution edge**
  (`lnTwoMismatchCount_density_zero_of_equidistributed`): under the
  ladder's base hypothesis `Equidistributed lnTwoOrbit`, disagreements
  have density zero — the conditional density-one agreement.

Per Lagarias's own acid test the unconditional content stays at the
forcing level: the kick floor yields "disagreement ⇒ boundary event",
never a growth/density conclusion by itself.
-/

namespace NormalNumbers

open Filter Set

/-! ### The surrogate digit and the single-digit bridge -/

/-- The digit the Bailey–Crandall surrogate predicts at position `n`:
the leading binary digit of `x_n`. -/
noncomputable def lnTwoSurrogateDigit (n : ℕ) : ℕ :=
  if lnTwoOrbit n < 1 / 2 then 0 else 1

theorem lnTwoSurrogateDigit_eq_zero_iff (n : ℕ) :
    lnTwoSurrogateDigit n = 0 ↔ lnTwoOrbit n < 1 / 2 := by
  unfold lnTwoSurrogateDigit
  split <;> simp_all

/-- `ln 2` is its own fractional part. -/
theorem fract_log_two : Int.fract (Real.log 2) = Real.log 2 := by
  refine Int.fract_eq_self.mpr ⟨Real.log_nonneg one_le_two, ?_⟩
  have := Real.log_two_lt_d9
  linarith

/-- **Single-digit bridge**: the true digit of `ln 2` at position `n` is
`0` exactly when the doubling orbit sits in the bottom half. -/
theorem digitOf_log_two_eq_zero_iff (n : ℕ) :
    digitOf 2 (Real.log 2) n = 0 ↔ orbit 2 (Real.log 2) n < 1 / 2 := by
  have hiff := occursAt_replicate_zero_iff (Real.log 2) n 1
  constructor
  · intro hd
    have hocc : OccursAt 2 (Real.log 2) (List.replicate 1 0) n := by
      intro j hj
      have hj0 : j = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hj)
      subst hj0
      simpa [fract_log_two] using hd
    have := (hiff.mp hocc).2
    simpa using this
  · intro ho
    have horb := orbit_mem_Ico 2 (Real.log 2) n
    have hocc : OccursAt 2 (Real.log 2) (List.replicate 1 0) n :=
      hiff.mpr ⟨horb.1, by simpa using ho⟩
    have := hocc 0 (by simp)
    simpa [fract_log_two] using this

theorem digitOf_lt_two (x : ℝ) (i : ℕ) : digitOf 2 x i < 2 :=
  Nat.mod_lt _ (by norm_num)

/-- Digit disagreement, characterized on the two orbits: the true orbit
and the surrogate sit on opposite sides of `1/2`. -/
theorem digit_mismatch_iff (n : ℕ) :
    digitOf 2 (Real.log 2) n ≠ lnTwoSurrogateDigit n ↔
      ¬ (orbit 2 (Real.log 2) n < 1 / 2 ↔ lnTwoOrbit n < 1 / 2) := by
  have hbridge := digitOf_log_two_eq_zero_iff n
  have hsur := lnTwoSurrogateDigit_eq_zero_iff n
  have hd2 := digitOf_lt_two (Real.log 2) n
  have hs2 : lnTwoSurrogateDigit n < 2 := by
    unfold lnTwoSurrogateDigit; split <;> norm_num
  constructor
  · intro hne hcong
    apply hne
    have h00 : digitOf 2 (Real.log 2) n = 0 ↔ lnTwoSurrogateDigit n = 0 := by
      rw [hbridge, hsur]; exact hcong
    have hd : digitOf 2 (Real.log 2) n = 0 ∨ digitOf 2 (Real.log 2) n = 1 := by omega
    have hs : lnTwoSurrogateDigit n = 0 ∨ lnTwoSurrogateDigit n = 1 := by omega
    rcases hd with hd | hd <;> rcases hs with hs | hs
    · rw [hd, hs]
    · exfalso; rw [hd, hs] at h00; simp at h00
    · exfalso; rw [hd, hs] at h00; simp at h00
    · rw [hd, hs]
  · intro hncong heq
    apply hncong
    rw [← hbridge, ← hsur, heq]

/-! ### The unconditional window forcing (the frozen node) -/

/-- **Window forcing** (unconditional, the footnote-1 mechanism): a digit
disagreement at position `n` forces the surrogate into the boundary
window — within `1/(n+1)` below the digit boundary `1/2`, or within
`1/(n+1)` below the wrap point `1`. -/
theorem lnTwoOrbit_window_of_digit_mismatch {n : ℕ}
    (h : digitOf 2 (Real.log 2) n ≠ lnTwoSurrogateDigit n) :
    (1 / 2 - 1 / ((n : ℝ) + 1) ≤ lnTwoOrbit n ∧ lnTwoOrbit n < 1 / 2) ∨
      1 - 1 / ((n : ℝ) + 1) ≤ lnTwoOrbit n := by
  rw [digit_mismatch_iff] at h
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hx01 := lnTwoOrbit_mem_Ico n
  have horb : orbit 2 (Real.log 2) n = Int.fract (x + τ) := orbit_log_two_eq n
  rcases lt_or_ge (x + τ) 1 with hlt | hge
  · -- no wraparound: orbit = x + τ ≥ x, so a mismatch is a straddle
    have hfr : orbit 2 (Real.log 2) n = x + τ := by
      rw [horb, Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩]
    rcases lt_or_ge x (1 / 2) with hxlt | hxge
    · -- x below half; mismatch forces the orbit at or above half
      have hoge : ¬ orbit 2 (Real.log 2) n < 1 / 2 := fun hol => h ⟨fun _ => hxlt, fun _ => hol⟩
      push_neg at hoge
      exact Or.inl ⟨by rw [hfr] at hoge; linarith, hxlt⟩
    · -- x at or above half and no wrap: orbit ≥ x ≥ 1/2, no mismatch possible
      exfalso
      exact h ⟨fun hol => by rw [hfr] at hol; linarith, fun hxl => absurd hxl (not_lt.mpr hxge)⟩
  · -- wraparound: x ≥ 1 − τ ≥ 1 − 1/(n+1), the top window outright
    exact Or.inr (by linarith)

/-! ### The costume identification: mismatch = small dyadic norm -/

private lemma orbit_two_succ (x : ℝ) (n : ℕ) :
    orbit 2 x (n + 1) = Int.fract (2 * orbit 2 x n) := by
  unfold orbit
  have hsplit : x * ((2 : ℕ) : ℝ) ^ (n + 1)
      = 2 * Int.fract (x * ((2 : ℕ) : ℝ) ^ n) + ((2 * ⌊x * ((2 : ℕ) : ℝ) ^ n⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hsplit, Int.fract_add_intCast]

/-- **Costume identification**: a digit disagreement at `n` is a small
dyadic norm in disguise — `‖2ⁿ·ln 2‖ < 1/(n+1)` (the wraparound case) or
`‖2ⁿ⁺¹·ln 2‖ < 2/(n+1)` (the straddle case, pushed one step by the
doubling).  The footnote-1 event collapses onto the separation family. -/
theorem lnTwoNorm_small_of_digit_mismatch {n : ℕ}
    (h : digitOf 2 (Real.log 2) n ≠ lnTwoSurrogateDigit n) :
    lnTwoNorm n < 1 / ((n : ℝ) + 1) ∨ lnTwoNorm (n + 1) < 2 / ((n : ℝ) + 1) := by
  rw [digit_mismatch_iff] at h
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hx01 := lnTwoOrbit_mem_Ico n
  have horb : orbit 2 (Real.log 2) n = Int.fract (x + τ) := orbit_log_two_eq n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rcases lt_or_ge (x + τ) 1 with hlt | hge
  · -- no wraparound: mismatch is a straddle, orbit_n ∈ [1/2, 1/2 + τ)
    have hfr : orbit 2 (Real.log 2) n = x + τ := by
      rw [horb, Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩]
    rcases lt_or_ge x (1 / 2) with hxlt | hxge
    · have hoge : ¬ orbit 2 (Real.log 2) n < 1 / 2 := fun hol => h ⟨fun _ => hxlt, fun _ => hol⟩
      push_neg at hoge
      rw [hfr] at hoge
      -- orbit_{n+1} = fract (2(x+τ)) with 2(x+τ) ∈ [1, 1 + 2τ), so it equals 2(x+τ) − 1 < 2τ
      right
      have h2lt : 2 * (x + τ) - 1 < 1 := by linarith
      have h2ge : 0 ≤ 2 * (x + τ) - 1 := by linarith
      have hnext : orbit 2 (Real.log 2) (n + 1) = 2 * (x + τ) - 1 := by
        rw [orbit_two_succ, hfr]
        have : 2 * (x + τ) = 2 * (x + τ) - 1 + ((1 : ℤ) : ℝ) := by push_cast; ring
        rw [this, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨h2ge, h2lt⟩]
        push_cast
        ring
      have hnorm : lnTwoNorm (n + 1) ≤ 2 * (x + τ) - 1 := by
        rw [lnTwoNorm, hnext]; exact min_le_left _ _
      have : 2 * (x + τ) - 1 < 2 * τ := by linarith
      have hτ2 : 2 * τ ≤ 2 / ((n : ℝ) + 1) := by
        rw [div_eq_mul_one_div 2]
        linarith
      linarith
    · exfalso
      exact h ⟨fun hol => by rw [hfr] at hol; linarith, fun hxl => absurd hxl (not_lt.mpr hxge)⟩
  · -- wraparound: orbit_n = x + τ − 1 ∈ [0, τ) — the dyadic norm at n is tiny
    left
    have hlt2 : x + τ - 1 < 1 := by
      have hq : τ ≤ 1 := hτle.trans (by
        rw [div_le_one hn1]
        linarith [Nat.cast_nonneg (α := ℝ) n])
      linarith [hx01.2]
    have hfr : orbit 2 (Real.log 2) n = x + τ - 1 := by
      have hshift : x + τ - 1 + ((1 : ℤ) : ℝ) = x + τ := by push_cast; ring
      rw [horb, ← hshift, Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, hlt2⟩]
      push_cast
      ring
    have hnorm : lnTwoNorm n ≤ x + τ - 1 := by
      rw [lnTwoNorm, hfr]; exact min_le_left _ _
    have : x + τ - 1 < τ := by linarith [hx01.2]
    calc lnTwoNorm n ≤ x + τ - 1 := hnorm
      _ < τ := this
      _ ≤ 1 / ((n : ℝ) + 1) := hτle

/-! ### The separation edge: `LnTwoPolySep C`, `C < 1`, leaves only
finitely many disagreements -/

/-- **Separation edge**: polynomial dyadic separation with exponent
`C < 1` settles Lagarias footnote 1 for `ln 2` in the strong form — the
true and surrogate digits agree at all but finitely many positions.
(The mismatch windows shrink like `1/n`; separation `(n+2)^{−C}` with
`C < 1` eventually clears them.) -/
theorem eventually_digit_agree_of_polySep {C : ℝ} {N₀ : ℕ} (hC : C < 1)
    (hsep : LnTwoPolySep C N₀) :
    ∀ᶠ n in atTop, digitOf 2 (Real.log 2) n = lnTwoSurrogateDigit n := by
  -- eventually `(n+2)^(1−C) ≥ 6` and `(n+3)^(1−C) ≥ 6`
  have hpow : Tendsto (fun y : ℝ => y ^ (1 - C)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hcast2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hcast3 : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
  have h6 : ∀ᶠ n : ℕ in atTop,
      6 ≤ ((n : ℝ) + 2) ^ (1 - C) ∧ 6 ≤ ((n : ℝ) + 3) ^ (1 - C) :=
    ((hpow.comp hcast2).eventually_ge_atTop 6).and
      ((hpow.comp hcast3).eventually_ge_atTop 6)
  filter_upwards [h6, eventually_ge_atTop N₀,
    eventually_ge_atTop (N₀ + 1)] with n h6n hnN hnN1
  by_contra hne
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  rcases lnTwoNorm_small_of_digit_mismatch hne with hsm | hsm
  · -- `‖2ⁿ·ln 2‖ < 1/(n+1)` against separation `(n+2)^{−C}`
    have hlow : ((n : ℝ) + 2) ^ (-C) ≤ lnTwoNorm n := hsep n hnN
    have hsplit : ((n : ℝ) + 2) ^ (1 - C)
        = ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ (-C) := by
      rw [show (1 : ℝ) - C = 1 + -C by ring, Real.rpow_add hn2,
        Real.rpow_one]
    rw [hsplit] at h6n
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 2) ^ (-C) := Real.rpow_nonneg hn2.le _
    -- from 6 ≤ (n+2)·t : (n+1)·t ≥ 1, contradicting t ≤ norm < 1/(n+1)
    have hmul : lnTwoNorm n * ((n : ℝ) + 1) < 1 :=
      (lt_div_iff₀ hn1).mp hsm
    nlinarith [h6n.1, hlow, hmul, hpos, Nat.cast_nonneg (α := ℝ) n]
  · -- `‖2ⁿ⁺¹·ln 2‖ < 2/(n+1)` against separation `(n+3)^{−C}`
    have hlow : ((n : ℝ) + 3) ^ (-C) ≤ lnTwoNorm (n + 1) := by
      have hs := hsep (n + 1) (by omega)
      push_cast at hs
      have e : ((n : ℝ) + 1 + 2 : ℝ) = (n : ℝ) + 3 := by ring
      rw [e] at hs
      exact hs
    have hsplit : ((n : ℝ) + 3) ^ (1 - C)
        = ((n : ℝ) + 3) * ((n : ℝ) + 3) ^ (-C) := by
      rw [show (1 : ℝ) - C = 1 + -C by ring, Real.rpow_add hn3,
        Real.rpow_one]
    rw [hsplit] at h6n
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 3) ^ (-C) := Real.rpow_nonneg hn3.le _
    have hmul : lnTwoNorm (n + 1) * ((n : ℝ) + 1) < 2 :=
      (lt_div_iff₀ hn1).mp hsm
    nlinarith [h6n.2, hlow, hmul, hpos, Nat.cast_nonneg (α := ℝ) n]

/-! ### The equidistribution edge: conditional density-one agreement -/

open Classical in
/-- Disagreements between the true and surrogate digits among the first
`N` positions. -/
noncomputable def lnTwoMismatchCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n =>
    digitOf 2 (Real.log 2) n ≠ lnTwoSurrogateDigit n).card

open Classical in
private lemma lnTwoMismatchCount_le (M N : ℕ) (hM : 1 ≤ M) :
    lnTwoMismatchCount N
      ≤ M + visitCount lnTwoOrbit (1 / 2 - 1 / (M : ℝ)) (1 / 2) N
          + visitCount lnTwoOrbit (1 - 1 / (M : ℝ)) 1 N := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsub : ((Finset.range N).filter fun n =>
        digitOf 2 (Real.log 2) n ≠ lnTwoSurrogateDigit n)
      ⊆ Finset.range M
        ∪ ((Finset.range N).filter fun k => lnTwoOrbit k ∈ Set.Ico (1 / 2 - 1 / (M : ℝ)) (1 / 2))
        ∪ ((Finset.range N).filter fun k => lnTwoOrbit k ∈ Set.Ico (1 - 1 / (M : ℝ)) 1) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnN, hmis⟩ := hn
    rcases lt_or_ge n M with hnM | hnM
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hnM))
    · -- n ≥ M: the forcing window at n sits inside the fixed 1/M window
      have hwin : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / (M : ℝ) := by
        apply one_div_le_one_div_of_le hM0
        have : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM
        linarith
      have hx01 := lnTwoOrbit_mem_Ico n
      rcases lnTwoOrbit_window_of_digit_mismatch hmis with ⟨hlo, hhi⟩ | htop
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [Finset.mem_filter]
        exact ⟨hnN, ⟨by linarith, hhi⟩⟩
      · refine Finset.mem_union_right _ ?_
        rw [Finset.mem_filter]
        exact ⟨hnN, ⟨by linarith, hx01.2⟩⟩
  calc lnTwoMismatchCount N
      ≤ (Finset.range M
          ∪ ((Finset.range N).filter fun k => lnTwoOrbit k ∈ Set.Ico (1 / 2 - 1 / (M : ℝ)) (1 / 2))
          ∪ ((Finset.range N).filter fun k => lnTwoOrbit k ∈ Set.Ico (1 - 1 / (M : ℝ)) 1)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range M
          ∪ ((Finset.range N).filter fun k => lnTwoOrbit k ∈ Set.Ico (1 / 2 - 1 / (M : ℝ)) (1 / 2))).card
        + ((Finset.range N).filter fun k => lnTwoOrbit k ∈ Set.Ico (1 - 1 / (M : ℝ)) 1).card :=
        Finset.card_union_le _ _
    _ ≤ M + visitCount lnTwoOrbit (1 / 2 - 1 / (M : ℝ)) (1 / 2) N
        + visitCount lnTwoOrbit (1 - 1 / (M : ℝ)) 1 N := by
        have h1 := Finset.card_union_le (Finset.range M)
          ((Finset.range N).filter fun k => lnTwoOrbit k ∈ Set.Ico (1 / 2 - 1 / (M : ℝ)) (1 / 2))
        rw [Finset.card_range] at h1
        unfold visitCount
        omega

/-- **Equidistribution edge**: under the ladder's base hypothesis
`Equidistributed lnTwoOrbit`, the true and surrogate digits of `ln 2`
agree at density one (the disagreement count is `o(N)`) — the
conditional answer to Lagarias footnote 1 for `ln 2`. -/
theorem lnTwoMismatchCount_density_zero_of_equidistributed
    (h : Equidistributed lnTwoOrbit) :
    Tendsto (fun N => (lnTwoMismatchCount N : ℝ) / N) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- fixed window scale 1/M with 1/M < ε/8 (and M ≥ 2 for the interval bounds)
  obtain ⟨M, hMgt⟩ := exists_nat_gt (max (8 / ε) 2)
  have hM2 : 2 ≤ M := by
    have := (le_max_right (8 / ε) 2).trans_lt hMgt
    exact_mod_cast this.le
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    linarith
  have hMε : 1 / (M : ℝ) < ε / 8 := by
    have h8 : 8 / ε < (M : ℝ) := (le_max_left (8 / ε) 2).trans_lt hMgt
    rw [div_lt_div_iff₀ hM0 (by norm_num : (0 : ℝ) < 8)]
    have := (div_lt_iff₀ hε).mp h8
    linarith
  have hMhalf : 1 / (M : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast hM2
  -- the two window frequencies tend to 1/M each
  have h1 := h (1 / 2 - 1 / (M : ℝ)) (1 / 2) (by linarith) (by
      have : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      linarith) (by norm_num)
  have h2 := h (1 - 1 / (M : ℝ)) 1 (by linarith) (by
      have : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      linarith) le_rfl
  rw [show (1 : ℝ) / 2 - (1 / 2 - 1 / (M : ℝ)) = 1 / (M : ℝ) by ring] at h1
  rw [show (1 : ℝ) - (1 - 1 / (M : ℝ)) = 1 / (M : ℝ) by ring] at h2
  have hev1 := Metric.tendsto_atTop.mp h1 (ε / 8) (by positivity)
  have hev2 := Metric.tendsto_atTop.mp h2 (ε / 8) (by positivity)
  obtain ⟨N₁, hN₁⟩ := hev1
  obtain ⟨N₂, hN₂⟩ := hev2
  -- M/N eventually below ε/4
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp
    (tendsto_const_div_atTop_nhds_zero_nat (M : ℝ)) (ε / 4) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN => ?_⟩
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) ((le_max_left _ _).trans hN)
  have hNN₂ : N₂ ≤ N := le_trans (le_max_right _ _) ((le_max_left _ _).trans hN)
  have hNN₃ : N₃ ≤ N := le_trans (le_max_left _ _) ((le_max_right _ _).trans hN)
  have hN1' : 1 ≤ N := le_trans (le_max_right _ _) ((le_max_right _ _).trans hN)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1'
  -- unpack the three eventual bounds
  have hv1 : (visitCount lnTwoOrbit (1 / 2 - 1 / (M : ℝ)) (1 / 2) N : ℝ) / N
      < 1 / (M : ℝ) + ε / 8 := by
    have := hN₁ N hNN₁
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hv2 : (visitCount lnTwoOrbit (1 - 1 / (M : ℝ)) 1 N : ℝ) / N
      < 1 / (M : ℝ) + ε / 8 := by
    have := hN₂ N hNN₂
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hv3 : (M : ℝ) / N < ε / 4 := by
    have := hN₃ N hNN₃
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  -- assemble
  have hcount := lnTwoMismatchCount_le M N (by omega)
  have hcast : (lnTwoMismatchCount N : ℝ)
      ≤ (M : ℝ) + (visitCount lnTwoOrbit (1 / 2 - 1 / (M : ℝ)) (1 / 2) N : ℝ)
        + (visitCount lnTwoOrbit (1 - 1 / (M : ℝ)) 1 N : ℝ) := by
    exact_mod_cast hcount
  have hdiv : (lnTwoMismatchCount N : ℝ) / N
      ≤ (M : ℝ) / N
        + (visitCount lnTwoOrbit (1 / 2 - 1 / (M : ℝ)) (1 / 2) N : ℝ) / N
        + (visitCount lnTwoOrbit (1 - 1 / (M : ℝ)) 1 N : ℝ) / N := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hcast hN0.le
  have hnonneg : (0 : ℝ) ≤ (lnTwoMismatchCount N : ℝ) / N := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  calc (lnTwoMismatchCount N : ℝ) / N
      ≤ (M : ℝ) / N
        + (visitCount lnTwoOrbit (1 / 2 - 1 / (M : ℝ)) (1 / 2) N : ℝ) / N
        + (visitCount lnTwoOrbit (1 - 1 / (M : ℝ)) 1 N : ℝ) / N := hdiv
    _ < ε / 4 + (1 / (M : ℝ) + ε / 8) + (1 / (M : ℝ) + ε / 8) := by linarith
    _ < ε := by linarith [hMε]

end NormalNumbers
