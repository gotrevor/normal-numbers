/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFCorrect
import NormalNumbers.DaryDigits

/-!
# W5 — correctness of the schedule, d-ary side (B–Y §2.2)

Per base `d` and stage `s` (with `d` active, `d ≤ tSched s`), the Lemma-13
payload puts `xstar` in a definite order-`mSched s d` cell and reads off a
GOOD block of new base-`d` digits up to order `mSched (s+1) d`
(`xstar_dary_step` + `digit_window_eq`).  This file sets up the accessors
and the `badBlocks ↔ HasDiscLt` bridge; the chain (Lemma 9), the `m`-growth
estimates, and the final simple-normality limits build on it.
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Accessors -/

/-- The d-ary cell order of stage `s` at base `d`. -/
noncomputable def mSched (s d : ℕ) : ℕ := (sched s).B.m d

/-- The d-ary cell index of stage `s` at base `d`. -/
noncomputable def jSched (s d : ℕ) : ℤ := (sched s).B.j d

theorem xstar_mem_Ioo : xstar ∈ Set.Ioo (0 : ℝ) 1 := (xstar_mem 0).1

/-- **The d-ary payload at `xstar`** (SchedStep payloads 5, 9, 10 combined):
for an active base, `xstar` lies in a definite cell of stage `s`'s block and
its refined sub-cell carries a good digit block, gaining at least
`kminFn (tSched (s+1))` digits. -/
theorem xstar_dary_step (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) :
    ∃ k : ℕ, mSched (s + 1) d = mSched s d + k ∧
      kminFn (tSched (s + 1)) ≤ k ∧
      ∃ i : ℕ, i < 2 ∧ xstar ∈ daryCell d (mSched s d) (jSched s d + i) 1 ∧
        ∃ β : Fin k → Fin d,
          β ∉ badBlocks d k (schedEps (tSched (s + 1))) ∧
          xstar ∈ daryCell d (mSched s d + k)
            ((jSched s d + i) * d ^ k
              + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1 := by
  obtain ⟨u, m₁, j₁, r₁, ht, hw, hlen, hpos, hold, hstart, hK, hCF, hgrow,
    hgood⟩ := sched_step s
  have hdt' : d ≤ tSched (s + 1) := le_trans hdt (sched_t_mono (Nat.le_succ s))
  obtain ⟨hm₁, hj₁⟩ := hold d hd2 hdt
  have hx : xstar ∈ cfCylinder ((sched (s + 1)).B.w) := xstar_mem (s + 1)
  have hgrow' := hgrow d hd2 hdt'
  obtain ⟨i, hi2, hcell, hβex⟩ := hgood d hd2 hdt' xstar hx
  -- make the digit gain `k` opaque BEFORE destructuring `∃ β` (the `set`
  -- rewrite is only type-correct while `β` is still bound)
  set k : ℕ := (sched (s + 1)).B.m d - m₁ d with hk
  clear_value k
  obtain ⟨β, hβ, hsub⟩ := hβex
  rw [hm₁, hj₁] at hcell hsub
  refine ⟨k, ?_, ?_, i, hi2, hcell, β, hβ, hsub⟩
  · have hms : mSched s d = m₁ d := hm₁.symm
    show (sched (s + 1)).B.m d = mSched s d + k
    omega
  · show kminFn ((sched (s + 1)).t) ≤ k
    omega

/-- The cell index of `xstar`'s cell is nonnegative (it is the floor of a
positive number below `d^m`). -/
theorem jSched_add_nonneg {s d : ℕ} (hd : 1 ≤ d) {i : ℕ}
    (hcell : xstar ∈ daryCell d (mSched s d) (jSched s d + i) 1) :
    0 ≤ jSched s d + i := by
  have hfloor := floor_eq_of_mem_daryCell_one hd hcell
  rw [← hfloor]
  have hx0 : 0 ≤ xstar := xstar_mem_Ioo.1.le
  positivity

/-! ## The `badBlocks ↔ HasDiscLt` bridge -/

/-- Avoiding the bad-block set is exactly the deviation-form discrepancy
bound of B–Y Lemma 9. -/
theorem hasDiscLt_ofFn_of_notMem_badBlocks {d k : ℕ} {ε : ℝ}
    {β : Fin k → Fin d} (hβ : β ∉ badBlocks d k ε) :
    HasDiscLt (List.ofFn β) ε := by
  intro c
  rw [badBlocks, Finset.mem_filter] at hβ
  push Not at hβ
  have h := hβ (Finset.mem_univ β) c
  rw [← digitCount_eq_count_ofFn, List.length_ofFn]
  exact h

/-- `HasDiscLt` is monotone in the accuracy. -/
theorem HasDiscLt.mono {b : ℕ} {u : List (Fin b)} {ε ε' : ℝ}
    (h : HasDiscLt u ε) (hε : ε ≤ ε') : HasDiscLt u ε' := fun c =>
  lt_of_lt_of_le (h c) (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- **The per-stage digit window of `xstar`** (a, b combined): at each stage
with base `d` active, `xstar` gains `k ≥ kminFn` new base-`d` digits, and
that digit window is a `schedEps (tSched (s+1))`-good block. -/
theorem xstar_dary_window (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) :
    ∃ k : ℕ, mSched (s + 1) d = mSched s d + k ∧
      kminFn (tSched (s + 1)) ≤ k ∧
      ∃ β : Fin k → Fin d,
        HasDiscLt (List.ofFn β) (schedEps (tSched (s + 1))) ∧
        (List.range k).map (fun l => digitOf d xstar (mSched s d + l))
          = List.ofFn fun i => (β i : ℕ) := by
  obtain ⟨k, hm, hkmin, i, hi2, hcell, β, hβ, hsub⟩ :=
    xstar_dary_step s d hd2 hdt
  have hd1 : 1 ≤ d := by omega
  have hJ : 0 ≤ jSched s d + i := jSched_add_nonneg hd1 hcell
  exact ⟨k, hm, hkmin, β, hasDiscLt_ofFn_of_notMem_badBlocks hβ,
    digit_window_eq hd1 hJ hsub⟩

/-! ## Continuant growth (for the `m`-growth estimates) -/

/-- Fibonacci doubling: `2^j ≤ fib (2j + 1)`. -/
theorem two_pow_le_fib (j : ℕ) : 2 ^ j ≤ Nat.fib (2 * j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
    rw [h1, Nat.fib_add_two, pow_succ]
    have h2 : Nat.fib (2 * j + 1) ≤ Nat.fib (2 * j + 1 + 1) :=
      Nat.fib_mono (Nat.le_succ _)
    omega

/-- Exponential continuant growth: a genuine word of length `n` has
`cfK ≥ 2^(n/2)` (integer division). -/
theorem two_pow_le_cfK (u : List ℕ) (hpos : ∀ a ∈ u, 1 ≤ a) :
    2 ^ (u.length / 2) ≤ cfK u := by
  have h1 := fib_le_cfK u hpos
  have h2 : 2 * (u.length / 2) + 1 ≤ u.length + 1 := by omega
  calc 2 ^ (u.length / 2) ≤ Nat.fib (2 * (u.length / 2) + 1) :=
        two_pow_le_fib _
    _ ≤ Nat.fib (u.length + 1) := Nat.fib_mono h2
    _ ≤ cfK u := h1

/-- **The per-stage `d`-power bracket** (foundation of the `m`-growth estimate,
DIRECTIVE item (c)): at every stage `s` with base `d` active, `d^{mSched s d}`
is pinned within a constant factor of `cfK (wSched s)²`.  Both bounds come
straight from the brick: the LOWER from the ratio field `d^{-m} ≤ 2d·|I_w|`
(with `|I_w| ≤ 1/cfK²`), the UPPER from the `≤ 2`-cell containment
`|I_w| ≤ 2·d^{-m}` (with `|I_w| ≥ 1/(2·cfK²)`).  This is the interval that will
turn the per-stage digit gain `k = mSched (s+1) d − mSched s d` into a bounded
multiple of `log cfK (uSched s)`: dividing the bracket at `s+1` by the bracket
at `s` gives `cfK (uSched s)²/(8d) ≤ d^k ≤ 32d·cfK (uSched s)²`. -/
theorem dpow_mSched_bracket (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) :
    (cfK (wSched s) : ℝ) ^ 2 / (2 * d) ≤ (d : ℝ) ^ (mSched s d) ∧
      (d : ℝ) ^ (mSched s d) ≤ 4 * (cfK (wSched s) : ℝ) ^ 2 := by
  have hw_ne : wSched s ≠ [] := wSched_ne s
  have hw_pos : ∀ a ∈ wSched s, 1 ≤ a := wSched_pos s
  set Q : ℝ := (cfK (wSched s) : ℝ) with hQ
  set D : ℝ := (cfK (wSched s).dropLast : ℝ) with hD
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQ]; exact_mod_cast one_le_cfK (wSched s) hw_pos
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le one_pos hQ1
  have hD0 : (0 : ℝ) ≤ D := by rw [hD]; positivity
  have hDQ : D ≤ Q := by rw [hD, hQ]; exact_mod_cast cfK_dropLast_le (wSched s) hw_pos
  have hQQD : (0 : ℝ) < Q * (Q + D) := by positivity
  have hmeq : mSched s d = (sched s).B.m d := rfl
  have hwB : wSched s = (sched s).B.w := rfl
  have hP0 : (0 : ℝ) < (d : ℝ) ^ (mSched s d) := by positivity
  have hvol : volume (cfCylinder (wSched s)) = ENNReal.ofReal (1 / (Q * (Q + D))) := by
    rw [hQ, hD]; exact volume_cfCylinder (wSched s) hw_ne hw_pos
  -- LOWER bound `Q²/(2d) ≤ d^m` from the ratio field.
  have hlow : Q ^ 2 / (2 * d) ≤ (d : ℝ) ^ (mSched s d) := by
    have hratio := (sched s).B.hratio d hd2 hdt
    rw [← hwB, hvol] at hratio
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * d)] at hratio
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hratio
    -- hratio : ((d)^((sched s).B.m d))⁻¹ ≤ 2*d * (1/(Q*(Q+D)))
    rw [← hmeq] at hratio
    have hcross : Q * (Q + D) ≤ 2 * (d : ℝ) * (d : ℝ) ^ (mSched s d) := by
      rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ hP0 hQQD, one_mul] at hratio
      linarith [hratio]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)]
    nlinarith [hcross, mul_nonneg hQ0.le hD0]
  -- UPPER bound `d^m ≤ 4Q²` from the ≤2-cell containment.
  have hup : (d : ℝ) ^ (mSched s d) ≤ 4 * Q ^ 2 := by
    have hr2 : ((sched s).B.r d : ℝ) ≤ 2 := by exact_mod_cast (sched s).B.hr2 d hd2 hdt
    have hupvol : volume (cfCylinder (wSched s))
        ≤ ENNReal.ofReal (2 / (d : ℝ) ^ (mSched s d)) := by
      calc volume (cfCylinder (wSched s))
          ≤ volume (daryCell d ((sched s).B.m d) ((sched s).B.j d) ((sched s).B.r d)) := by
            rw [hwB]; exact measure_mono ((sched s).B.hsub d hd2 hdt)
        _ = ENNReal.ofReal (((sched s).B.r d : ℝ) / (d : ℝ) ^ ((sched s).B.m d)) :=
            volume_daryCell d ((sched s).B.m d) hd1 ((sched s).B.j d) ((sched s).B.r d)
        _ ≤ ENNReal.ofReal (2 / (d : ℝ) ^ (mSched s d)) := by
            rw [← hmeq]
            exact ENNReal.ofReal_le_ofReal
              (div_le_div_of_nonneg_right hr2 (pow_nonneg hdR.le _))
    rw [hvol, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hupvol
    -- hupvol : 1/(Q*(Q+D)) ≤ 2/d^m
    have hcross : (d : ℝ) ^ (mSched s d) ≤ 2 * (Q * (Q + D)) := by
      rw [div_le_div_iff₀ hQQD hP0, one_mul] at hupvol
      linarith [hupvol]
    nlinarith [hcross, hDQ, hQ0, mul_le_mul_of_nonneg_left hDQ hQ0.le]
  exact ⟨hlow, hup⟩

/-- The digits of the block appended at step `s` are genuine (`≥ 1`). -/
theorem uSched_pos (s : ℕ) : ∀ a ∈ uSched s, 1 ≤ a := by
  intro a ha
  have hmem : a ∈ wSched (s + 1) := by
    rw [wSched_succ]; exact List.mem_append_right _ ha
  exact wSched_pos (s + 1) a hmem

/-- **Per-stage `d`-power gain bracket** (c1): dividing `dpow_mSched_bracket` at
`s+1` by the one at `s`, the multiplicative digit gain `d^k` (where
`k = mSched (s+1) d − mSched s d`) is pinned within a constant factor of
`cfK (uSched s)²`.  Stated in cleared (division-free) form.  Upper via
`cfK (w++u) ≤ 2 cfK w cfK u`, lower via `cfK w cfK u ≤ cfK (w++u)`. -/
theorem dpow_gain_bracket (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) {k : ℕ}
    (hk : mSched (s + 1) d = mSched s d + k) :
    (cfK (uSched s) : ℝ) ^ 2 ≤ 8 * d * (d : ℝ) ^ k ∧
      (d : ℝ) ^ k ≤ 32 * d * (cfK (uSched s) : ℝ) ^ 2 := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hdt1 : d ≤ tSched (s + 1) := le_trans hdt (sched_t_mono (Nat.le_succ s))
  obtain ⟨hlo_s, hup_s⟩ := dpow_mSched_bracket s d hd2 hdt
  obtain ⟨hlo_s1, hup_s1⟩ := dpow_mSched_bracket (s + 1) d hd2 hdt1
  set Ws : ℝ := (cfK (wSched s) : ℝ) with hWs
  set Ws1 : ℝ := (cfK (wSched (s + 1)) : ℝ) with hWs1
  set U : ℝ := (cfK (uSched s) : ℝ) with hU
  have hWs0 : (0 : ℝ) < Ws := by
    rw [hWs]; exact_mod_cast lt_of_lt_of_le one_pos (one_le_cfK _ (wSched_pos s))
  have hU0 : (0 : ℝ) < U := by
    rw [hU]; exact_mod_cast lt_of_lt_of_le one_pos (one_le_cfK _ (uSched_pos s))
  -- quasi-multiplicativity of the continuant along `w(s+1) = w s ++ u s`
  have happ_up : Ws1 ≤ 2 * (Ws * U) := by
    rw [hWs1, hWs, hU, wSched_succ]
    exact_mod_cast cfK_append_le (wSched s) (uSched s) (wSched_ne s) (uSched_ne s)
      (wSched_pos s) (uSched_pos s)
  have happ_lo : Ws * U ≤ Ws1 := by
    rw [hWs1, hWs, hU, wSched_succ]
    exact_mod_cast cfK_mul_le_append (wSched s) (uSched s) (wSched_ne s) (uSched_ne s)
      (wSched_pos s) (uSched_pos s)
  have hWs10 : (0 : ℝ) < Ws1 := lt_of_lt_of_le (by positivity) happ_lo
  -- factor `d^{m(s+1)} = d^{m s} · d^k`
  have hsplit : (d : ℝ) ^ (mSched (s + 1) d)
      = (d : ℝ) ^ (mSched s d) * (d : ℝ) ^ k := by rw [hk, pow_add]
  have hms0 : (0 : ℝ) < (d : ℝ) ^ (mSched s d) := by positivity
  have hdk0 : (0 : ℝ) < (d : ℝ) ^ k := by positivity
  have hWs2 : (0 : ℝ) < Ws ^ 2 := by positivity
  -- cleared bracket hypotheses (division removed)
  have hlo_s1' : Ws1 ^ 2 ≤ 2 * d * ((d : ℝ) ^ (mSched s d) * (d : ℝ) ^ k) := by
    have h := hlo_s1
    rw [hsplit, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)] at h
    nlinarith [h]
  have hup_s1' : (d : ℝ) ^ (mSched s d) * (d : ℝ) ^ k ≤ 4 * Ws1 ^ 2 := by
    have h := hup_s1; rw [hsplit] at h; linarith [h]
  have hlo_s' : Ws ^ 2 ≤ 2 * d * (d : ℝ) ^ (mSched s d) := by
    have h := hlo_s
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)] at h
    nlinarith [h]
  -- squared quasi-multiplicativity
  have sqlo2 : Ws ^ 2 * U ^ 2 ≤ Ws1 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr happ_lo)
      (by positivity : (0 : ℝ) ≤ Ws1 + Ws * U)]
  have squp2 : Ws1 ^ 2 ≤ 4 * (Ws ^ 2 * U ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr happ_up)
      (by positivity : (0 : ℝ) ≤ 2 * (Ws * U) + Ws1)]
  refine ⟨?_, ?_⟩
  · -- lower: U² ≤ 8d·d^k
    have hchain : Ws ^ 2 * U ^ 2 ≤ 8 * d * (Ws ^ 2 * (d : ℝ) ^ k) := by
      have t1 : Ws ^ 2 * U ^ 2
          ≤ 2 * d * ((d : ℝ) ^ (mSched s d) * (d : ℝ) ^ k) := le_trans sqlo2 hlo_s1'
      have t2 : 2 * d * ((d : ℝ) ^ (mSched s d) * (d : ℝ) ^ k)
          ≤ 8 * d * (Ws ^ 2 * (d : ℝ) ^ k) := by
        nlinarith [mul_le_mul_of_nonneg_left hup_s
          (by positivity : (0 : ℝ) ≤ 2 * d * (d : ℝ) ^ k)]
      exact le_trans t1 t2
    nlinarith [hchain, hWs2]
  · -- upper: d^k ≤ 32d·U²
    have hchain : Ws ^ 2 * (d : ℝ) ^ k ≤ 32 * d * (Ws ^ 2 * U ^ 2) := by
      have t1 : Ws ^ 2 * (d : ℝ) ^ k
          ≤ 2 * d * ((d : ℝ) ^ (mSched s d) * (d : ℝ) ^ k) := by
        nlinarith [mul_le_mul_of_nonneg_right hlo_s'
          (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ k)]
      have t2 : 2 * d * ((d : ℝ) ^ (mSched s d) * (d : ℝ) ^ k)
          ≤ 2 * d * (4 * Ws1 ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hup_s1'
          (by positivity : (0 : ℝ) ≤ 2 * d)]
      have t3 : 2 * d * (4 * Ws1 ^ 2) ≤ 32 * d * (Ws ^ 2 * U ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left squp2
          (by positivity : (0 : ℝ) ≤ 2 * d)]
      exact le_trans (le_trans t1 t2) t3
    nlinarith [hchain, hWs2]

/-- **(c2) the log of the gain bracket**: taking `Real.log` of `dpow_gain_bracket`
turns the per-stage digit gain `k = mSched (s+1) d − mSched s d` into a two-sided
bound by `log cfK (uSched s)`, in division-free `k·log d` form (`log d > 0` since
`d ≥ 2`).  This is the shape the interior estimate sums: the numerator uses the
upper bound (`k` small when `cfK (uSched s)` is small — good-length control),
the denominator the lower bound (`Σ k_j` large via `two_pow_le_cfK`). -/
theorem log_gain_bracket (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) {k : ℕ}
    (hk : mSched (s + 1) d = mSched s d + k) :
    2 * Real.log (cfK (uSched s)) - Real.log (8 * d) ≤ (k : ℝ) * Real.log d ∧
      (k : ℝ) * Real.log d
        ≤ 2 * Real.log (cfK (uSched s)) + Real.log (32 * d) := by
  obtain ⟨hlo, hup⟩ := dpow_gain_bracket s d hd2 hdt hk
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  set U : ℝ := (cfK (uSched s) : ℝ) with hU
  have hU0 : (0 : ℝ) < U := by
    rw [hU]; exact_mod_cast lt_of_lt_of_le one_pos (one_le_cfK _ (uSched_pos s))
  have hdk0 : (0 : ℝ) < (d : ℝ) ^ k := by positivity
  have hlogdk : Real.log ((d : ℝ) ^ k) = (k : ℝ) * Real.log d := by rw [Real.log_pow]
  have hlogU2 : Real.log (U ^ 2) = 2 * Real.log U := by
    rw [Real.log_pow]; push_cast; ring
  have h8d : (8 : ℝ) * d ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 8) hdR).ne'
  have h32d : (32 : ℝ) * d ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 32) hdR).ne'
  have hdkne : ((d : ℝ) ^ k) ≠ 0 := hdk0.ne'
  have hU2ne : (U ^ 2) ≠ 0 := (pow_pos hU0 2).ne'
  refine ⟨?_, ?_⟩
  · have h := Real.log_le_log (pow_pos hU0 2) hlo
    rw [hlogU2, Real.log_mul h8d hdkne, hlogdk] at h
    linarith [h]
  · have h := Real.log_le_log hdk0 hup
    rw [hlogdk, Real.log_mul h32d hU2ne, hlogU2] at h
    linarith [h]

/-- **(c3a) the numerator bound**: feeding the good-length control
`cfK (uSched s) ≤ exp(goodC · nFn (tSched (s+1)))` (from `uSched_spec`) into the
upper half of `log_gain_bracket`, the per-stage digit gain `k` obeys
`k · log d ≤ 2·goodC·n_{s+1} + log(32d)` — i.e. `k` grows at most linearly in the
stage length `n_{s+1} = nFn (tSched (s+1))`.  This is the numerator of the
interior ratio `k_{s+1} / (m_d(s) − m_d(s₀))`. -/
theorem gain_le (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) {k : ℕ}
    (hk : mSched (s + 1) d = mSched s d + k) :
    (k : ℝ) * Real.log d
      ≤ 2 * goodC * nFn (tSched (s + 1)) + Real.log (32 * d) := by
  obtain ⟨-, hup⟩ := log_gain_bracket s d hd2 hdt hk
  have hgood := (uSched_spec s).2.2.1
  have hU0 : (0 : ℝ) < (cfK (uSched s) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_pos (one_le_cfK _ (uSched_pos s))
  have hlog : Real.log (cfK (uSched s)) ≤ goodC * nFn (tSched (s + 1)) := by
    have h := Real.log_le_log hU0 hgood
    rwa [Real.log_exp] at h
  linarith [hup, hlog]

/-- **(c3b) the denominator building block**: the lower half of
`dpow_mSched_bracket` together with `two_pow_le_cfK` on `wSched s` pins the
accumulated digit count from below by the word length —
`m_d(s) · log d ≥ 2·⌊L_s/2⌋·log 2 − log(2d)` where `L_s = |wSched s|`.  Since the
denominator of the interior ratio is `m_d(s) − m_d(s₀)` and `L_s → ∞`, this
grows like `(log 2 / log d)·L_s`, beating the numerator's `∼ n_{s+1}` under the
schedule dominance `t·n(t) ≤ L`. -/
theorem le_mSched_mul_log (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) :
    2 * (((wSched s).length / 2 : ℕ) : ℝ) * Real.log 2 - Real.log (2 * d)
      ≤ (mSched s d : ℝ) * Real.log d := by
  obtain ⟨hlo, -⟩ := dpow_mSched_bracket s d hd2 hdt
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  set W : ℝ := (cfK (wSched s) : ℝ) with hW
  have hW0 : (0 : ℝ) < W := by
    rw [hW]; exact_mod_cast lt_of_lt_of_le one_pos (one_le_cfK _ (wSched_pos s))
  have hcleared : W ^ 2 ≤ 2 * d * (d : ℝ) ^ (mSched s d) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)] at hlo
    nlinarith [hlo]
  have h2d : (2 : ℝ) * d ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) hdR).ne'
  have hdmne : ((d : ℝ) ^ (mSched s d)) ≠ 0 :=
    (by positivity : (0 : ℝ) < (d : ℝ) ^ (mSched s d)).ne'
  have hlogcl : (2 : ℝ) * Real.log W
      ≤ Real.log (2 * d) + (mSched s d : ℝ) * Real.log d := by
    have h := Real.log_le_log (pow_pos hW0 2) hcleared
    rw [Real.log_mul h2d hdmne] at h
    simp only [Real.log_pow] at h
    push_cast at h
    linarith [h]
  have htwo : (2 : ℝ) ^ ((wSched s).length / 2) ≤ W := by
    rw [hW]; exact_mod_cast two_pow_le_cfK (wSched s) (wSched_pos s)
  have hlogW : (((wSched s).length / 2 : ℕ) : ℝ) * Real.log 2 ≤ Real.log W := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ ((wSched s).length / 2)) htwo
    rwa [Real.log_pow] at h
  linarith [hlogcl, hlogW]

end NormalNumbers
