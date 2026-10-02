/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Cell

/-!
# S7-T, the free half: tightness of the image expansion costs nothing, and the crux is the gap

The crux `OrbitCellBound q r₀ C` already contains its own hardest special case, `w = []`: the
frequency of **large digits** in the image expansion must be at most `C γ(cellSet [] T)`, and
`γ(cellSet [] T) ≤ 1/(T log 2)`.  Lap 30 recorded why that case is the one to attack first: a
post-emission state whose image straddles `1/k` below the cell scale destroys the per-state
distortion bound, and such a state is exactly one that emits a huge digit.

This module proves how far a *free* argument gets, and thereby locates the content of S7-T.

## The free bound

For **every** irrational `y ∈ (0,1)` the continuant dominates the digit product
(`prod_le_cfK`), and a digit `≥ T` contributes a factor `≥ T`, so

  `#{i < p : cfDigit y i ≥ T} · log T ≤ log (cfK (digitWord y p))`   (`largeDigitCount_mul_log_le`)

— no normality, no transducer, no state.  Under any Lévy-type bound `log qₚ ≤ Λ p` on the image
this reads: the frequency of digits `≥ T` is at most `Λ / log T` (`tailFreq_le_of_levyBound`),
which tends to `0`.  **So tightness of the image's empirical measures is free**; the
Krylov–Bogolyubov half of `GaussACRigidity` never needed the crux.

## …and why that is not enough

`1/log T` is not `O(1/T)`: `exists_rate_gap` produces, for every constant `C`, a threshold at which
the free bound is weaker than what `OrbitCellBound` demands.  The gap between `1/log T` and `1/T`
is therefore *exactly* the content of S7-T, and it is where the absolute continuity of the limit
measure lives — a Hölder modulus is not enough (`GaussACRigidity` genuinely needs the linear
bound, lap 29 refutation (c)), and `1/log T` is far short of even a Hölder modulus.

## Guard rule

Content locator: `pow_countP_le_prod` at `T = 1` is the trivial `1 ≤ ∏`, and
`blockCount_cellSet_nil_le_length` is the trivial `count ≤ p`; the free bound improves on the
latter only once `log T > Λ`, which `exists_rate_gap` then shows is never enough.  Degenerate
cases: `nonneg_of_levyBound` — a Lévy bound forces `0 ≤ Λ`, so the hypothesis is not vacuously
strong; and `largeDigitCount_mul_log_le` at `p = 0` is `0 ≤ 0`.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-! ## Counting large digits -/

/-- Along an irrational orbit, the empty word's cell is just "the next digit is at least `T`". -/
lemma mem_cellSet_nil_iff {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) (T : ℕ) :
    y ∈ cellSet [] T ↔ T ≤ cfDigit y 0 := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨hy, by intro i hi; simp at hi⟩, h⟩

/-- **The digit product dominates `T` to the power of the number of digits `≥ T`.**  The one
inequality behind the free bound. -/
theorem pow_countP_le_prod (T : ℕ) : ∀ (l : List ℕ), (∀ a ∈ l, 1 ≤ a) →
    T ^ (l.countP (fun a => decide (T ≤ a))) ≤ l.prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      have ha : 1 ≤ a := h a (List.mem_cons_self ..)
      have hl : ∀ b ∈ l, 1 ≤ b := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have ihl := ih hl
      rw [List.countP_cons, List.prod_cons]
      by_cases hT : T ≤ a
      · simp only [hT, decide_true, if_true]
        calc T ^ (l.countP (fun a => decide (T ≤ a)) + 1)
            = T ^ (l.countP (fun a => decide (T ≤ a))) * T := by rw [pow_succ]
          _ ≤ l.prod * a := Nat.mul_le_mul ihl hT
          _ = a * l.prod := by ring
      · simp only [hT, decide_false]
        exact le_trans ihl (Nat.le_mul_of_pos_left _ ha)

/-- The `w = []` cell count IS the count of large digits in the prefix word. -/
theorem blockCount_cellSet_nil_eq {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (T : ℕ) : ∀ p : ℕ,
    blockCount (cellSet [] T) p y = ((digitWord y p).countP (fun a => decide (T ≤ a)) : ℝ)
  | 0 => by simp [blockCount_apply, digitWord]
  | (p + 1) => by
      have ih := blockCount_cellSet_nil_eq hy hmem T p
      rw [blockCount_apply, Finset.sum_range_succ, ← blockCount_apply, ih]
      have hdw : digitWord y (p + 1) = digitWord y p ++ [cfDigit y p] := by
        simp [digitWord, List.range_succ]
      rw [hdw, List.countP_append]
      have horb : gaussMap^[p] y ∈ Set.Ioo (0:ℝ) 1 := (irrational_orbit y hy hmem p).2
      have hd : cfDigit (gaussMap^[p] y) 0 = cfDigit y p := (cfDigit_eq_iterate y p).symm
      by_cases hc : T ≤ cfDigit y p
      · have hin : gaussMap^[p] y ∈ cellSet [] T :=
          (mem_cellSet_nil_iff horb T).2 (by rw [hd]; exact hc)
        rw [blockIndic, Set.indicator_of_mem hin]
        simp [hc]
      · have hout : gaussMap^[p] y ∉ cellSet [] T := by
          intro hmem'
          exact hc (by rw [← hd]; exact (mem_cellSet_nil_iff horb T).1 hmem')
        rw [blockIndic, Set.indicator_of_notMem hout]
        simp [hc]

/-- The trivial bound: at most `p` of the first `p` digits are large. -/
theorem blockCount_cellSet_nil_le_length {y : ℝ} (hy : Irrational y)
    (hmem : y ∈ Set.Ioo (0:ℝ) 1) (T p : ℕ) : blockCount (cellSet [] T) p y ≤ p := by
  rw [blockCount_cellSet_nil_eq hy hmem T p]
  have := List.countP_le_length (l := digitWord y p) (p := fun a => decide (T ≤ a))
  have hlen : (digitWord y p).length = p := by simp [digitWord]
  rw [hlen] at this
  exact_mod_cast this

/-! ## The free bound -/

/-- **The free half of S7-T.**  For every irrational `y ∈ (0,1)`, every threshold and every
horizon, the number of large digits is at most `log qₚ / log T`.  No normality is used. -/
theorem largeDigitCount_mul_log_le {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (T p : ℕ) :
    blockCount (cellSet [] T) p y * Real.log T ≤ Real.log (cfK (digitWord y p)) := by
  have hpos : ∀ a ∈ digitWord y p, 1 ≤ a := by
    intro a ha
    simp only [digitWord, List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact one_le_cfDigit y hy hmem i
  set k := (digitWord y p).countP (fun a => decide (T ≤ a)) with hk
  have h1 : T ^ k ≤ cfK (digitWord y p) :=
    le_trans (pow_countP_le_prod T _ hpos) (prod_le_cfK _)
  rcases Nat.lt_or_ge T 1 with hT0 | hT1
  · -- `T = 0`: `log 0 = 0`, and the continuant is at least `1`.
    interval_cases T
    have : (0:ℝ) ≤ Real.log (cfK (digitWord y p)) :=
      Real.log_nonneg (by exact_mod_cast one_le_cfK _ hpos)
    simpa using this
  · have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT1
    have hKpos : (0:ℝ) < ((cfK (digitWord y p) : ℕ) : ℝ) := by
      have h := one_le_cfK (digitWord y p) hpos
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h
    have hlog : Real.log ((T ^ k : ℕ) : ℝ) ≤ Real.log ((cfK (digitWord y p) : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast h1)
    have hLHS : Real.log ((T ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log T := by
      push_cast
      rw [Real.log_pow]
    rw [hLHS] at hlog
    rw [blockCount_cellSet_nil_eq hy hmem T p, ← hk]
    exact hlog

/-! ## What it gives, and what it does not -/

/-- A Lévy-type bound on the image's continuants: `log qₚ ≤ Λ p` eventually.  It is the *only*
extra input the free tightness bound needs. -/
def LevyBound (y : ℝ) (Λ : ℝ) : Prop :=
  ∀ᶠ p : ℕ in atTop, Real.log (cfK (digitWord y p)) ≤ Λ * p

/-- **Degenerate verdict.**  A Lévy bound forces `0 ≤ Λ`: the continuant is at least `1`, so its
log is nonnegative. -/
theorem nonneg_of_levyBound {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {Λ : ℝ} (h : LevyBound y Λ) : 0 ≤ Λ := by
  obtain ⟨p, hp, hp1⟩ := (h.and (eventually_gt_atTop 0)).exists
  have hpos : ∀ a ∈ digitWord y p, 1 ≤ a := by
    intro a ha
    simp only [digitWord, List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact one_le_cfDigit y hy hmem i
  have h0 : (0:ℝ) ≤ Real.log (cfK (digitWord y p)) :=
    Real.log_nonneg (by exact_mod_cast one_le_cfK _ hpos)
  have hpr : (0:ℝ) < p := by exact_mod_cast hp1
  nlinarith

/-- **Tightness is free.**  Under a Lévy bound the frequency of digits `≥ T` in the image is at
most `Λ / log T`, for every horizon past the Lévy threshold. -/
theorem tailFreq_le_of_levyBound {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {Λ : ℝ} (hL : LevyBound y Λ) {T : ℕ} (hT : 2 ≤ T) :
    ∀ᶠ p : ℕ in atTop, blockCount (cellSet [] T) p y / p ≤ Λ / Real.log T := by
  have hTlog : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT)
  filter_upwards [hL, eventually_gt_atTop 0] with p hp hp1
  have hpr : (0:ℝ) < p := by exact_mod_cast hp1
  have hmain := largeDigitCount_mul_log_le hy hmem T p
  rw [div_le_div_iff₀ hpr hTlog]
  calc blockCount (cellSet [] T) p y * Real.log T
      ≤ Real.log (cfK (digitWord y p)) := hmain
    _ ≤ Λ * p := hp

/-- The free rate tends to `0`: the image's empirical measures are tight, unconditionally on the
crux. -/
theorem tendsto_freeRate (Λ : ℝ) :
    Tendsto (fun T : ℕ => Λ / Real.log T) atTop (nhds 0) := by
  have h : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h.const_div_atTop Λ

/-- **The gap, as a theorem.**  For every constant `C` there is a threshold at which the crux's
demand `C/T` is strictly stronger than the free bound `1/log T`.  So the free argument, however it
is sharpened in `Λ`, can never supply `OrbitCellBound` — the content of S7-T is exactly the
passage from `1/log T` to `1/T`. -/
theorem exists_rate_gap (C : ℝ) : ∃ T : ℕ, 2 ≤ T ∧ C / T < 1 / Real.log T := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (4 * C ^ 2 + 4) 2)
  refine ⟨n, ?_, ?_⟩
  · have : (2:ℝ) ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
    exact_mod_cast this
  · have hn2 : (2:ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
    have hnC : 4 * C ^ 2 + 4 < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hnpos : (0:ℝ) < n := by linarith
    have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
    -- `log n ≤ 2 √n`
    have hsq : Real.sqrt n * Real.sqrt n = (n:ℝ) := Real.mul_self_sqrt hnpos.le
    have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hlogs : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 :=
      Real.log_le_sub_one_of_pos hspos
    have hlog2 : Real.log n ≤ 2 * Real.sqrt n := by
      have : Real.log n = 2 * Real.log (Real.sqrt n) := by
        rw [Real.log_sqrt hnpos.le]; ring
      rw [this]; linarith
    -- `2 C √n < n` from `n > 4C² + 4`
    have hCs : C * Real.log n < (n:ℝ) := by
      rcases le_or_gt C 0 with hC | hC
      · nlinarith
      · have h2 : C * Real.log n ≤ 2 * C * Real.sqrt n := by nlinarith
        have h3 : 2 * C < Real.sqrt n := by nlinarith [sq_nonneg (Real.sqrt n - 2 * C)]
        nlinarith
    rw [div_lt_div_iff₀ hnpos hlogpos]
    linarith

section Audit

#print axioms pow_countP_le_prod
#print axioms blockCount_cellSet_nil_eq
#print axioms blockCount_cellSet_nil_le_length
#print axioms largeDigitCount_mul_log_le
#print axioms nonneg_of_levyBound
#print axioms tailFreq_le_of_levyBound
#print axioms tendsto_freeRate
#print axioms exists_rate_gap

end Audit

end NormalNumbers.VandeheyS7
