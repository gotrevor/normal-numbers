/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableNormal
import NormalNumbers.VisitDeviationB

/-!
# Polynomial decay + computable lower approximations ⇒ a computable coin sequence whose image
is normal in every base

All-bases version of `ComputableNormal.exists_computable_normal_of_digits`.  For `b` not a power
of `2`, `⌊G ω · bᵐ⌋` is not a function of a finite coin prefix, so the tests read a computable
**lower approximation** `A p ≤ G ω ≤ A p + 2^{-|p|}` (`p` a prefix of `ω`) through its exact
floors `Ψ b m p = ⌊A p · bᵐ⌋`.

Level `n` (`N = n^14`) tests every base `2 ≤ b ≤ n`:
* block tests `(ℓ, v)`, `1 ≤ ℓ`, `b^ℓ ≤ n`: approximate visit count `Vc` within `3N/(4n)` of
  `N b^{-ℓ}`;
* a top test: the approximate orbit points at indices `< N + n` fall in the top depth-`n` cell
  `[1 − b^{-n}, 1)` at most `N/(4n)` times.
A floor mismatch between `G ω` and `A p` at exponent `E` forces the approximate point at index
`E` into that top cell (`top_of_floor_ne`), so passing the top test bounds the error of every
block count by `N/(4n)` (`Vtrue_sub_Vc_le`).  Conversely an approximate top visit is a true visit
to `[0, b^{-n}) ∪ [1 − b^{-n}, 1)` (`orbit_mem_of_top`), which `visit_deviation_b` controls.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.ComputableNormalB

open Derandomize DecayAeNormal VisitDeviation VisitDeviationB ComputableNormal

/-! ## Orbit cells as floor residues, base `b` -/

/-- **Orbit block membership is a floor residue**, base `b`. -/
theorem orbit_mem_iff_b (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : 0 ≤ x) (k ℓ v : ℕ) :
    orbit b x k ∈ Set.Ico ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) ↔
      ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ % b ^ ℓ = v := by
  have hb0 : (0 : ℝ) < b := by positivity
  set y := x * (b : ℝ) ^ k with hydef
  have hy0 : 0 ≤ y := by positivity
  have horb : orbit b x k = Int.fract y := by simp [orbit, hydef]
  set f := Int.fract y
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hyf : y = (⌊y⌋₊ : ℝ) + f := by
    simp only [f, Int.fract]
    rw [← Int.natCast_floor_eq_floor hy0]; push_cast; ring
  have hP : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  set c := ⌊f * (b : ℝ) ^ ℓ⌋₊
  have hc : c < b ^ ℓ := by
    have : f * (b : ℝ) ^ ℓ < (b ^ ℓ : ℕ) := by push_cast; nlinarith
    exact (Nat.floor_lt (by positivity)).2 this
  have hfloor : ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ = ⌊y⌋₊ * b ^ ℓ + c := by
    have : x * (b : ℝ) ^ (k + ℓ) = f * (b : ℝ) ^ ℓ + ((⌊y⌋₊ * b ^ ℓ : ℕ) : ℝ) := by
      rw [pow_add, ← mul_assoc, ← hydef]
      conv_lhs => rw [hyf]
      push_cast; ring
    rw [this, Nat.floor_add_natCast (by positivity)]
    ring
  rw [hfloor, Nat.mul_add_mod_of_lt hc, horb]
  rw [Set.mem_Ico, div_le_iff₀ hP, lt_div_iff₀ hP, eq_comm]
  simp only [c]
  rw [eq_comm, Nat.floor_eq_iff (by positivity)]

/-- The top depth-`r` cell: `fract(y) ≥ 1 − b^{-r}` iff the depth-`r` digit block is all `b−1`. -/
theorem top_iff (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha : 0 ≤ a) (E r : ℕ) :
    1 - 1 / (b : ℝ) ^ r ≤ Int.fract (a * (b : ℝ) ^ E) ↔
      ⌊a * (b : ℝ) ^ (E + r)⌋₊ % b ^ r = b ^ r - 1 := by
  have hb1 : 1 ≤ b ^ r := Nat.one_le_pow _ _ (by omega)
  rw [← orbit_mem_iff_b b hb a ha E r (b ^ r - 1)]
  have hP : (0 : ℝ) < (b : ℝ) ^ r := by positivity
  simp only [orbit, Set.mem_Ico, Nat.cast_sub hb1, Nat.cast_pow, Nat.cast_one]
  have e1 : ((b : ℝ) ^ r - 1) / (b : ℝ) ^ r = 1 - 1 / (b : ℝ) ^ r := by field_simp
  have e2 : ((b : ℝ) ^ r - 1 + 1) / (b : ℝ) ^ r = 1 := by rw [sub_add_cancel]; field_simp
  rw [e1, e2]
  exact ⟨fun h => ⟨h, Int.fract_lt_one _⟩, fun h => h.1⟩

/-- A floor mismatch forces the approximation into the top cell. -/
theorem top_of_floor_ne (b : ℕ) (hb : 2 ≤ b) {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (E r : ℕ)
    (hη : (x - a) * (b : ℝ) ^ E ≤ 1 / (b : ℝ) ^ r)
    (hne : ⌊x * (b : ℝ) ^ E⌋₊ ≠ ⌊a * (b : ℝ) ^ E⌋₊) :
    ⌊a * (b : ℝ) ^ (E + r)⌋₊ % b ^ r = b ^ r - 1 := by
  rw [← top_iff b hb a ha E r]
  have hbE : (0 : ℝ) < (b : ℝ) ^ E := by positivity
  set X := x * (b : ℝ) ^ E
  set Y := a * (b : ℝ) ^ E
  have hY0 : 0 ≤ Y := by positivity
  have hXY : Y ≤ X := mul_le_mul_of_nonneg_right hax hbE.le
  have hle : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hXY
  have hlt : ⌊Y⌋₊ + 1 ≤ ⌊X⌋₊ := by omega
  have h1 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ X :=
    (Nat.cast_le.2 hlt).trans (Nat.floor_le (hY0.trans hXY))
  have hdiff : X - Y ≤ 1 / (b : ℝ) ^ r := by
    have : X - Y = (x - a) * (b : ℝ) ^ E := by simp only [X, Y]; ring
    rw [this]; exact hη
  have hfr : Int.fract Y = Y - ⌊Y⌋₊ := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor hY0]; push_cast; ring
  rw [hfr]
  push_cast at h1
  linarith

/-- An approximate top visit is a true visit near `0` or near `1`. -/
theorem orbit_mem_of_top (b : ℕ) (hb : 2 ≤ b) {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (j r : ℕ)
    (hη : (x - a) * (b : ℝ) ^ j ≤ 1 / (b : ℝ) ^ r)
    (htop : ⌊a * (b : ℝ) ^ (j + r)⌋₊ % b ^ r = b ^ r - 1) :
    orbit b x j ∈ Set.Ico 0 (1 / (b : ℝ) ^ r) ∨ orbit b x j ∈ Set.Ico (1 - 1 / (b : ℝ) ^ r) 1 := by
  rw [← top_iff b hb a ha j r] at htop
  have hbE : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  set X := x * (b : ℝ) ^ j
  set Y := a * (b : ℝ) ^ j
  have hY0 : 0 ≤ Y := by positivity
  have hXY : Y ≤ X := mul_le_mul_of_nonneg_right hax hbE.le
  have hdiff : X - Y ≤ 1 / (b : ℝ) ^ r := by
    have : X - Y = (x - a) * (b : ℝ) ^ j := by simp only [X, Y]; ring
    rw [this]; exact hη
  have horb : orbit b x j = Int.fract X := rfl
  rw [horb]
  have hfX0 := Int.fract_nonneg X
  have hfX1 := Int.fract_lt_one X
  have hfY1 := Int.fract_lt_one Y
  have hfl : ⌊Y⌋ ≤ ⌊X⌋ := Int.floor_le_floor hXY
  rcases eq_or_lt_of_le hfl with h | h
  · right
    refine ⟨?_, hfX1⟩
    have : Int.fract X = Int.fract Y + (X - Y) := by
      rw [Int.fract, Int.fract, ← h]; ring
    linarith
  · left
    refine ⟨hfX0, ?_⟩
    have h' : (⌊Y⌋ : ℝ) + 1 ≤ ⌊X⌋ := by exact_mod_cast h
    have hX : Int.fract X = X - ⌊X⌋ := rfl
    have hY : Int.fract Y = Y - ⌊Y⌋ := rfl
    linarith

/-! ## The tests -/

section Tests

variable (Ψ : ℕ → ℕ → List Bool → ℕ)

/-- Approximate depth-`r` digit block at orbit index `E`. -/
def dA (b E r : ℕ) (p : List Bool) : ℕ := Ψ b (E + r) p % b ^ r

/-- Approximate visit count of the cell `(ℓ, v)` among the first `N` orbit points. -/
def Vc (b ℓ v N : ℕ) (p : List Bool) : ℕ :=
  ((List.range N).map fun k => if dA Ψ b k ℓ p = v then 1 else 0).sum

/-- Approximate visits to the top depth-`n` cell among the first `n^14 + n` orbit points. -/
def Tc (b n : ℕ) (p : List Bool) : ℕ :=
  ((List.range (n ^ 14 + n)).map fun j => if dA Ψ b j n p = b ^ n - 1 then 1 else 0).sum

/-- `|Vc/N − b^{-ℓ}| > 3/(4n)`, `N = n^14`. -/
def fails (b n ℓ v : ℕ) (p : List Bool) : Prop :=
  3 * n ^ 14 * b ^ ℓ < 4 * n * (Vc Ψ b ℓ v (n ^ 14) p * b ^ ℓ - n ^ 14 +
    (n ^ 14 - Vc Ψ b ℓ v (n ^ 14) p * b ^ ℓ))

/-- `Tc > N/(4n)`. -/
def failsTop (b n : ℕ) (p : List Bool) : Prop := n ^ 14 < 4 * n * Tc Ψ b n p

instance (b n ℓ v : ℕ) (p : List Bool) : Decidable (fails Ψ b n ℓ v p) := by
  unfold fails; infer_instance

instance (b n : ℕ) (p : List Bool) : Decidable (failsTop Ψ b n p) := by
  unfold failsTop; infer_instance

/-- Number of failing tests for base `b` at level `n`. -/
def baseBad (b n : ℕ) (p : List Bool) : ℕ :=
  (if failsTop Ψ b n p then 1 else 0) +
  ((List.range (n + 1)).map fun ℓ => if 1 ≤ ℓ ∧ b ^ ℓ ≤ n then
    ((List.range (b ^ ℓ)).map fun v => if fails Ψ b n ℓ v p then 1 else 0).sum else 0).sum

/-- Number of failing tests at level `n`, all bases `2 ≤ b ≤ n`. -/
def levelBad (n : ℕ) (p : List Bool) : ℕ :=
  ((List.range (n + 1)).map fun b => if 2 ≤ b then baseBad Ψ b n p else 0).sum

def badT (n₀ j : ℕ) (p : List Bool) : Bool := decide (0 < levelBad Ψ (j + n₀) p)

/-- Depth of test `j`: `n (n^14 + 2n)` coins, `n = j + n₀`. -/
def depth (n₀ j : ℕ) : ℕ := (j + n₀) * ((j + n₀) ^ 14 + 2 * (j + n₀))

end Tests

/-! ## Counting -/

theorem list_sum_range_map (f : ℕ → ℕ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ k ∈ Finset.range N, f k := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem visitCount_eq_sum (u : ℕ → ℝ) (a c : ℝ) (N : ℕ) :
    visitCount u a c N = ∑ k ∈ Finset.range N, if u k ∈ Set.Ico a c then 1 else 0 := by
  classical
  unfold visitCount
  rw [Finset.card_filter]

section Count

variable (Ψ : ℕ → ℕ → List Bool → ℕ) (A : List Bool → ℝ)

/-- **Block counts: true vs approximate, error at most the top count.** -/
theorem abs_Vtrue_sub_Vc_le (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊)
    (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (p : List Bool) (ha : 0 ≤ A p) (hax : A p ≤ x)
    (n : ℕ) (hη : (x - A p) * (b : ℝ) ^ (n ^ 14 + 2 * n) ≤ 1) {ℓ v : ℕ} (hℓn : ℓ ≤ n) :
    |(visitCount (orbit b x) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (n ^ 14) : ℝ) -
      (Vc Ψ b ℓ v (n ^ 14) p : ℝ)| ≤ Tc Ψ b n p := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hx0 : 0 ≤ x := ha.trans hax
  set t : ℕ → ℕ := fun j => if dA Ψ b j n p = b ^ n - 1 then 1 else 0 with ht
  -- termwise
  have hterm : ∀ k < n ^ 14, |(if orbit b x k ∈ Set.Ico ((v : ℝ) / (b : ℝ) ^ ℓ)
      ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) then (1 : ℝ) else 0) -
      (if dA Ψ b k ℓ p = v then (1 : ℝ) else 0)| ≤ (t (ℓ + k) : ℝ) := by
    intro k hk
    have hiff := orbit_mem_iff_b b hb x hx0 k ℓ v
    by_cases hfl : ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ = ⌊A p * (b : ℝ) ^ (k + ℓ)⌋₊
    · have hd : dA Ψ b k ℓ p = ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ % b ^ ℓ := by
        rw [dA, hΨ, hfl]
      have hPQ : orbit b x k ∈ Set.Ico ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) ↔
          dA Ψ b k ℓ p = v := by rw [hiff, hd]
      have ht0 : (0 : ℝ) ≤ t (ℓ + k) := by positivity
      by_cases hQ : dA Ψ b k ℓ p = v
      · rw [if_pos (hPQ.2 hQ), if_pos hQ]; simpa using ht0
      · rw [if_neg (fun h => hQ (hPQ.1 h)), if_neg hQ]; simpa using ht0
    · have htop := top_of_floor_ne b hb ha hax (k + ℓ) n ?_ hfl
      · have : t (ℓ + k) = 1 := by
          simp only [ht, dA, hΨ, show ℓ + k + n = k + ℓ + n by ring]
          rw [if_pos htop]
        rw [this]
        split_ifs <;> norm_num
      · have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
        have hpow : (b : ℝ) ^ (k + ℓ) * (b : ℝ) ^ n ≤ (b : ℝ) ^ (n ^ 14 + 2 * n) := by
          rw [← pow_add]; exact pow_le_pow_right₀ hb1 (by omega)
        rw [le_div_iff₀ hbn]
        have h0 : 0 ≤ x - A p := by linarith
        calc (x - A p) * (b : ℝ) ^ (k + ℓ) * (b : ℝ) ^ n
            = (x - A p) * ((b : ℝ) ^ (k + ℓ) * (b : ℝ) ^ n) := by ring
          _ ≤ (x - A p) * (b : ℝ) ^ (n ^ 14 + 2 * n) := by gcongr
          _ ≤ 1 := hη
  rw [visitCount_eq_sum, Vc, list_sum_range_map, Tc, list_sum_range_map]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.1 hk)).trans ?_
  calc ∑ k ∈ Finset.range (n ^ 14), (t (ℓ + k) : ℝ)
      ≤ ∑ j ∈ Finset.range (ℓ + n ^ 14), (t j : ℝ) := by
        rw [Finset.sum_range_add]; simp only [le_add_iff_nonneg_left]; positivity
    _ ≤ ∑ j ∈ Finset.range (n ^ 14 + n), (t j : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          fun _ _ _ => by positivity
    _ = _ := by simp only [ht]; push_cast; rfl

/-- **Top count ≤ true visits near `0` and near `1`.** -/
theorem Tc_le (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊)
    (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (p : List Bool) (ha : 0 ≤ A p) (hax : A p ≤ x)
    (n : ℕ) (hη : (x - A p) * (b : ℝ) ^ (n ^ 14 + 2 * n) ≤ 1) :
    (Tc Ψ b n p : ℝ) ≤ visitCount (orbit b x) 0 (1 / (b : ℝ) ^ n) (n ^ 14 + n) +
      visitCount (orbit b x) (1 - 1 / (b : ℝ) ^ n) 1 (n ^ 14 + n) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  rw [Tc, list_sum_range_map, visitCount_eq_sum, visitCount_eq_sum]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  by_cases h1 : dA Ψ b j n p = b ^ n - 1
  swap
  · rw [if_neg h1]; split_ifs <;> norm_num
  rw [if_pos h1]
  have hη' : (x - A p) * (b : ℝ) ^ j ≤ 1 / (b : ℝ) ^ n := by
    have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    have hpow : (b : ℝ) ^ j * (b : ℝ) ^ n ≤ (b : ℝ) ^ (n ^ 14 + 2 * n) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hb1 (by omega)
    rw [le_div_iff₀ hbn]
    have h0 : 0 ≤ x - A p := by linarith
    calc (x - A p) * (b : ℝ) ^ j * (b : ℝ) ^ n = (x - A p) * ((b : ℝ) ^ j * (b : ℝ) ^ n) := by ring
      _ ≤ (x - A p) * (b : ℝ) ^ (n ^ 14 + 2 * n) := by gcongr
      _ ≤ 1 := hη
  have htop : ⌊A p * (b : ℝ) ^ (j + n)⌋₊ % b ^ n = b ^ n - 1 := by
    rw [dA, hΨ] at h1; exact h1
  rcases orbit_mem_of_top b hb ha hax j n hη' htop with h | h
  · rw [if_pos h]; split_ifs <;> norm_num
  · rw [if_pos h]; split_ifs <;> norm_num

end Count

/-! ## Probability bounds -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem sqrt_bound_le {n N : ℕ} (hn : 1 ≤ n) (hN : n ^ 14 ≤ N) {K : ℝ} (hK : 0 ≤ K) :
    Real.sqrt (((N : ℝ) + K) / (N : ℝ) ^ 2) ≤ Real.sqrt (1 + K) / (n : ℝ) ^ 7 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNR : ((n : ℝ) ^ 14) ≤ N := by exact_mod_cast hN
  have h14 : (1 : ℝ) ≤ (n : ℝ) ^ 14 := one_le_pow₀ hnR
  have hN1 : (1 : ℝ) ≤ N := h14.trans hNR
  rw [show Real.sqrt (1 + K) / (n : ℝ) ^ 7 = Real.sqrt ((1 + K) / ((n : ℝ) ^ 7) ^ 2) by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : ((n : ℝ) ^ 7) ^ 2 = (n : ℝ) ^ 14 := by ring
  rw [e]
  have : ((N : ℝ) + K) * (n : ℝ) ^ 14 ≤ (1 + K) * (N : ℝ) * N := by
    have a1 := mul_le_mul_of_nonneg_left hNR hK
    have a2 := mul_le_mul_of_nonneg_left hNR (by linarith : (0:ℝ) ≤ N)
    have a3 := mul_le_mul_of_nonneg_left hN1 (mul_nonneg hK (by linarith : (0:ℝ) ≤ N))
    nlinarith
  nlinarith

/-- Block deviation `> 1/(2n)` has probability `≤ 48 √(1+K) / n^5`. -/
theorem block_prob (b : ℕ) (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    {n ℓ v : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hv : v < b ^ ℓ) :
    μ.real {ω | 1 / (2 * (n : ℝ)) <
      |(visitCount (orbit b (G ω)) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (n ^ 14) : ℝ) /
        ((n ^ 14 : ℕ) : ℝ) - 1 / (b : ℝ) ^ ℓ|} ≤ 48 * Real.sqrt (1 + Kc C δ) / (n : ℝ) ^ 5 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hP : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hvR : (v : ℝ) + 1 ≤ (b : ℝ) ^ ℓ := by exact_mod_cast hv
  have hP2 : (2 : ℝ) ≤ (b : ℝ) ^ ℓ := by
    have : 2 ≤ b ^ ℓ := le_trans hb (Nat.le_self_pow (by omega) b)
    exact_mod_cast this
  have hK := Kc_nonneg hC hδ
  have hN1 : 1 ≤ n ^ 14 := Nat.one_le_pow _ _ hn
  have e1 : (v + 1 : ℝ) / (b : ℝ) ^ ℓ - (v : ℝ) / (b : ℝ) ^ ℓ = 1 / (b : ℝ) ^ ℓ := by ring
  have hdev := visit_deviation_b μ b hb G hG hC hδ hdec ((v : ℝ) / (b : ℝ) ^ ℓ)
    ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (1 / (6 * (n : ℝ))) (1 / (6 * (n : ℝ)))
    (by positivity) (by gcongr; linarith) (by rw [div_le_one hP]; exact hvR)
    (by rw [e1, div_le_div_iff₀ hP (by norm_num)]; linarith)
    (by positivity) (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    (by positivity) (n ^ 14) hN1
  rw [e1] at hdev
  have e2 : 2 * (1 / (6 * (n : ℝ))) + 1 / (6 * (n : ℝ)) = 1 / (2 * (n : ℝ)) := by
    field_simp; ring
  rw [e2] at hdev
  refine hdev.trans ?_
  have hsq := sqrt_bound_le (N := n ^ 14) hn (by push_cast; rfl) hK
  push_cast at hsq ⊢
  have e : 2 * (2 / (3 * (1 / (6 * (n : ℝ)))) / (1 / (6 * (n : ℝ)))) = 48 * (n : ℝ) ^ 2 := by
    field_simp; ring
  unfold Kc at hsq ⊢
  rw [← mul_assoc, e]
  calc 48 * (n : ℝ) ^ 2 * Real.sqrt (((n : ℝ) ^ 14 + C * 2 ^ δ * ((1 - 2 ^ (-δ / 2))⁻¹) ^ 2) /
        ((n : ℝ) ^ 14) ^ 2)
      ≤ 48 * (n : ℝ) ^ 2 * (Real.sqrt (1 + C * 2 ^ δ * ((1 - 2 ^ (-δ / 2))⁻¹) ^ 2) /
        (n : ℝ) ^ 7) := by gcongr
    _ = _ := by field_simp

/-- Visits to a short cell `[a, c)`, `c − a ≤ 1/(32n)`, exceeding `n^14/(8n)` among the first
`n^14 + n` points, have probability `≤ 12288 √(1+K) / n^5`. -/
theorem tail_prob (b : ℕ) (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    {n : ℕ} (hn : 1 ≤ n) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (hlen : c - a ≤ 1 / (32 * (n : ℝ))) :
    μ.real {ω | ((n ^ 14 : ℕ) : ℝ) < 8 * n * visitCount (orbit b (G ω)) a c (n ^ 14 + n)} ≤
      12288 * Real.sqrt (1 + Kc C δ) / (n : ℝ) ^ 5 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK := Kc_nonneg hC hδ
  have hN1 : 1 ≤ n ^ 14 + n := by omega
  have hdev := visit_deviation_b μ b hb G hG hC hδ hdec a c (1 / (96 * (n : ℝ)))
    (1 / (96 * (n : ℝ))) ha hac hc (hlen.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith))
    (by positivity) (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    (by positivity) (n ^ 14 + n) hN1
  have hsub : {ω | ((n ^ 14 : ℕ) : ℝ) < 8 * n * visitCount (orbit b (G ω)) a c (n ^ 14 + n)} ⊆
      {ω | 2 * (1 / (96 * (n : ℝ))) + 1 / (96 * (n : ℝ)) <
        |(visitCount (orbit b (G ω)) a c (n ^ 14 + n) : ℝ) / ((n ^ 14 + n : ℕ) : ℝ) - (c - a)|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    set V := (visitCount (orbit b (G ω)) a c (n ^ 14 + n) : ℝ)
    have hN : (0 : ℝ) < ((n ^ 14 + n : ℕ) : ℝ) := by positivity
    have hle : ((n ^ 14 + n : ℕ) : ℝ) ≤ 2 * ((n ^ 14 : ℕ) : ℝ) := by
      push_cast
      have : (n : ℝ) ≤ (n : ℝ) ^ 14 := le_self_pow₀ hnR (by norm_num)
      linarith
    have h1 : 1 / (16 * (n : ℝ)) < V / ((n ^ 14 + n : ℕ) : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hN]
      nlinarith
    have e : 2 * (1 / (96 * (n : ℝ))) + 1 / (96 * (n : ℝ)) = 1 / (32 * (n : ℝ)) := by
      field_simp; ring
    rw [e, lt_abs]; left
    have : 1 / (16 * (n : ℝ)) = 1 / (32 * (n : ℝ)) + 1 / (32 * (n : ℝ)) := by
      field_simp; ring
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hdev.trans ?_)
  have hsq := sqrt_bound_le (N := n ^ 14 + n) hn (by omega) hK
  push_cast at hsq ⊢
  have e : 2 * (2 / (3 * (1 / (96 * (n : ℝ)))) / (1 / (96 * (n : ℝ)))) = 12288 * (n : ℝ) ^ 2 := by
    field_simp; ring
  unfold Kc at hsq ⊢
  rw [← mul_assoc, e]
  calc 12288 * (n : ℝ) ^ 2 * Real.sqrt (((n : ℝ) ^ 14 + n + C * 2 ^ δ * ((1 - 2 ^ (-δ / 2))⁻¹) ^ 2) /
        ((n : ℝ) ^ 14 + n) ^ 2)
      ≤ 12288 * (n : ℝ) ^ 2 * (Real.sqrt (1 + C * 2 ^ δ * ((1 - 2 ^ (-δ / 2))⁻¹) ^ 2) /
        (n : ℝ) ^ 7) := by gcongr
    _ = _ := by field_simp

end Prob

end NormalNumbers.ComputableNormalB
