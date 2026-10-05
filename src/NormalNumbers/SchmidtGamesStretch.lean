/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SchmidtGames
import Mathlib.Computability.Partrec

/-!
# Stretch: a computable point of `U ∩ BAD` in the middle-third Cantor set

Kept apart from `SchmidtGames.lean`: a stretch conjecture, not a frozen headline.

**Context.**  Temur, *Simultaneously small continued fraction entropy and base `b` entropy*,
arXiv:2609.16362 (14 Sep 2026), answering Bugeaud 2012 Problem 10.53, constructs a COMPUTABLE
irrational `ξ` with `‖bᵏξ‖ > δ_b := 154^{−2^b}` for every `b ≥ 2`, `k ≥ 0`, a doubly
exponential bound.  `UniformBad.bugeaud_10_36` gives `b^{−24}`, a polynomial bound, with no
computability claim.

**Conjecture.**  Some computable `e : ℕ → Bool` gives a point `Σ 2·e(n)·3^{−(n+1)}` of the
middle-third Cantor set lying in `U ∩ Bad`: polynomial `b^{−C}` for every base, badly
approximable, Cantor, and computable at once.

**Mechanism.**  Play the BFS potential game with a computable Bob: Bob descends through triadic
Cantor intervals and picks a child whose potential (Alice's deletions from `potentialWinning_E`
and BFS Lemma 3.11 (print; arXiv v3: 3.10), weighted as in BFS §5) stays below threshold.  The potentials are infinite
sums over bases, computable to any precision from explicit tails `Σ_{b > B} b^{−C/2}`.  So Bob
compares rational over-approximations with a margin; the averaging step in BFS Theorem 5.5
leaves room for that margin.  Known-false sibling it must fail on: the same descent with
target "normal in base 2" (`not_potentialWinning_isNormal`).

Confidence: true 75%; Lean 25% (several laps, after headline 1).
-/

namespace NormalNumbers.SchmidtGames

/-- The point of the middle-third Cantor set with ternary digits `2·e(n)`. -/
noncomputable def cantorPoint (e : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, (if e n then (2 : ℝ) else 0) / 3 ^ (n + 1)

/-! ## A decidable descent

The route actually formalized (not the BFS game above): a direct descent through base-`9`
Cantor cylinders `[X/9ᵏ, (X+1)/9ᵏ]` (digits `0, 2, 6, 8`, i.e. two ternary Cantor digits per
step), with a *dyadic* potential `Φ_k = Σ 2^{k − L i}` over the charged obstacles meeting the
cylinder.  Each obstacle `i` carries a level `L i` with `2 r_i < 9^{−L i}`; while `Φ_k < 1` every
carried obstacle has `L i > k`, so it meets at most one of the four children (sibling gaps are
`≥ 9^{−(k+1)}`), where its weight doubles.  Hence `Σ_children Φ ≤ 2Φ_k + 4·(new) < 4` when the
newly charged potential of every stage-`k` window is `≤ 1/2`, and some child keeps `Φ < 1`.
All weights are dyadic rationals and each `Φ_k` is a finite sum, so Bob's test `Φ < 1` is a
comparison of natural numbers: the descent is primitive recursive. -/

namespace Stretch

open Finset

/-- The base-`9` Cantor digits `0, 2, 6, 8` (for `j < 4`). -/
def dig (j : ℕ) : ℕ := 6 * (j / 2) + 2 * (j % 2)

section Engine

variable {ι : Type*} (F : ℕ → Finset ι) (c r : ι → ℝ) (L : ι → ℕ)

/-- Obstacle `i` (the closed interval `[c i − r i, c i + r i]`) meets `[X/9ᵏ, (X+1)/9ᵏ]`. -/
def Meets (i : ι) (k X : ℕ) : Prop :=
  c i - r i ≤ ((X : ℝ) + 1) / 9 ^ k ∧ (X : ℝ) / 9 ^ k ≤ c i + r i

open Classical in
/-- The dyadic potential of the cylinder `(k, X)`. -/
noncomputable def pot (k X : ℕ) : ℝ :=
  ∑ i ∈ (F k).filter (fun i => Meets c r i k X), (2 : ℝ) ^ ((k : ℤ) - L i)

open Classical in
/-- The newly charged potential of the stage-`k+1` window `X`. -/
noncomputable def newPot (k X : ℕ) : ℝ :=
  ∑ i ∈ (F (k + 1) \ F k).filter (fun i => Meets c r i (k + 1) X),
    (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - L i)

theorem dig_le {j : ℕ} (hj : j < 4) : dig j ≤ 8 := by
  unfold dig; interval_cases j <;> norm_num

theorem meets_parent {i : ι} {k X j : ℕ} (hj : j < 4) (h : Meets c r i (k + 1) (9 * X + dig j)) :
    Meets c r i k X := by
  have hd : (dig j : ℝ) ≤ 8 := by exact_mod_cast dig_le hj
  have h9 : (0 : ℝ) < 9 ^ k := by positivity
  obtain ⟨h1, h2⟩ := h
  push_cast at h1 h2
  rw [pow_succ] at h1 h2
  refine ⟨h1.trans ?_, le_trans ?_ h2⟩
  · rw [div_le_div_iff₀ (by positivity) h9]; nlinarith
  · rw [div_le_div_iff₀ h9 (by positivity)]; nlinarith

theorem meets_unique {i : ι} {k X j j' : ℕ} (hj : j < 4) (hj' : j' < 4)
    (hr : 2 * r i < 1 / 9 ^ (k + 1)) (h : Meets c r i (k + 1) (9 * X + dig j))
    (h' : Meets c r i (k + 1) (9 * X + dig j')) : j = j' := by
  by_contra hne
  have h9 : (0 : ℝ) < 9 ^ (k + 1) := by positivity
  -- WLOG-free: the digits of distinct children differ by at least 2
  have key : ∀ a b : ℕ, a < 4 → b < 4 → a ≠ b → Meets c r i (k + 1) (9 * X + dig a) →
      Meets c r i (k + 1) (9 * X + dig b) → dig a < dig b → False := by
    intro a b ha hb _ hA hB hlt
    have h2 : dig a + 2 ≤ dig b := by
      unfold dig at hlt ⊢; interval_cases a <;> interval_cases b <;> omega
    have h2' : (dig a : ℝ) + 2 ≤ dig b := by exact_mod_cast h2
    obtain ⟨hA2, -⟩ := hA
    obtain ⟨-, hB1⟩ := hB
    push_cast at hA2 hB1
    have : ((9 * X + dig b : ℝ)) / 9 ^ (k + 1) - ((9 * X + dig a : ℝ) + 1) / 9 ^ (k + 1)
        ≤ 2 * r i := by linarith
    rw [← sub_div] at this
    have : 1 / (9 : ℝ) ^ (k + 1) ≤ 2 * r i :=
      le_trans (div_le_div_of_nonneg_right (by linarith) h9.le) this
    linarith
  rcases lt_trichotomy (dig j) (dig j') with hlt | heq | hgt
  · exact key j j' hj hj' hne h h' hlt
  · apply hne; unfold dig at heq; interval_cases j <;> interval_cases j' <;> omega
  · exact key j' j hj' hj (Ne.symm hne) h' h hgt

open Classical in
theorem pot_split (hF : ∀ k, F k ⊆ F (k + 1)) (k Y : ℕ) :
    pot F c r L (k + 1) Y = (∑ i ∈ F k, if Meets c r i (k + 1) Y then
      (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - L i) else 0) + newPot F c r L k Y := by
  unfold pot newPot
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sdiff (hF k), add_comm]

/-- **Engine step.** -/
theorem pot_step (hF : ∀ k, F k ⊆ F (k + 1)) (hr : ∀ i, 2 * r i < 1 / 9 ^ L i)
    (hnew : ∀ k X, newPot F c r L k X ≤ 1 / 2) {k X : ℕ} (h : pot F c r L k X < 1) :
    ∃ j < 4, pot F c r L (k + 1) (9 * X + dig j) < 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum4 : (4 : ℝ) ≤ ∑ j ∈ range 4, pot F c r L (k + 1) (9 * X + dig j) := by
    have := Finset.card_nsmul_le_sum (range 4) (fun j => pot F c r L (k + 1) (9 * X + dig j)) 1
      (fun j hj => hcon j (Finset.mem_range.mp hj))
    simpa using this
  -- per-obstacle bound on the old part
  have hper : ∀ i ∈ F k, (∑ j ∈ range 4, if Meets c r i (k + 1) (9 * X + dig j) then
      (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - L i) else 0) ≤
      2 * (if Meets c r i k X then (2 : ℝ) ^ ((k : ℤ) - L i) else 0) := by
    intro i hi
    by_cases hm : Meets c r i k X
    · rw [if_pos hm]
      have hw : (2 : ℝ) ^ ((k : ℤ) - L i) < 1 := by
        refine lt_of_le_of_lt ?_ h
        unfold pot
        exact Finset.single_le_sum (f := fun i => (2 : ℝ) ^ ((k : ℤ) - L i))
          (fun _ _ => by positivity) (Finset.mem_filter.mpr ⟨hi, hm⟩)
      have hL : k + 1 ≤ L i := by
        by_contra hL
        have : (0 : ℤ) ≤ (k : ℤ) - L i := by omega
        have := one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2) this
        linarith
      have hri : 2 * r i < 1 / 9 ^ (k + 1) := lt_of_lt_of_le (hr i)
        (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hL))
      have hcard : ((range 4).filter (fun j => Meets c r i (k + 1) (9 * X + dig j))).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          simp only [Finset.mem_filter, Finset.mem_range] at ha hb
          exact meets_unique c r hb.1 ha.1 hri hb.2 ha.2 |>.symm
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hz : (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - L i) = 2 * 2 ^ ((k : ℤ) - L i) := by
        rw [show (((k + 1 : ℕ) : ℤ) - L i) = 1 + ((k : ℤ) - L i) by push_cast; ring,
          zpow_add₀ (by norm_num), zpow_one]
      rw [hz]
      have : ((((range 4).filter (fun j => Meets c r i (k + 1) (9 * X + dig j))).card : ℕ) : ℝ)
          ≤ 1 := by exact_mod_cast hcard
      have hp : (0 : ℝ) ≤ 2 * 2 ^ ((k : ℤ) - L i) := by positivity
      nlinarith
    · rw [if_neg hm, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun j hj => if_neg fun h' => hm ?_)
      exact meets_parent c r (Finset.mem_range.mp hj) h'
  have hold : (∑ j ∈ range 4, ∑ i ∈ F k, if Meets c r i (k + 1) (9 * X + dig j) then
      (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - L i) else 0) ≤ 2 * pot F c r L k X := by
    rw [Finset.sum_comm]
    unfold pot
    rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_le_sum hper
  have hnew4 : ∑ j ∈ range 4, newPot F c r L k (9 * X + dig j) ≤ 2 := by
    have := Finset.sum_le_card_nsmul (range 4) (fun j => newPot F c r L k (9 * X + dig j)) (1 / 2)
      (fun j _ => hnew k _)
    simp at this; linarith
  simp_rw [pot_split F c r L hF] at hsum4
  rw [Finset.sum_add_distrib] at hsum4
  linarith

end Engine

section Descent

variable (good : ℕ → ℕ → Bool)

/-- Bob's choice: the first child passing `good`. -/
def pick (k X : ℕ) : ℕ :=
  if good (k + 1) (9 * X + dig 0) then 0 else if good (k + 1) (9 * X + dig 1) then 1
  else if good (k + 1) (9 * X + dig 2) then 2 else 3

/-- The numerators of the chosen cylinders. -/
def path : ℕ → ℕ
  | 0 => 0
  | k + 1 => 9 * path k + dig (pick good k (path k))

/-- The ternary Cantor bits of the descent. -/
def bits (n : ℕ) : Bool :=
  if n % 2 = 0 then decide (2 ≤ pick good (n / 2) (path good (n / 2)))
  else decide (pick good (n / 2) (path good (n / 2)) % 2 = 1)

theorem pick_good {k X : ℕ} (h : ∃ j < 4, good (k + 1) (9 * X + dig j) = true) :
    good (k + 1) (9 * X + dig (pick good k X)) = true := by
  sorry

theorem cantorPoint_bits_mem (k : ℕ) :
    cantorPoint (bits good) ∈ Set.Icc ((path good k : ℝ) / 9 ^ k) (((path good k : ℝ) + 1) / 9 ^ k) := by
  sorry

/-- **Avoidance.**  If `good` decides `pot < 1`, the descent point misses every obstacle. -/
theorem cantorPoint_bits_avoid {ι : Type*} (F : ℕ → Finset ι) (c r : ι → ℝ) (L : ι → ℕ)
    (hF : ∀ k, F k ⊆ F (k + 1)) (hr : ∀ i, 2 * r i < 1 / 9 ^ L i)
    (hnew : ∀ k X, newPot F c r L k X ≤ 1 / 2) (h0 : pot F c r L 0 0 < 1)
    (hgood : ∀ k X, good k X = true ↔ pot F c r L k X < 1) {k : ℕ} {i : ι} (hi : i ∈ F k) :
    cantorPoint (bits good) ∉ Set.Icc (c i - r i) (c i + r i) := by
  sorry

end Descent

/-! ### The obstacles of `E 40 ∩ BA 9⁻⁵` -/

/-- Index: `inl (b, n, a)` is `|ξ − a/bⁿ| ≤ b^{−n−40}`; `inr (p, q)` is `|ξ − p/q| ≤ 9⁻⁵/q²`. -/
abbrev Idx := (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ)

/-- Stage of a base-`b`, level-`n` obstacle: `9^{st−1} ≤ bⁿ < 9^{st}` (early charging). -/
def stU (b n : ℕ) : ℕ := Nat.log 9 (b ^ n) + 1

/-- Stage of a denominator-`q` obstacle: `9^{st−2} ≤ q² < 9^{st−1}`. -/
def stB (q : ℕ) : ℕ := Nat.log 9 (q ^ 2) + 2

def lev : Idx → ℕ
  | .inl (b, n, _) => stU b n + (8 + 2 * Nat.log 2 b)
  | .inr (_, q) => stB q + 2

def stage : Idx → ℕ
  | .inl (b, n, _) => stU b n
  | .inr (_, q) => stB q

noncomputable def ctr : Idx → ℝ
  | .inl (b, n, a) => (a : ℝ) / (b : ℝ) ^ n
  | .inr (p, q) => (p : ℝ) / q

noncomputable def rad : Idx → ℝ
  | .inl (b, n, _) => 1 / (b : ℝ) ^ (n + 40)
  | .inr (_, q) => 1 / (9 ^ 5 * (q : ℝ) ^ 2)

def ValidU (x : ℕ × ℕ × ℕ) : Prop := 2 ≤ x.1 ∧ (1 ≤ x.2.1 ∨ x.1 = 2) ∧ x.2.2 ≤ x.1 ^ x.2.1

def ValidB (x : ℕ × ℕ) : Prop := 1 ≤ x.2 ∧ x.1 ≤ x.2 ∧ Nat.Coprime x.1 x.2

instance (x : ℕ × ℕ × ℕ) : Decidable (ValidU x) := by unfold ValidU; infer_instance
instance (x : ℕ × ℕ) : Decidable (ValidB x) := by unfold ValidB; infer_instance

/-- The obstacles charged by stage `k`, as a finite box. -/
def FF (k : ℕ) : Finset Idx :=
  ((range (9 ^ k) ×ˢ range (4 * k + 1) ×ˢ range (9 ^ k + 1)).filter
      (fun x => ValidU x ∧ stU x.1 x.2.1 ≤ k)).disjSum
    ((range (3 ^ k) ×ˢ range (3 ^ k)).filter (fun x => ValidB x ∧ stB x.2 ≤ k))

theorem mem_FF_inl {k : ℕ} {x : ℕ × ℕ × ℕ} : Sum.inl x ∈ FF k ↔ ValidU x ∧ stU x.1 x.2.1 ≤ k := by
  sorry

theorem mem_FF_inr {k : ℕ} {x : ℕ × ℕ} : Sum.inr x ∈ FF k ↔ ValidB x ∧ stB x.2 ≤ k := by
  sorry

theorem FF_mono (k : ℕ) : FF k ⊆ FF (k + 1) := by
  sorry

theorem rad_lt (i : Idx) : 2 * rad i < 1 / 9 ^ lev i := by
  sorry

/-- **The counting lemma**: newly charged potential of any window is `≤ 1/2`
(`≤ 1/8` from all bases, `≤ 1/4` from the one possible rational). -/
theorem newPot_FF_le (k X : ℕ) : newPot FF ctr rad lev k X ≤ 1 / 2 := by
  sorry

theorem pot_FF_zero : pot FF ctr rad lev 0 0 < 1 := by
  sorry

/-! ### Bob's test in natural numbers -/

/-- Obstacle `i` meets the cylinder `(k, X)`, cross-multiplied into `ℕ`. -/
def MeetsNat : Idx → ℕ → ℕ → Prop
  | .inl (b, n, a), k, X =>
      (a * b ^ 40 - 1) * 9 ^ k ≤ (X + 1) * b ^ (n + 40) ∧ X * b ^ (n + 40) ≤ (a * b ^ 40 + 1) * 9 ^ k
  | .inr (p, q), k, X =>
      (9 ^ 5 * p * q - 1) * 9 ^ k ≤ (X + 1) * (9 ^ 5 * q ^ 2) ∧
        X * (9 ^ 5 * q ^ 2) ≤ (9 ^ 5 * p * q + 1) * 9 ^ k

instance (i : Idx) (k X : ℕ) : Decidable (MeetsNat i k X) := by
  rcases i with ⟨b, n, a⟩ | ⟨p, q⟩ <;> unfold MeetsNat <;> infer_instance

/-- Bob's test: `Φ_k < 1`, scaled by `2^{9k+8}`. -/
def goodNat (k X : ℕ) : Bool :=
  decide ((∑ i ∈ (FF k).filter (fun i => MeetsNat i k X), 2 ^ (10 * k + 8 - lev i)) < 2 ^ (9 * k + 8))

theorem goodNat_iff (k X : ℕ) : goodNat k X = true ↔ pot FF ctr rad lev k X < 1 := by
  sorry

theorem primrec_goodNat : Primrec₂ goodNat := by
  sorry

/-- The descent's digits. -/
def eBob : ℕ → Bool := bits goodNat

theorem computable_eBob : Computable eBob := by
  sorry

theorem cantorPoint_eBob_avoid {i : Idx} {k : ℕ} (hi : i ∈ FF k) :
    cantorPoint eBob ∉ Set.Icc (ctr i - rad i) (ctr i + rad i) :=
  cantorPoint_bits_avoid goodNat FF ctr rad lev FF_mono rad_lt newPot_FF_le pot_FF_zero
    goodNat_iff hi

theorem cantorPoint_eBob_mem_E : cantorPoint eBob ∈ E 40 := by
  sorry

theorem cantorPoint_eBob_mem_BA : cantorPoint eBob ∈ BA (1 / 9 ^ 5) := by
  sorry

end Stretch

/-- **Stretch conjecture.**  A computable point of `U ∩ Bad` in the middle-third Cantor set. -/
theorem exists_computable_cantorPoint_mem_U_inter_Bad :
    ∃ e : ℕ → Bool, Computable e ∧ cantorPoint e ∈ U ∩ Bad :=
  ⟨Stretch.eBob, Stretch.computable_eBob, E_subset_U 40 Stretch.cantorPoint_eBob_mem_E,
    Set.mem_iUnion₂.mpr ⟨1 / 9 ^ 5, by norm_num, Stretch.cantorPoint_eBob_mem_BA⟩⟩

end NormalNumbers.SchmidtGames
