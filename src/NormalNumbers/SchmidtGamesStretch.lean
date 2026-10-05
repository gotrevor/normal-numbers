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
theorem pot_step (hF : ∀ k, F k ⊆ F (k + 1)) (hr : ∀ k, ∀ i ∈ F k, 2 * r i < 1 / 9 ^ L i)
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
      have hri : 2 * r i < 1 / 9 ^ (k + 1) := lt_of_lt_of_le (hr k i hi)
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
  obtain ⟨j, hj, hg⟩ := h
  unfold pick
  interval_cases j <;> split_ifs <;> simp_all

theorem pick_lt (k X : ℕ) : pick good k X < 4 := by
  unfold pick; split_ifs <;> norm_num

/-- The `n`-th term of `cantorPoint`. -/
noncomputable def term (e : ℕ → Bool) (n : ℕ) : ℝ := (if e n then (2 : ℝ) else 0) / 3 ^ (n + 1)

theorem term_nonneg (e : ℕ → Bool) (n : ℕ) : 0 ≤ term e n := by
  unfold term; split_ifs <;> positivity

theorem term_le (e : ℕ → Bool) (n : ℕ) : term e n ≤ 2 * (1 / 3) ^ (n + 1) := by
  unfold term; rw [one_div_pow, ← div_eq_mul_one_div]
  exact div_le_div_of_nonneg_right (by split_ifs <;> norm_num) (by positivity)

theorem summable_term (e : ℕ → Bool) : Summable (term e) :=
  Summable.of_nonneg_of_le (term_nonneg e) (term_le e)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1) |>.mul_left 2)

theorem sum_term_bits (k : ℕ) :
    ∑ n ∈ range (2 * k), term (bits good) n = (path good k : ℝ) / 9 ^ k := by
  induction k with
  | zero => simp [path]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h0 : (2 * k) % 2 = 0 := by omega
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have d0 : 2 * k / 2 = k := by omega
    have d1 : (2 * k + 1) / 2 = k := by omega
    have hp := pick_lt good k (path good k)
    simp only [term, bits, h0, h1, d0, d1, path]
    generalize pick good k (path good k) = j at hp ⊢
    push_cast
    have e3 : (3 : ℝ) ^ (2 * k + 1 + 1) = 9 ^ (k + 1) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]; ring_nf
    have e2 : (3 : ℝ) ^ (2 * k + 1) = 9 ^ (k + 1) / 3 := by
      rw [← e3]; ring
    rw [e3, e2]
    interval_cases j <;> simp [dig] <;> field_simp <;> ring

theorem cantorPoint_eq (e : ℕ → Bool) (m : ℕ) :
    cantorPoint e = ∑ n ∈ range m, term e n + ∑' n, term e (n + m) :=
  ((summable_term e).sum_add_tsum_nat_add m).symm

theorem tail_le (e : ℕ → Bool) (m : ℕ) : ∑' n, term e (n + m) ≤ 1 / 3 ^ m := by
  have hs : Summable fun n : ℕ => 2 * (1 / 3 : ℝ) ^ (n + m + 1) :=
    ((summable_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (2 * (1 / 3 : ℝ) ^ (m + 1))).congr fun n => by ring
  calc ∑' n, term e (n + m) ≤ ∑' n : ℕ, 2 * (1 / 3 : ℝ) ^ (n + m + 1) :=
        Summable.tsum_le_tsum (fun n => term_le e _)
          ((summable_term e).comp_injective (add_left_injective m)) hs
    _ = 1 / 3 ^ m := by
      rw [show (fun n : ℕ => 2 * (1 / 3 : ℝ) ^ (n + m + 1)) =
          fun n => (2 * (1 / 3) ^ (m + 1)) * (1 / 3 : ℝ) ^ n from funext fun n => by ring,
        tsum_mul_left, tsum_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)]
      rw [one_div_pow]; field_simp; ring

theorem cantorPoint_bits_mem (k : ℕ) :
    cantorPoint (bits good) ∈ Set.Icc ((path good k : ℝ) / 9 ^ k) (((path good k : ℝ) + 1) / 9 ^ k) := by
  rw [cantorPoint_eq _ (2 * k), sum_term_bits]
  have h1 := tail_le (bits good) (2 * k)
  have h2 : 0 ≤ ∑' n, term (bits good) (n + 2 * k) := tsum_nonneg fun n => term_nonneg _ _
  have h3 : (3 : ℝ) ^ (2 * k) = 9 ^ k := by rw [pow_mul]; norm_num
  rw [h3] at h1
  constructor
  · linarith
  · rw [add_div]; linarith

/-- **Avoidance.**  If `good` decides `pot < 1`, the descent point misses every obstacle. -/
theorem cantorPoint_bits_avoid {ι : Type*} (F : ℕ → Finset ι) (c r : ι → ℝ) (L : ι → ℕ)
    (hF : ∀ k, F k ⊆ F (k + 1)) (hr : ∀ k, ∀ i ∈ F k, 2 * r i < 1 / 9 ^ L i)
    (hnew : ∀ k X, newPot F c r L k X ≤ 1 / 2) (h0 : pot F c r L 0 0 < 1)
    (hgood : ∀ k X, good k X = true ↔ pot F c r L k X < 1) {k : ℕ} {i : ι} (hi : i ∈ F k) :
    cantorPoint (bits good) ∉ Set.Icc (c i - r i) (c i + r i) := by
  classical
  have inv : ∀ k, pot F c r L k (path good k) < 1 := by
    intro k
    induction k with
    | zero => simpa [path] using h0
    | succ k ih =>
      obtain ⟨j, hj, hpj⟩ := pot_step F c r L hF hr hnew ih
      have := pick_good good ⟨j, hj, (hgood _ _).mpr hpj⟩
      exact (hgood _ _).mp this
  have hmono : ∀ m, F k ⊆ F (k + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => exact ih.trans (hF _)
  intro hx
  set K := k + L i
  have hiK : i ∈ F K := hmono _ hi
  have hm : Meets c r i K (path good K) := by
    have := cantorPoint_bits_mem good K
    exact ⟨hx.1.trans this.2, this.1.trans hx.2⟩
  have hge : (2 : ℝ) ^ ((K : ℤ) - L i) ≤ pot F c r L K (path good K) := by
    unfold pot
    exact Finset.single_le_sum (f := fun i => (2 : ℝ) ^ ((K : ℤ) - L i))
      (fun _ _ => by positivity) (Finset.mem_filter.mpr ⟨hiK, hm⟩)
  have h1 : (1 : ℝ) ≤ 2 ^ ((K : ℤ) - L i) :=
    one_le_zpow₀ (by norm_num) (by simp [K])
  linarith [inv K]

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

theorem pow_lt_of_stU {b n k : ℕ} (hb : 2 ≤ b) (h : stU b n ≤ k) : b ^ n < 9 ^ k :=
  lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
    (Nat.pow_le_pow_right (by norm_num) h)

theorem sq_lt_of_stB {q k : ℕ} (h : stB q ≤ k) : q ^ 2 < 9 ^ (k - 1) :=
  lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
    (Nat.pow_le_pow_right (by norm_num) (by unfold stB at h; omega))

theorem mem_FF_inl {k : ℕ} {x : ℕ × ℕ × ℕ} : Sum.inl x ∈ FF k ↔ ValidU x ∧ stU x.1 x.2.1 ≤ k := by
  obtain ⟨b, n, a⟩ := x
  simp only [FF, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨hv, hs⟩
    obtain ⟨hb, hn, ha⟩ := hv
    simp only at hb hn ha hs ⊢
    have hlt := pow_lt_of_stU hb hs
    have hk : 1 ≤ k := le_trans (by unfold stU; omega) hs
    refine ⟨⟨?_, ?_, by omega⟩, ⟨hb, hn, ha⟩, hs⟩
    · rcases hn with hn | hn
      · exact lt_of_le_of_lt (Nat.le_self_pow (by omega) b) hlt
      · subst hn; calc 2 < 9 ^ 1 := by norm_num
          _ ≤ 9 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    · have h1 : 2 ^ n < 2 ^ (4 * k) := by
        calc 2 ^ n ≤ b ^ n := Nat.pow_le_pow_left hb n
          _ < 9 ^ k := hlt
          _ ≤ 16 ^ k := Nat.pow_le_pow_left (by norm_num) k
          _ = 2 ^ (4 * k) := by rw [pow_mul]; norm_num
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
      omega

theorem mem_FF_inr {k : ℕ} {x : ℕ × ℕ} : Sum.inr x ∈ FF k ↔ ValidB x ∧ stB x.2 ≤ k := by
  obtain ⟨p, q⟩ := x
  simp only [FF, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨hv, hs⟩
    have h1 := sq_lt_of_stB hs
    have h2 : q ^ 2 < (3 ^ k) ^ 2 := by
      calc q ^ 2 < 9 ^ (k - 1) := h1
        _ ≤ 9 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (3 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hq := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
    exact ⟨⟨by have := hv.2.1; simp only at this; omega, hq⟩, hv, hs⟩

theorem FF_mono (k : ℕ) : FF k ⊆ FF (k + 1) := by
  intro i hi
  rcases i with x | x
  · rw [mem_FF_inl] at hi ⊢; exact ⟨hi.1, by omega⟩
  · rw [mem_FF_inr] at hi ⊢; exact ⟨hi.1, by omega⟩

theorem nat_rad_inl {b n : ℕ} (hb : 2 ≤ b) :
    2 * 9 ^ (stU b n + (8 + 2 * Nat.log 2 b)) < b ^ (n + 40) := by
  have h1 : 9 ^ stU b n ≤ 9 * b ^ n := by
    unfold stU; rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 9 (by positivity))
  have h2 : 9 ^ (2 * Nat.log 2 b) ≤ b ^ 7 := by
    calc 9 ^ (2 * Nat.log 2 b) = 81 ^ Nat.log 2 b := by rw [pow_mul]; norm_num
      _ ≤ 128 ^ Nat.log 2 b := Nat.pow_le_pow_left (by norm_num) _
      _ = (2 ^ Nat.log 2 b) ^ 7 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ b ^ 7 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) 7
  have h3 : 2 ^ 33 ≤ b ^ 33 := Nat.pow_le_pow_left hb 33
  have hbn : 0 < b ^ n := by positivity
  have hb7 : 0 < b ^ 7 := by positivity
  calc 2 * 9 ^ (stU b n + (8 + 2 * Nat.log 2 b))
      = 2 * 9 ^ 8 * (9 ^ stU b n * 9 ^ (2 * Nat.log 2 b)) := by ring
    _ ≤ 2 * 9 ^ 8 * (9 * b ^ n * b ^ 7) := by gcongr
    _ = (18 * 9 ^ 8) * (b ^ n * b ^ 7) := by ring
    _ < 2 ^ 33 * (b ^ n * b ^ 7) := by
        apply Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ ≤ b ^ 33 * (b ^ n * b ^ 7) := by gcongr
    _ = b ^ (n + 40) := by ring

theorem nat_rad_inr (q : ℕ) (hq : 1 ≤ q) : 2 * 9 ^ (stB q + 2) < 9 ^ 5 * q ^ 2 := by
  have h1 : 9 ^ Nat.log 9 (q ^ 2) ≤ q ^ 2 := Nat.pow_log_le_self 9 (by positivity)
  have hq2 : 0 < q ^ 2 := by positivity
  unfold stB
  calc 2 * 9 ^ (Nat.log 9 (q ^ 2) + 2 + 2) = 2 * 9 ^ 4 * 9 ^ Nat.log 9 (q ^ 2) := by ring
    _ ≤ 2 * 9 ^ 4 * q ^ 2 := by gcongr
    _ < 9 ^ 5 * q ^ 2 := by apply Nat.mul_lt_mul_of_pos_right (by norm_num) hq2

/-- The radius-level inequality holds for valid obstacles (all others are never charged). -/
theorem rad_lt_of_mem {i : Idx} {k : ℕ} (hi : i ∈ FF k) : 2 * rad i < 1 / 9 ^ lev i := by
  rcases i with ⟨b, n, a⟩ | ⟨p, q⟩
  · obtain ⟨⟨hb, -, -⟩, -⟩ := mem_FF_inl.mp hi
    have h := nat_rad_inl (n := n) hb
    have hR : (2 : ℝ) * 9 ^ (stU b n + (8 + 2 * Nat.log 2 b)) < (b : ℝ) ^ (n + 40) := by
      exact_mod_cast h
    simp only [rad, lev]
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  · obtain ⟨⟨hq, -, -⟩, -⟩ := mem_FF_inr.mp hi
    have h := nat_rad_inr q hq
    have hR : (2 : ℝ) * 9 ^ (stB q + 2) < 9 ^ 5 * (q : ℝ) ^ 2 := by exact_mod_cast h
    simp only [rad, lev]
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith

/-- **The counting lemma**: newly charged potential of any window is `≤ 1/2`
(`≤ 1/8` from all bases, `≤ 1/4` from the one possible rational). -/
theorem newPot_FF_le (k X : ℕ) : newPot FF ctr rad lev k X ≤ 1 / 2 := by
  sorry

theorem FF_zero : FF 0 = ∅ := by
  ext i
  simp only [Finset.notMem_empty, iff_false]
  intro hi
  rcases i with x | x
  · have := (mem_FF_inl.mp hi).2; unfold stU at this; omega
  · have := (mem_FF_inr.mp hi).2; unfold stB at this; omega

theorem pot_FF_zero : pot FF ctr rad lev 0 0 < 1 := by
  simp [pot, FF_zero]

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
  cantorPoint_bits_avoid goodNat FF ctr rad lev FF_mono (fun _ _ hi => rad_lt_of_mem hi) newPot_FF_le pot_FF_zero
    goodNat_iff hi

theorem cantorPoint_eBob_mem_Icc : cantorPoint eBob ∈ Set.Icc 0 1 := by
  simpa [path, eBob] using cantorPoint_bits_mem goodNat 0

theorem cantorPoint_eBob_dnear {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n ∨ b = 2) :
    1 / (b : ℝ) ^ 40 < UniformBad.dnear ((b : ℝ) ^ n * cantorPoint eBob) := by
  set ξ := cantorPoint eBob
  obtain ⟨hξ0, hξ1⟩ := cantorPoint_eBob_mem_Icc
  by_contra hcon
  push Not at hcon
  set z := round ((b : ℝ) ^ n * ξ)
  have hz : |(b : ℝ) ^ n * ξ - z| ≤ 1 / (b : ℝ) ^ 40 := hcon
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hB : (1 : ℝ) / (b : ℝ) ^ 40 < 1 := by
    rw [div_lt_one (by positivity)]
    calc (1 : ℝ) < 2 ^ 40 := by norm_num
      _ ≤ (b : ℝ) ^ 40 := by gcongr
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hz' := abs_le.mp hz
  have hz0 : (0 : ℤ) ≤ z := by
    have : (-1 : ℝ) < z := by nlinarith
    exact_mod_cast (show (-1 : ℤ) < z by exact_mod_cast this)
  have hzb : z ≤ ((b ^ n : ℕ) : ℤ) := by
    have : (z : ℝ) < (b : ℝ) ^ n + 1 := by nlinarith
    have : z < ((b ^ n : ℕ) : ℤ) + 1 := by push_cast; exact_mod_cast this
    omega
  set a := z.toNat
  have ha : (a : ℝ) = z := by
    have : (a : ℤ) = z := Int.toNat_of_nonneg hz0
    exact_mod_cast this
  have hmem : Sum.inl (b, n, a) ∈ FF (stU b n) :=
    mem_FF_inl.mpr ⟨⟨hb, hn, by simp only; omega⟩, le_rfl⟩
  apply cantorPoint_eBob_avoid hmem
  simp only [ctr, rad]
  have key : |ξ - a / (b : ℝ) ^ n| ≤ 1 / (b : ℝ) ^ (n + 40) := by
    rw [ha, show ξ - z / (b : ℝ) ^ n = ((b : ℝ) ^ n * ξ - z) / (b : ℝ) ^ n by field_simp,
      abs_div, abs_of_pos hbn, pow_add, div_le_iff₀ hbn]
    calc |(b : ℝ) ^ n * ξ - z| ≤ 1 / (b : ℝ) ^ 40 := hz
      _ = 1 / ((b : ℝ) ^ n * (b : ℝ) ^ 40) * (b : ℝ) ^ n := by field_simp
  rw [abs_le] at key
  constructor <;> linarith [key.1, key.2]

theorem cantorPoint_eBob_mem_E : cantorPoint eBob ∈ E 40 := by
  intro b hb n
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hr : (b : ℝ) ^ (-(40 : ℝ)) = 1 / (b : ℝ) ^ 40 := by
    rw [Real.rpow_neg (by positivity), one_div]; norm_cast
  rw [hr]
  by_cases h : 1 ≤ n ∨ b = 2
  · exact cantorPoint_eBob_dnear hb h
  · push Not at h
    obtain ⟨hn, -⟩ := h
    have hn0 : n = 0 := by omega
    subst hn0
    have := cantorPoint_eBob_dnear (b := 2) (n := 0) le_rfl (Or.inr rfl)
    simp only [pow_zero, one_mul, Nat.cast_ofNat] at this ⊢
    exact lt_of_le_of_lt (by gcongr) this

theorem cantorPoint_eBob_mem_BA : cantorPoint eBob ∈ BA (1 / 9 ^ 5) := by
  intro p q hq
  set ξ := cantorPoint eBob
  obtain ⟨hξ0, hξ1⟩ := cantorPoint_eBob_mem_Icc
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hsmall : (1 / 9 ^ 5 : ℝ) / (q : ℝ) ^ 2 < 1 / q := by
    rw [div_lt_div_iff₀ (by positivity) hq0]; nlinarith
  by_cases hp0 : p < 0
  · have hp1 : p ≤ -1 := by omega
    have hp1R : (p : ℝ) ≤ -1 := by exact_mod_cast hp1
    have : (p : ℝ) / q ≤ -1 / q := div_le_div_of_nonneg_right hp1R hq0.le
    rw [abs_of_pos (by have := div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) hq0; linarith)]
    have : -1 / (q : ℝ) = -(1 / q) := by ring
    linarith
  by_cases hpq : (q : ℤ) < p
  · have hp1 : (q : ℝ) + 1 ≤ p := by exact_mod_cast hpq
    have : (1 : ℝ) + 1 / q ≤ p / q := by
      rw [le_div_iff₀ hq0]; field_simp; linarith
    have : (0 : ℝ) < 1 / q := by positivity
    rw [abs_of_neg (by linarith)]
    linarith
  push Not at hp0 hpq
  -- reduce to lowest terms
  set m := p.toNat
  have hm : (m : ℤ) = p := Int.toNat_of_nonneg hp0
  have hmq : m ≤ q := by omega
  set g := Nat.gcd m q
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hq
  set m₀ := m / g
  set q₀ := q / g
  have hcop : Nat.Coprime m₀ q₀ := Nat.coprime_div_gcd_div_gcd hg
  have hmg : m₀ * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m q)
  have hqg : q₀ * g = q := Nat.div_mul_cancel (Nat.gcd_dvd_right m q)
  have hq₀ : 1 ≤ q₀ := by
    rcases Nat.eq_zero_or_pos q₀ with h | h
    · rw [h, zero_mul] at hqg; omega
    · exact h
  have hm₀ : m₀ ≤ q₀ := by
    by_contra h; push Not at h
    have := Nat.mul_lt_mul_of_pos_right h hg; omega
  have hmem : Sum.inr (m₀, q₀) ∈ FF (stB q₀) :=
    mem_FF_inr.mpr ⟨⟨hq₀, hm₀, hcop⟩, le_rfl⟩
  have hav := cantorPoint_eBob_avoid hmem
  simp only [ctr, rad, Set.mem_Icc, not_and_or, not_le] at hav
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hq₀R : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
  have hval : (p : ℝ) / q = (m₀ : ℝ) / q₀ := by
    rw [← hm, ← hmg, ← hqg]; push_cast; field_simp
  have hle : (1 / 9 ^ 5 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (9 ^ 5 * (q₀ : ℝ) ^ 2) := by
    rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have : (q₀ : ℝ) ≤ q := by rw [← hqg]; push_cast; nlinarith
    gcongr
  rw [hval]
  have hpos : (0 : ℝ) < 1 / (9 ^ 5 * (q₀ : ℝ) ^ 2) := by positivity
  rcases hav with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

end Stretch

/-- **Stretch conjecture.**  A computable point of `U ∩ Bad` in the middle-third Cantor set. -/
theorem exists_computable_cantorPoint_mem_U_inter_Bad :
    ∃ e : ℕ → Bool, Computable e ∧ cantorPoint e ∈ U ∩ Bad :=
  ⟨Stretch.eBob, Stretch.computable_eBob, E_subset_U 40 Stretch.cantorPoint_eBob_mem_E,
    Set.mem_iUnion₂.mpr ⟨1 / 9 ^ 5, by norm_num, Stretch.cantorPoint_eBob_mem_BA⟩⟩

end NormalNumbers.SchmidtGames
