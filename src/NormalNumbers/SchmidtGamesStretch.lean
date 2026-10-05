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

**Status: PROVED** (2026-10-05), by a different mechanism than the BFS game sketched above: the
decidable dyadic-potential descent below (`Stretch`), with explicit constants.  The point lies in
`E 40 ∩ BA 9⁻⁵` (`Stretch.cantorPoint_eBob_mem_E`, `Stretch.cantorPoint_eBob_mem_BA`), i.e.
`‖bⁿξ‖ > b^{−40}` for every base `b ≥ 2` and `n ≥ 0`, against Temur's `154^{−2^b}`; Bob's choice
is a primitive recursive comparison of natural numbers (`Stretch.primrec_goodNat`).  No literature
hypothesis is used: the badly-approximable half is handled directly (one rational per window, by the
simplex lemma `Stretch.bad_unique`), not via `Literature.BFSBadPotential`.
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
theorem card_le_of_spread (T : Finset ℕ) (d : ℕ) (h : ∀ x ∈ T, ∀ y ∈ T, x ≤ y → y ≤ x + d) :
    T.card ≤ d + 1 := by
  rcases T.eq_empty_or_nonempty with hT | hT
  · simp [hT]
  · have hsub : T ⊆ Finset.Icc (T.min' hT) (T.min' hT + d) := fun y hy =>
      Finset.mem_Icc.mpr ⟨T.min'_le y hy, h _ (T.min'_mem hT) y hy (T.min'_le y hy)⟩
    have := Finset.card_le_card hsub
    simp at this; omega

/-- Stage facts for a base-`b` obstacle charged exactly at stage `s`. -/
theorem stU_bounds {b n s : ℕ} (hb : 2 ≤ b) (h : stU b n = s) :
    b ^ n < 9 ^ s ∧ 9 ^ s ≤ 9 * b ^ n := by
  refine ⟨pow_lt_of_stU hb h.le, ?_⟩
  rw [← h]; unfold stU; rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 9 (by positivity))

theorem stB_bounds {q s : ℕ} (hq : 1 ≤ q) (h : stB q = s) :
    9 * q ^ 2 < 9 ^ s ∧ 9 ^ s ≤ 81 * q ^ 2 := by
  rw [← h]; unfold stB
  set t := Nat.log 9 (q ^ 2)
  have h1 : q ^ 2 < 9 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : 9 ^ t ≤ q ^ 2 := Nat.pow_log_le_self 9 (by positivity)
  have e1 : 9 ^ (t + 2) = 9 ^ (t + 1) * 9 := pow_succ _ _
  have e2 : 9 ^ (t + 2) = 9 ^ t * 81 := by rw [pow_add]; norm_num
  constructor <;> omega

theorem n_spread {b n n' s : ℕ} (hb : 2 ≤ b) (h : stU b n = s) (h' : stU b n' = s)
    (hle : n ≤ n') : n' ≤ n + 3 := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := stU_bounds hb h
  obtain ⟨h1', -⟩ := stU_bounds hb h'
  have : b ^ n * 16 ≤ b ^ n' := by
    calc b ^ n * 16 ≤ b ^ n * b ^ 4 := by
          gcongr; calc 16 = 2 ^ 4 := by norm_num
            _ ≤ b ^ 4 := Nat.pow_le_pow_left hb 4
      _ = b ^ (n + 4) := by ring
      _ ≤ b ^ n' := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem a_spread {b n a a' s X : ℕ} (hb : 2 ≤ b) (h : stU b n = s) (hle : a ≤ a')
    (hm : Meets ctr rad (Sum.inl (b, n, a)) s X) (hm' : Meets ctr rad (Sum.inl (b, n, a')) s X) :
    a' ≤ a + 1 := by
  by_contra hc
  push Not at hc
  have hc' : (a : ℝ) + 2 ≤ a' := by exact_mod_cast hc
  obtain ⟨h1, -⟩ := stU_bounds hb h
  have hBN : ((b : ℝ) ^ n) < 9 ^ s := by exact_mod_cast h1
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hB : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have h40 : (2 : ℝ) ≤ (b : ℝ) ^ 40 := by
    calc (2 : ℝ) ≤ 2 ^ 40 := by norm_num
      _ ≤ (b : ℝ) ^ 40 := by gcongr
  simp only [Meets, ctr, rad] at hm hm'
  obtain ⟨-, hA⟩ := hm
  obtain ⟨hA', -⟩ := hm'
  -- a'/B − r ≤ (X+1)/N and X/N ≤ a/B + r
  have hr : 1 / (b : ℝ) ^ (n + 40) ≤ 1 / (2 * (b : ℝ) ^ n) := by
    rw [pow_add]; apply one_div_le_one_div_of_le (by positivity); nlinarith
  have hN : 1 / (9 : ℝ) ^ s < 1 / (b : ℝ) ^ n := one_div_lt_one_div_of_lt hB hBN
  have : ((a' : ℝ) - a) / (b : ℝ) ^ n ≤ 1 / 9 ^ s + 2 * (1 / (b : ℝ) ^ (n + 40)) := by
    rw [sub_div]
    have e : ((X : ℝ) + 1) / 9 ^ s = X / 9 ^ s + 1 / 9 ^ s := by ring
    linarith
  have h2 : (2 : ℝ) / (b : ℝ) ^ n ≤ ((a' : ℝ) - a) / (b : ℝ) ^ n :=
    div_le_div_of_nonneg_right (by linarith) hB.le
  have e2 : 2 * (1 / (2 * (b : ℝ) ^ n)) = 1 / (b : ℝ) ^ n := by field_simp
  have e3 : (2 : ℝ) / (b : ℝ) ^ n = 1 / (b : ℝ) ^ n + 1 / (b : ℝ) ^ n := by ring
  linarith

theorem bad_unique {p q p' q' s X : ℕ} (hv : ValidB (p, q)) (hv' : ValidB (p', q'))
    (h : stB q = s) (h' : stB q' = s) (hm : Meets ctr rad (Sum.inr (p, q)) s X)
    (hm' : Meets ctr rad (Sum.inr (p', q')) s X) : (p, q) = (p', q') := by
  obtain ⟨hq, -, hc⟩ := hv
  obtain ⟨hq', -, hc'⟩ := hv'
  simp only at hq hc hq' hc'
  obtain ⟨b1, b2⟩ := stB_bounds hq h
  obtain ⟨b1', b2'⟩ := stB_bounds hq' h'
  by_cases hpq : p * q' = p' * q
  · have d1 : q ∣ q' := (Nat.Coprime.symm hc).dvd_of_dvd_mul_left ⟨p', by rw [hpq]; ring⟩
    have d2 : q' ∣ q := (Nat.Coprime.symm hc').dvd_of_dvd_mul_left ⟨p, by rw [← hpq]; ring⟩
    have hqq := Nat.dvd_antisymm d1 d2
    subst hqq
    have : p = p' := Nat.eq_of_mul_eq_mul_right (by omega) hpq
    rw [this]
  exfalso
  have hN := (show (0 : ℝ) < 9 ^ s by positivity)
  have qR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have qR' : (1 : ℝ) ≤ q' := by exact_mod_cast hq'
  have B1 : 9 * (q : ℝ) ^ 2 < 9 ^ s := by exact_mod_cast b1
  have B1' : 9 * (q' : ℝ) ^ 2 < 9 ^ s := by exact_mod_cast b1'
  have B2 : (9 : ℝ) ^ s ≤ 81 * (q : ℝ) ^ 2 := by exact_mod_cast b2
  have B2' : (9 : ℝ) ^ s ≤ 81 * (q' : ℝ) ^ 2 := by exact_mod_cast b2'
  have hqq : 9 * ((q : ℝ) * q') < 9 ^ s := by
    have : (9 * ((q : ℝ) * q')) ^ 2 < (9 ^ s) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hN.le this
  have hr : 1 / (9 ^ 5 * (q : ℝ) ^ 2) ≤ 1 / (729 * 9 ^ s) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hr' : 1 / (9 ^ 5 * (q' : ℝ) ^ 2) ≤ 1 / (729 * 9 ^ s) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hD : (1 : ℝ) ≤ |(p : ℝ) * q' - p' * q| := by
    have : (p : ℤ) * q' - p' * q ≠ 0 := by
      intro h0; apply hpq; exact_mod_cast (sub_eq_zero.mp h0)
    have := Int.one_le_abs this
    exact_mod_cast this
  have hdiff : |(p : ℝ) / q - p' / q'| = |(p : ℝ) * q' - p' * q| / (q * q') := by
    rw [div_sub_div _ _ (by positivity) (by positivity), abs_div,
      abs_of_pos (show (0 : ℝ) < q * q' by positivity)]
    ring_nf
  have hlow : 9 / (9 : ℝ) ^ s < |(p : ℝ) / q - p' / q'| := by
    rw [hdiff, div_lt_div_iff₀ hN (by positivity)]; nlinarith
  simp only [Meets, ctr, rad] at hm hm'
  have hup : |(p : ℝ) / q - p' / q'| ≤ 1 / 9 ^ s + 2 * (1 / (729 * 9 ^ s)) := by
    have e : ((X : ℝ) + 1) / 9 ^ s = X / 9 ^ s + 1 / 9 ^ s := by ring
    rw [abs_le]; constructor <;> linarith [hm.1, hm.2, hm'.1, hm'.2]
  have : 1 / (9 : ℝ) ^ s + 2 * (1 / (729 * 9 ^ s)) < 9 / 9 ^ s := by
    rw [show 1 / (9 : ℝ) ^ s + 2 * (1 / (729 * 9 ^ s)) = (731 / 729) / 9 ^ s by field_simp; ring]
    exact div_lt_div_of_pos_right (by norm_num) hN
  linarith

/-- Projections of an index (garbage `0` on the wrong summand). -/
def bOf : Idx → ℕ | .inl x => x.1 | .inr _ => 0
def nOf : Idx → ℕ | .inl x => x.2.1 | .inr _ => 0
def aOf : Idx → ℕ | .inl x => x.2.2 | .inr _ => 0

theorem weight_inl_le {b n a s : ℕ} (hb : 2 ≤ b) (h : stU b n = s) :
    (2 : ℝ) ^ ((s : ℤ) - lev (Sum.inl (b, n, a))) ≤ 1 / (64 * (b : ℝ) ^ 2) := by
  simp only [lev, h]
  set m := Nat.log 2 b
  have hb2 : b < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) b
  have hbR : (b : ℝ) < 2 ^ (m + 1) := by exact_mod_cast hb2
  rw [show ((s : ℤ) - ((s + (8 + 2 * m) : ℕ) : ℤ)) = -((8 + 2 * m : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, ← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  have : (b : ℝ) ^ 2 < (2 ^ (m + 1)) ^ 2 := by
    have : (0 : ℝ) ≤ b := by positivity
    gcongr
  calc 64 * (b : ℝ) ^ 2 ≤ 64 * (2 ^ (m + 1)) ^ 2 := by linarith
    _ = 2 ^ (8 + 2 * m) := by ring

theorem sum_inv_sq_le (M : ℕ) : ∑ b ∈ Finset.Ico 2 M, 1 / ((b : ℝ) ^ 2) ≤ 1 := by
  have key : ∀ M : ℕ, 2 ≤ M → ∑ b ∈ Finset.Ico 2 M, 1 / ((b : ℝ) ^ 2) ≤ 1 - 1 / (M - 1 : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
      have : 1 / ((M : ℝ) ^ 2) ≤ 1 / (M - 1 : ℝ) - 1 / M := by
        rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity)
          (by nlinarith)]
        nlinarith
      push_cast
      rw [show (M : ℝ) + 1 - 1 = M by ring]
      linarith
  rcases Nat.lt_or_ge M 2 with hM | hM
  · rw [Finset.Ico_eq_empty (by omega)]; simp
  · have := key M hM
    have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have : 0 ≤ 1 / (M - 1 : ℝ) := by apply div_nonneg <;> linarith
    linarith

open Classical in
theorem newPot_FF_le (k X : ℕ) : newPot FF ctr rad lev k X ≤ 1 / 2 := by
  have hN : newPot FF ctr rad lev k X = ∑ i ∈ (FF (k + 1) \ FF k).filter
      (fun i => Meets ctr rad i (k + 1) X), (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - lev i) := by
    unfold newPot; congr; funext a b; exact Subsingleton.elim _ _
  generalize hs : k + 1 = s at hN
  set N := (FF s \ FF k).filter (fun i => Meets ctr rad i s X) with hNdef
  -- membership facts
  have memL : ∀ i ∈ N, ∀ x : ℕ × ℕ × ℕ, i = Sum.inl x → ValidU x ∧ stU x.1 x.2.1 = s ∧
      Meets ctr rad i s X := by
    intro i hi x hx
    subst hx
    simp only [hNdef, Finset.mem_filter, Finset.mem_sdiff] at hi
    obtain ⟨⟨h1, h2⟩, hm⟩ := hi
    rw [mem_FF_inl] at h1 h2
    refine ⟨h1.1, ?_, hm⟩
    by_contra hne
    exact h2 ⟨h1.1, by omega⟩
  have memR : ∀ i ∈ N, ∀ x : ℕ × ℕ, i = Sum.inr x → ValidB x ∧ stB x.2 = s ∧
      Meets ctr rad i s X := by
    intro i hi x hx
    subst hx
    simp only [hNdef, Finset.mem_filter, Finset.mem_sdiff] at hi
    obtain ⟨⟨h1, h2⟩, hm⟩ := hi
    rw [mem_FF_inr] at h1 h2
    refine ⟨h1.1, ?_, hm⟩
    by_contra hne
    exact h2 ⟨h1.1, by omega⟩
  rw [hN, ← Finset.sum_filter_add_sum_filter_not N (fun i => i.isLeft = true)]
  set NL := N.filter (fun i => i.isLeft = true)
  set NR := N.filter (fun i => ¬ i.isLeft = true)
  -- the rational part: at most one obstacle, weight 1/4
  have hR : ∑ i ∈ NR, (2 : ℝ) ^ ((s : ℤ) - lev i) ≤ 1 / 4 := by
    have hw : ∀ i ∈ NR, (2 : ℝ) ^ ((s : ℤ) - lev i) = 1 / 4 := by
      intro i hi
      obtain ⟨hi, hl⟩ := Finset.mem_filter.mp hi
      rcases i with x | ⟨p, q⟩
      · simp at hl
      · obtain ⟨-, hs, -⟩ := memR _ hi (p, q) rfl
        simp only [lev, hs]
        rw [show ((s : ℤ) - ((s + 2 : ℕ) : ℤ)) = -2 by push_cast; ring]; norm_num
    have hcard : NR.card ≤ 1 := by
      refine Finset.card_le_one.mpr fun i hi j hj => ?_
      obtain ⟨hi, hil⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj, hjl⟩ := Finset.mem_filter.mp hj
      rcases i with x | ⟨p, q⟩
      · simp at hil
      rcases j with y | ⟨p', q'⟩
      · simp at hjl
      obtain ⟨v, hs, hm⟩ := memR _ hi (p, q) rfl
      obtain ⟨v', hs', hm'⟩ := memR _ hj (p', q') rfl
      rw [bad_unique v v' hs hs' hm hm']
    rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
    have : (NR.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    linarith
  -- the base part
  have hL : ∑ i ∈ NL, (2 : ℝ) ^ ((s : ℤ) - lev i) ≤ 1 / 8 := by
    have memL' : ∀ i ∈ NL, ∃ x : ℕ × ℕ × ℕ, i = Sum.inl x ∧ ValidU x ∧ stU x.1 x.2.1 = s ∧
        Meets ctr rad i s X := by
      intro i hi
      obtain ⟨hi, hl⟩ := Finset.mem_filter.mp hi
      rcases i with x | x
      · exact ⟨x, rfl, memL _ hi x rfl⟩
      · simp at hl
    -- each weight is at most f (bOf i)
    have hw : ∀ i ∈ NL, (2 : ℝ) ^ ((s : ℤ) - lev i) ≤ 1 / (64 * ((bOf i : ℕ) : ℝ) ^ 2) := by
      intro i hi
      obtain ⟨⟨b, n, a⟩, rfl, ⟨hb, -, -⟩, hs, -⟩ := memL' i hi
      exact weight_inl_le hb hs
    refine (Finset.sum_le_sum hw).trans ?_
    rw [← Finset.sum_fiberwise_of_maps_to (g := bOf) (t := NL.image bOf)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    -- fibers have at most 8 elements
    have hfib : ∀ b ∈ NL.image bOf, (NL.filter (fun i => bOf i = b)).card ≤ 8 := by
      intro b _
      set Fb := NL.filter (fun i => bOf i = b)
      have hnimg : (Fb.image nOf).card ≤ 4 := by
        apply card_le_of_spread _ 3
        intro x hx y hy hxy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hi, hib⟩ := Finset.mem_filter.mp hi
        obtain ⟨hj, hjb⟩ := Finset.mem_filter.mp hj
        obtain ⟨⟨b1, n1, a1⟩, rfl, ⟨hb1, -, -⟩, hs1, -⟩ := memL' i hi
        obtain ⟨⟨b2, n2, a2⟩, rfl, ⟨hb2, -, -⟩, hs2, -⟩ := memL' j hj
        simp only [bOf, nOf] at hib hjb hxy ⊢
        subst hib hjb
        exact n_spread hb1 hs1 hs2 hxy
      have hper : ∀ n ∈ Fb.image nOf, (Fb.filter (fun i => nOf i = n)).card ≤ 2 := by
        intro n _
        set Fn := Fb.filter (fun i => nOf i = n)
        have hinj : Set.InjOn aOf Fn := by
          intro i hi j hj hij
          obtain ⟨hi, hin⟩ := Finset.mem_filter.mp hi
          obtain ⟨hj, hjn⟩ := Finset.mem_filter.mp hj
          obtain ⟨hi, hib⟩ := Finset.mem_filter.mp hi
          obtain ⟨hj, hjb⟩ := Finset.mem_filter.mp hj
          obtain ⟨⟨b1, n1, a1⟩, rfl, -⟩ := memL' i hi
          obtain ⟨⟨b2, n2, a2⟩, rfl, -⟩ := memL' j hj
          simp only [bOf, nOf, aOf] at hib hjb hin hjn hij
          subst hib hjb hin hjn hij
          rfl
        rw [← Finset.card_image_of_injOn hinj]
        apply card_le_of_spread _ 1
        intro x hx y hy hxy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hi, hin⟩ := Finset.mem_filter.mp hi
        obtain ⟨hj, hjn⟩ := Finset.mem_filter.mp hj
        obtain ⟨hi, hib⟩ := Finset.mem_filter.mp hi
        obtain ⟨hj, hjb⟩ := Finset.mem_filter.mp hj
        obtain ⟨⟨b1, n1, a1⟩, rfl, ⟨hb1, -, -⟩, hs1, hm1⟩ := memL' i hi
        obtain ⟨⟨b2, n2, a2⟩, rfl, -, -, hm2⟩ := memL' j hj
        simp only [bOf, nOf, aOf] at hib hjb hin hjn hxy ⊢
        subst hib hjb hin hjn
        exact a_spread hb1 hs1 hxy hm1 hm2
      calc Fb.card ≤ 2 * (Fb.image nOf).card :=
            Finset.card_le_mul_card_image Fb 2 hper
        _ ≤ 2 * 4 := by gcongr
        _ = 8 := by norm_num
    have hsub : NL.image bOf ⊆ Finset.Ico (2 : ℕ) (9 ^ s) := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨⟨b, n, a⟩, rfl, hv, hs, -⟩ := memL' i hi
      have hmem : Sum.inl (b, n, a) ∈ FF s := mem_FF_inl.mpr ⟨hv, hs.le⟩
      simp only [FF, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hmem
      simp only [bOf, Finset.mem_Ico]
      exact ⟨hv.1, hmem.1.1⟩
    calc ∑ b ∈ NL.image bOf, ∑ i ∈ NL.filter (fun i => bOf i = b),
          1 / (64 * ((bOf i : ℕ) : ℝ) ^ 2)
        = ∑ b ∈ NL.image bOf, ((NL.filter (fun i => bOf i = b)).card : ℝ) *
            (1 / (64 * (b : ℝ) ^ 2)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_congr rfl (g := fun _ => 1 / (64 * (b : ℝ) ^ 2))
            (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ NL.image bOf, 8 * (1 / (64 * (b : ℝ) ^ 2)) := by
          refine Finset.sum_le_sum fun b hb => ?_
          have : ((NL.filter (fun i => bOf i = b)).card : ℝ) ≤ 8 := by exact_mod_cast hfib b hb
          have : (0 : ℝ) ≤ 1 / (64 * (b : ℝ) ^ 2) := by positivity
          nlinarith
      _ ≤ ∑ b ∈ Finset.Ico (2 : ℕ) (9 ^ s), 8 * (1 / (64 * (b : ℝ) ^ 2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = (1 / 8) * ∑ b ∈ Finset.Ico (2 : ℕ) (9 ^ s), 1 / ((b : ℝ) ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; field_simp; ring
      _ ≤ 1 / 8 := by
          have := sum_inv_sq_le (9 ^ s)
          nlinarith
  linarith

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

theorem cross_left (a B D N Y : ℕ) (hB : 0 < B) (hD : 0 < D) (hN : 0 < N) :
    (a : ℝ) / B - 1 / (B * D) ≤ Y / N ↔ (a * D - 1) * N ≤ Y * (B * D) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (a : ℝ) / B - 1 / (B * D) = ((a : ℝ) * D - 1) / (B * D) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) hN']
  rcases Nat.eq_zero_or_pos (a * D) with h0 | h0
  · rw [h0]
    have : (a : ℝ) * D = 0 := by exact_mod_cast h0
    rw [this]; simp only [zero_tsub, zero_mul, zero_le, iff_true]
    have : (0 : ℝ) ≤ Y * (B * D) := by positivity
    nlinarith
  · have hc : ((a * D - 1 : ℕ) : ℝ) = (a : ℝ) * D - 1 := by
      rw [Nat.cast_sub h0]; push_cast; ring
    rw [← hc, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]

theorem cross_right (a B D N X : ℕ) (hB : 0 < B) (hD : 0 < D) (hN : 0 < N) :
    (X : ℝ) / N ≤ a / B + 1 / (B * D) ↔ X * (B * D) ≤ (a * D + 1) * N := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (a : ℝ) / B + 1 / (B * D) = ((a : ℝ) * D + 1) / (B * D) := by field_simp
  rw [e, div_le_div_iff₀ hN' (by positivity)]
  constructor
  · intro h; exact_mod_cast (by linarith : (X : ℝ) * (B * D) ≤ (a * D + 1) * N)
  · intro h; have : ((X * (B * D) : ℕ) : ℝ) ≤ ((a * D + 1) * N : ℕ) := by exact_mod_cast h
    push_cast at this; linarith

theorem meets_iff {i : Idx} {k : ℕ} (hi : i ∈ FF k) (X : ℕ) :
    MeetsNat i k X ↔ Meets ctr rad i k X := by
  have h9 : 0 < 9 ^ k := by positivity
  rcases i with ⟨b, n, a⟩ | ⟨p, q⟩
  · obtain ⟨⟨hb, -, -⟩, -⟩ := mem_FF_inl.mp hi
    simp only at hb
    have hbn : 0 < b ^ n := by positivity
    have hb40 : 0 < b ^ 40 := by positivity
    have e : (1 : ℝ) / (b : ℝ) ^ (n + 40) = 1 / (((b ^ n : ℕ) : ℝ) * ((b ^ 40 : ℕ) : ℝ)) := by
      push_cast; rw [pow_add]
    simp only [MeetsNat, Meets, ctr, rad, e]
    have e2 : ((a : ℝ) / (b : ℝ) ^ n) = (a : ℝ) / ((b ^ n : ℕ) : ℝ) := by push_cast; rfl
    have eX : ((X : ℝ) + 1) = ((X + 1 : ℕ) : ℝ) := by push_cast; rfl
    have e9 : ((9 : ℝ) ^ k) = ((9 ^ k : ℕ) : ℝ) := by push_cast; rfl
    rw [e2, eX, e9, cross_left a _ _ _ _ hbn hb40 h9, cross_right a _ _ _ _ hbn hb40 h9,
      ← pow_add]
  · obtain ⟨⟨hq, -, -⟩, -⟩ := mem_FF_inr.mp hi
    simp only at hq
    have hq0 : 0 < q := hq
    have hD : 0 < 9 ^ 5 * q := by positivity
    have e : (1 : ℝ) / (9 ^ 5 * (q : ℝ) ^ 2) = 1 / ((q : ℝ) * ((9 ^ 5 * q : ℕ) : ℝ)) := by
      push_cast; ring_nf
    simp only [MeetsNat, Meets, ctr, rad, e]
    have eX : ((X : ℝ) + 1) = ((X + 1 : ℕ) : ℝ) := by push_cast; rfl
    have e9 : ((9 : ℝ) ^ k) = ((9 ^ k : ℕ) : ℝ) := by push_cast; rfl
    rw [eX, e9, cross_left p _ _ _ _ hq0 hD h9, cross_right p _ _ _ _ hq0 hD h9,
      show q * (9 ^ 5 * q) = 9 ^ 5 * q ^ 2 by ring, show p * (9 ^ 5 * q) = 9 ^ 5 * p * q by ring]

theorem lev_le {i : Idx} {k : ℕ} (hi : i ∈ FF k) : lev i ≤ 9 * k + 8 := by
  rcases i with ⟨b, n, a⟩ | ⟨p, q⟩
  · have hbox := hi
    simp only [FF, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hbox
    obtain ⟨⟨hb9, -, -⟩, ⟨hb, -, -⟩, hs⟩ := hbox
    simp only at hb9 hb hs
    have h16 : b < 2 ^ (4 * k) := by
      calc b < 9 ^ k := hb9
        _ ≤ 16 ^ k := Nat.pow_le_pow_left (by norm_num) k
        _ = 2 ^ (4 * k) := by rw [pow_mul]; norm_num
    have hlog : Nat.log 2 b < 4 * k := Nat.log_lt_of_lt_pow (by omega) h16
    simp only [lev]; omega
  · have := (mem_FF_inr.mp hi).2
    simp only at this
    simp only [lev]; omega

theorem goodNat_iff (k X : ℕ) : goodNat k X = true ↔ pot FF ctr rad lev k X < 1 := by
  classical
  unfold goodNat pot
  rw [decide_eq_true_iff]
  have hfil : (FF k).filter (fun i => MeetsNat i k X) =
      (FF k).filter (fun i => Meets ctr rad i k X) :=
    Finset.filter_congr fun i hi => meets_iff hi X
  rw [hfil]
  have hsum : (((∑ i ∈ (FF k).filter (fun i => Meets ctr rad i k X), 2 ^ (10 * k + 8 - lev i) : ℕ))
      : ℝ) = 2 ^ (9 * k + 8) * ∑ i ∈ (FF k).filter (fun i => Meets ctr rad i k X),
        (2 : ℝ) ^ ((k : ℤ) - lev i) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hl := lev_le (Finset.mem_filter.mp hi).1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    push_cast [show lev i ≤ 10 * k + 8 by omega]
    ring
  rw [← Nat.cast_lt (α := ℝ), hsum]
  push_cast
  constructor
  · intro h; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (9 * k + 8)]
  · intro h; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (9 * k + 8)]

/-! ### Bob's test is primitive recursive -/

theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem log_eq_findGreatest {b : ℕ} (hb : 1 < b) (x : ℕ) :
    Nat.log b x = Nat.findGreatest (fun t => b ^ t ≤ x) x := by
  symm
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun h => ?_, fun n hn _ hle => ?_⟩
  · rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · exact (Nat.log_lt_self b hx.ne').le
  · have hx : x ≠ 0 := by intro h0; subst h0; simp at h
    exact Nat.pow_log_le_self b hx
  · exact absurd hle (not_le.mpr (Nat.lt_pow_of_log_lt hb hn))

theorem primrec_log {b : ℕ} (hb : 1 < b) : Primrec (Nat.log b) := by
  have hp : PrimrecRel fun x t : ℕ => b ^ t ≤ x :=
    Primrec.nat_le.comp (primrec_pow.comp (Primrec.const b) Primrec.snd) Primrec.fst
  exact (Primrec.nat_findGreatest Primrec.id hp).of_eq fun x => (log_eq_findGreatest hb x).symm

theorem primrec_sum {α : Type*} [Primcodable α] {N : α → ℕ} {f : α → ℕ → ℕ} (hN : Primrec N)
    (hf : Primrec₂ f) : Primrec fun a => ∑ i ∈ range (N a), f a i := by
  have hh : Primrec₂ fun (a : α) (p : ℕ × ℕ) => p.2 + f a p.1 :=
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂
  refine (Primrec.nat_rec' hN (Primrec.const 0) hh).of_eq fun a => ?_
  generalize N a = m
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.sum_range_succ, ← ih]

theorem coprime_iff_bounded {p q : ℕ} (hq : 1 ≤ q) :
    Nat.Coprime p q ↔ ∀ d < q + 1, ¬ p % d = 0 ∨ ¬ q % d = 0 ∨ d = 1 := by
  constructor
  · intro h d _
    by_cases hp : p % d = 0
    · by_cases hq' : q % d = 0
      · right; right
        exact Nat.eq_one_of_dvd_coprimes h (Nat.dvd_of_mod_eq_zero hp) (Nat.dvd_of_mod_eq_zero hq')
      · right; left; exact hq'
    · left; exact hp
  · intro h
    have hg : Nat.gcd p q < q + 1 := Nat.lt_succ_of_le (Nat.le_of_dvd hq (Nat.gcd_dvd_right p q))
    rcases h _ hg with h1 | h1 | h1
    · exact absurd (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left p q)) h1
    · exact absurd (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right p q)) h1
    · exact h1

/-- The base-part term of Bob's sum. -/
def TU (k X b n a : ℕ) : ℕ :=
  if (ValidU (b, n, a) ∧ stU b n ≤ k) ∧ MeetsNat (Sum.inl (b, n, a)) k X then
    2 ^ (10 * k + 8 - lev (Sum.inl (b, n, a))) else 0

/-- The rational-part term of Bob's sum. -/
def TB (k X p q : ℕ) : ℕ :=
  if (ValidB (p, q) ∧ stB q ≤ k) ∧ MeetsNat (Sum.inr (p, q)) k X then
    2 ^ (10 * k + 8 - lev (Sum.inr (p, q))) else 0

theorem goodSum_eq (k X : ℕ) :
    (∑ i ∈ (FF k).filter (fun i => MeetsNat i k X), 2 ^ (10 * k + 8 - lev i)) =
      (∑ b ∈ range (9 ^ k), ∑ n ∈ range (4 * k + 1), ∑ a ∈ range (9 ^ k + 1), TU k X b n a) +
      ∑ p ∈ range (3 ^ k), ∑ q ∈ range (3 ^ k), TB k X p q := by
  rw [Finset.sum_filter, FF, Finset.sum_disjSum, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_product, Finset.sum_product]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun a _ => ?_
    unfold TU; simp only [ite_and]
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    unfold TB; simp only [ite_and]

theorem primrec_TU : Primrec fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
    TU t.1.1.1.1 t.1.1.1.2 t.1.1.2 t.1.2 t.2 := by
  have hk : Primrec fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => t.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hX : Primrec fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => t.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hb : Primrec fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => t.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => t.1.2 := Primrec.snd.comp Primrec.fst
  have ha : Primrec fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => t.2 := Primrec.snd
  have hbn := primrec_pow.comp hb hn
  have hb40 := primrec_pow.comp hb (Primrec.const 40)
  have hbn40 := primrec_pow.comp hb (Primrec.nat_add.comp hn (Primrec.const 40))
  have h9k := primrec_pow.comp (Primrec.const 9) hk
  have hst := Primrec.succ.comp ((primrec_log (by norm_num : 1 < 9)).comp hbn)
  have hlev := Primrec.nat_add.comp hst (Primrec.nat_add.comp (Primrec.const 8)
    (Primrec.nat_mul.comp (Primrec.const 2) ((primrec_log (by norm_num : 1 < 2)).comp hb)))
  have hc : PrimrecPred fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
      ((2 ≤ t.1.1.2 ∧ (1 ≤ t.1.2 ∨ t.1.1.2 = 2) ∧ t.2 ≤ t.1.1.2 ^ t.1.2) ∧
        Nat.log 9 (t.1.1.2 ^ t.1.2) + 1 ≤ t.1.1.1.1) ∧
      ((t.2 * t.1.1.2 ^ 40 - 1) * 9 ^ t.1.1.1.1 ≤ (t.1.1.1.2 + 1) * t.1.1.2 ^ (t.1.2 + 40) ∧
        t.1.1.1.2 * t.1.1.2 ^ (t.1.2 + 40) ≤ (t.2 * t.1.1.2 ^ 40 + 1) * 9 ^ t.1.1.1.1) :=
    PrimrecPred.and
      (PrimrecPred.and
        (PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 2) hb)
          (PrimrecPred.and
            (PrimrecPred.or (Primrec.nat_le.comp (Primrec.const 1) hn)
              (Primrec.eq.comp hb (Primrec.const 2)))
            (Primrec.nat_le.comp ha hbn)))
        (Primrec.nat_le.comp hst hk))
      (PrimrecPred.and
        (Primrec.nat_le.comp
          (Primrec.nat_mul.comp (Primrec.nat_sub.comp (Primrec.nat_mul.comp ha hb40)
            (Primrec.const 1)) h9k)
          (Primrec.nat_mul.comp (Primrec.succ.comp hX) hbn40))
        (Primrec.nat_le.comp (Primrec.nat_mul.comp hX hbn40)
          (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.nat_mul.comp ha hb40)) h9k)))
  have hw := primrec_pow.comp (Primrec.const 2)
    (Primrec.nat_sub.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) hk)
      (Primrec.const 8)) hlev)
  exact (Primrec.ite hc hw (Primrec.const 0)).of_eq fun t => by
    unfold TU; exact if_congr Iff.rfl rfl rfl

theorem primrec_TB : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => TB t.1.1.1 t.1.1.2 t.1.2 t.2 := by
  have hk : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hX : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hp : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.2 := Primrec.snd.comp Primrec.fst
  have hq : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.2 := Primrec.snd
  have hq2 := primrec_pow.comp hq (Primrec.const 2)
  have h9k := primrec_pow.comp (Primrec.const 9) hk
  have hst := Primrec.nat_add.comp ((primrec_log (by norm_num : 1 < 9)).comp hq2) (Primrec.const 2)
  have hpq := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const (9 ^ 5)) hp) hq
  have hD := Primrec.nat_mul.comp (Primrec.const (9 ^ 5)) hq2
  have hR : PrimrecRel fun (d : ℕ) (y : ℕ × ℕ) => ¬ y.1 % d = 0 ∨ ¬ y.2 % d = 0 ∨ d = 1 :=
    PrimrecPred.or (PrimrecPred.not (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) Primrec.fst) (Primrec.const 0)))
      (PrimrecPred.or (PrimrecPred.not (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) Primrec.fst) (Primrec.const 0)))
        (Primrec.eq.comp Primrec.fst (Primrec.const 1)))
  have hcop : PrimrecPred fun t : ((ℕ × ℕ) × ℕ) × ℕ =>
      ∀ d < t.2 + 1, ¬ t.1.2 % d = 0 ∨ ¬ t.2 % d = 0 ∨ d = 1 :=
    have h0 := PrimrecRel.comp (PrimrecRel.forall_mem_list hR)
      (Primrec.list_range.comp (Primrec.succ.comp hq)) (Primrec.pair hp hq)
    h0.of_eq fun t => by simp only [List.mem_range]
  have hc : PrimrecPred fun t : ((ℕ × ℕ) × ℕ) × ℕ =>
      ((1 ≤ t.2 ∧ t.1.2 ≤ t.2 ∧ ∀ d < t.2 + 1, ¬ t.1.2 % d = 0 ∨ ¬ t.2 % d = 0 ∨ d = 1) ∧
        Nat.log 9 (t.2 ^ 2) + 2 ≤ t.1.1.1) ∧
      ((9 ^ 5 * t.1.2 * t.2 - 1) * 9 ^ t.1.1.1 ≤ (t.1.1.2 + 1) * (9 ^ 5 * t.2 ^ 2) ∧
        t.1.1.2 * (9 ^ 5 * t.2 ^ 2) ≤ (9 ^ 5 * t.1.2 * t.2 + 1) * 9 ^ t.1.1.1) :=
    PrimrecPred.and
      (PrimrecPred.and
        (PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) hq)
          (PrimrecPred.and (Primrec.nat_le.comp hp hq) hcop))
        (Primrec.nat_le.comp hst hk))
      (PrimrecPred.and
        (Primrec.nat_le.comp
          (Primrec.nat_mul.comp (Primrec.nat_sub.comp hpq (Primrec.const 1)) h9k)
          (Primrec.nat_mul.comp (Primrec.succ.comp hX) hD))
        (Primrec.nat_le.comp (Primrec.nat_mul.comp hX hD)
          (Primrec.nat_mul.comp (Primrec.succ.comp hpq) h9k)))
  have hw := primrec_pow.comp (Primrec.const 2)
    (Primrec.nat_sub.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) hk)
      (Primrec.const 8)) (Primrec.nat_add.comp hst (Primrec.const 2)))
  refine (Primrec.ite hc hw (Primrec.const 0)).of_eq fun t => ?_
  unfold TB
  refine if_congr ?_ rfl rfl
  show ((1 ≤ t.2 ∧ t.1.2 ≤ t.2 ∧ _) ∧ _) ∧ _ ↔ ((1 ≤ t.2 ∧ t.1.2 ≤ t.2 ∧ Nat.Coprime t.1.2 t.2) ∧ _) ∧ _
  constructor
  · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩; exact ⟨⟨⟨h1, h2, (coprime_iff_bounded h1).mpr h3⟩, h4⟩, h5⟩
  · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩; exact ⟨⟨⟨h1, h2, (coprime_iff_bounded h1).mp h3⟩, h4⟩, h5⟩

theorem primrec_goodNat : Primrec₂ goodNat := by
  have hU3 : Primrec fun y : ((ℕ × ℕ) × ℕ) × ℕ =>
      ∑ a ∈ range (9 ^ y.1.1.1 + 1), TU y.1.1.1 y.1.1.2 y.1.2 y.2 a :=
    primrec_sum (N := fun y : ((ℕ × ℕ) × ℕ) × ℕ => 9 ^ y.1.1.1 + 1)
      (f := fun y a => TU y.1.1.1 y.1.1.2 y.1.2 y.2 a)
      (Primrec.succ.comp (primrec_pow.comp (Primrec.const 9)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) primrec_TU
  have hU2 : Primrec fun y : (ℕ × ℕ) × ℕ => ∑ n ∈ range (4 * y.1.1 + 1),
      ∑ a ∈ range (9 ^ y.1.1 + 1), TU y.1.1 y.1.2 y.2 n a :=
    primrec_sum (N := fun y : (ℕ × ℕ) × ℕ => 4 * y.1.1 + 1)
      (f := fun y n => ∑ a ∈ range (9 ^ y.1.1 + 1), TU y.1.1 y.1.2 y.2 n a)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.fst.comp Primrec.fst)))
      hU3
  have hU : Primrec fun x : ℕ × ℕ => ∑ b ∈ range (9 ^ x.1), ∑ n ∈ range (4 * x.1 + 1),
      ∑ a ∈ range (9 ^ x.1 + 1), TU x.1 x.2 b n a :=
    primrec_sum (N := fun x : ℕ × ℕ => 9 ^ x.1)
      (f := fun x b => ∑ n ∈ range (4 * x.1 + 1), ∑ a ∈ range (9 ^ x.1 + 1), TU x.1 x.2 b n a)
      (primrec_pow.comp (Primrec.const 9) Primrec.fst) hU2
  have hB2 : Primrec fun y : (ℕ × ℕ) × ℕ => ∑ q ∈ range (3 ^ y.1.1), TB y.1.1 y.1.2 y.2 q :=
    primrec_sum (N := fun y : (ℕ × ℕ) × ℕ => 3 ^ y.1.1)
      (f := fun y q => TB y.1.1 y.1.2 y.2 q)
      (primrec_pow.comp (Primrec.const 3) (Primrec.fst.comp Primrec.fst)) primrec_TB
  have hB : Primrec fun x : ℕ × ℕ => ∑ p ∈ range (3 ^ x.1), ∑ q ∈ range (3 ^ x.1),
      TB x.1 x.2 p q :=
    primrec_sum (N := fun x : ℕ × ℕ => 3 ^ x.1)
      (f := fun x p => ∑ q ∈ range (3 ^ x.1), TB x.1 x.2 p q)
      (primrec_pow.comp (Primrec.const 3) Primrec.fst) hB2
  have h := PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.nat_add.comp hU hB)
    (primrec_pow.comp (Primrec.const 2) (Primrec.nat_add.comp (Primrec.nat_mul.comp
      (Primrec.const 9) Primrec.fst) (Primrec.const 8))))
  exact h.of_eq fun x => by simp only [goodNat, goodSum_eq]

/-- The descent's digits. -/
def eBob : ℕ → Bool := bits goodNat

theorem primrec_dig : Primrec dig :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)))

theorem primrec_pick {good : ℕ → ℕ → Bool} (hg : Primrec₂ good) :
    Primrec₂ (pick good) := by
  have hc : ∀ j, PrimrecPred fun p : ℕ × ℕ => good (p.1 + 1) (9 * p.2 + dig j) = true := fun j =>
    Primrec.eq.comp (hg.comp (Primrec.succ.comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 9) Primrec.snd)
        (Primrec.const _))) (Primrec.const true)
  have h := Primrec.ite (hc 0) (Primrec.const 0) (Primrec.ite (hc 1) (Primrec.const 1)
    (Primrec.ite (hc 2) (Primrec.const 2) (Primrec.const 3)))
  exact h.of_eq fun p => rfl

theorem primrec_path {good : ℕ → ℕ → Bool} (hg : Primrec₂ good) : Primrec (path good) := by
  have h : Primrec (Nat.rec (motive := fun _ => ℕ) 0
      (fun k X => 9 * X + dig (pick good k X))) :=
    Primrec.nat_rec₁ 0 (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 9) Primrec.snd)
      (primrec_dig.comp (primrec_pick hg))).to₂
  refine h.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih => simp only [path, ← ih]

theorem primrec_bits {good : ℕ → ℕ → Bool} (hg : Primrec₂ good) : Primrec (bits good) := by
  have hj : Primrec fun n : ℕ => pick good (n / 2) (path good (n / 2)) :=
    (primrec_pick hg).comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
      ((primrec_path hg).comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
  have h := Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0))
    (PrimrecPred.decide (Primrec.nat_le.comp (Primrec.const 2) hj))
    (PrimrecPred.decide (Primrec.eq.comp (Primrec.nat_mod.comp hj (Primrec.const 2))
      (Primrec.const 1)))
  exact h.of_eq fun n => rfl

theorem computable_eBob : Computable eBob :=
  (primrec_bits primrec_goodNat).to_comp

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
