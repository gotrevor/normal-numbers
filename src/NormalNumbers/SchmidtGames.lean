/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBad
import NormalNumbers.RealDefs
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Instances.CantorSet

/-!
# The Bugeaud 10.36 set is potential winning: dimension of uniform bad approximability

`UniformBad.bugeaud_10_36` produced ONE `ξ` with `‖bⁿξ‖ > b^{−24}` for every base `b ≥ 2` and
every `n ≥ 0` (Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012,
Problem 10.36).  This file asks how LARGE the set of such `ξ` is.  For a real `C` put

  `E C = {ξ : ‖bⁿξ‖ > b^{−C} for all b ≥ 2, n ≥ 0}`,   `U = ⋃_C E C`.

Bugeaud's problem asks only that `U` be nonempty, and we know of no paper stating its size.

## Headlines (frozen 2026-10-04)

1. **`potentialWinning_E`** (proved 2026-10-04, the new combinatorial core).  For all `0 < β < 1`, `ρ > 0`
   there is `K` with `E C` `(K·2^{−C}, β, 1/2, ρ)`-potential winning for every `C ≥ 3`, in the
   potential game of Fishman–Simmons–Urbański / Broderick–Fishman–Simmons (`PotentialWinning`).
2. **`dimH_E₂_le`** (proved 2026-10-04, a base-2 covering count).
   `dim_H {ξ : ‖2ⁿξ‖ > 2^{−C} ∀ n} ≤ 1 − 2^{−(C+1)}` for `C ≥ 1`.
3. Wired from 1 and 2 (proved here, sorry-free, with headline 1 as the hypothesis
   `EPotentialWinning` and the cited dimension theorem):
   * **`codim_E_asymp`**: `1 − dim_H E C ≍ 2^{−C}`.  Uniform bad approximability to EVERY base
     costs, up to a constant factor in the codimension, no more than base 2 alone.  (Uses
     headline 2 for the upper half.)
   * **`dimH_U_eq_one_of`**: `dim_H U = 1`.
   * **`le_dimH_U_inter_cantor_of`**: `dim_H (U ∩ middle-third Cantor set) ≥ log 2 / log 3`
     (equality is classical, from `dim_H cantorSet = log 2/log 3`).
   * **`le_dimH_U_inter_Bad_inter_cantor_of`**: the same for `U ∩ BAD ∩ cantorSet`.

Closest prior result: Temur, arXiv:2609.16362 (14 Sep 2026, Bugeaud 10.53), a computable `ξ`
with `‖bᵏξ‖ > 154^{−2^b}` for all `b`, doubly exponential in `b`.  The computable version of
item 3 is the stretch conjecture in `SchmidtGamesStretch.lean`.

## Cited inputs (`Literature`, never `axiom`)

* `Literature.BFSPotentialDim J δ`: Broderick–Fishman–Simmons, *Quantitative results using
  variants of Schmidt's game: dimension bounds, arithmetic progressions, and more*, Acta Arith.
  188 (2019) 289–316, arXiv:1703.09015, **Theorem 5.5** (label `theorempotentialHD`), specialised
  to `X = ℝ`, `H` = singletons, `J` = `[0,1]` (Lebesgue, `δ = η = 1`) or the middle-third Cantor
  set (`δ = η = log 2/log 3`).  Ahlfors `δ`-regular measures are absolutely `(δ, singletons)`-
  decaying (their Example 5.2).  BFS bound the Ahlfors dimension, which is `≤ dim_H`; the Prop
  uses `dim_H`, so it is weaker.
* `Literature.BFSBadPotential`: BFS Lemma 3.10 (`BA₁(ε)` is `(2ε/((1−2ε)β), β, β/2)`-absolute
  winning), read through their Remark 4.2 (the proof deletes, so it is `c = 0` potential
  winning) and Proposition 4.5 (monotone in `c`: one deletion of radius `≤ αρ` meets every
  `c > 0` budget).
* The countable intersection property (BFS Proposition 4.4) is **proved** here for two sets
  (`PotentialWinning.inter`), so it is not cited.

## Difficulty check

* **Proved implications.**  Everything in item 3 from items 1, 2 and the cited Props.
* **Unproved premise.**  Item 1, and the routine item 2.  Mechanism for item 1: the
  `UniformBad` early charging, now played against Bob.  Charge obstacle
  `N(a/bⁿ, b^{−C−n})` on the first turn `k` with `ρ_k ≤ b^{−n}`.  Its centres are `b^{−n} ≥ ρ_k`
  apart, so at most 4 meet `B_k`; at most `1 + log_b(1/β)` levels `n` per base land on one turn;
  each has radius `< b^{−C} ρ_k/β`.  The `c = 1/2` budget is then
  `4 β^{−1/2} Σ_b (1 + log_b(1/β)) b^{−C/2} ρ_k^{1/2} ≍ 2^{−C/2} ρ_k^{1/2}`, so `α ≍ 2^{−C}`
  (turn 0, and the first turn with `ρ_k ≤ 1`, cost a `ρ`- or `β`-dependent constant).
* **Known-false siblings, in the kernel.**
  - `E C` for one FIXED `C` is not winning at small scales: it misses `(−2^{−C}, 2^{−C})`
    (`E_disjoint_gap`), so `not_potentialWinning_E_small`.  The union over `C` is essential.
  - Normality is not winning, given item 1 (`not_potentialWinning_isNormal`): `U` never meets a
    normal number (`UniformBad.not_isNormal_of_uniformBad`).  So no game argument proves
    normality.
  - Exponent `≤ 1` fails even for large bases (`UniformBad.not_uniformBad_largeBases_of_le_one`);
    the mechanism needs `Σ_b b^{−C c} < ∞` with `c < 1`, so `C > 1`, and agrees.
* **Confidence.**  Item 1: mathematics 90%, Lean 65% (2–4 laps).  Item 2: mathematics 97%, Lean
  55%.  Freshness of item 3 (that nobody has written it): about 55%; experts in potential games
  could call it routine once the early-charging count is in hand.

Audit: `docs/SCHMIDT-GAMES-AUDIT-2026-10-04.md`.
-/

open Set Filter Topology Metric
open scoped ENNReal

namespace NormalNumbers.SchmidtGames

open NormalNumbers.UniformBad (dnear dnear_le_abs_sub dnear_nonneg)

/-! ## The potential game on `ℝ` with singleton obstacles (BFS Definition 4.1) -/

/-- A move of Bob: a closed ball, recorded as `(centre, radius)`. -/
abbrev Move := ℝ × ℝ

/-- The closed ball of a move. -/
def Move.ball (B : Move) : Set ℝ := closedBall B.1 B.2

/-- An Alice strategy: after Bob's moves `B₀, …, B_k` she deletes a countable family of
neighbourhoods `N(y, r) = closedBall y r` of singletons, listed as `ℕ → Option (ℝ × ℝ)`
(`none` = nothing). -/
def Strategy : Type := (k : ℕ) → (Fin (k + 1) → Move) → ℕ → Option (ℝ × ℝ)

/-- The `c`-budget term of one deletion. -/
noncomputable def budgetTerm (c : ℝ) : Option (ℝ × ℝ) → ℝ≥0∞
  | none => 0
  | some p => ENNReal.ofReal (p.2 ^ c)

/-- Alice plays legally: positive thicknesses and `Σ_i ρ_{i,k}^c ≤ (α ρ_k)^c` (BFS (4.1)),
whenever Bob's current radius `ρ_k` is positive (legal Bob play with `ρ, β > 0` keeps it so).
Used only with `c > 0`; BFS's separate `c = 0` rule is not modelled. -/
def Strategy.Legal (σ : Strategy) (α c : ℝ) : Prop :=
  ∀ (k : ℕ) (h : Fin (k + 1) → Move), 0 < (h (Fin.last k)).2 →
    (∀ i p, σ k h i = some p → 0 < p.2) ∧
      ∑' i, budgetTerm c (σ k h i) ≤ ENNReal.ofReal ((α * (h (Fin.last k)).2) ^ c)

/-- Bob plays legally: `ρ₀ ≥ ρ`, `ρ_{k+1} ≥ β ρ_k`, `B_{k+1} ⊆ B_k`; he ignores Alice. -/
def BobLegal (β ρ : ℝ) (B : ℕ → Move) : Prop :=
  ρ ≤ (B 0).2 ∧ ∀ k, β * (B k).2 ≤ (B (k + 1)).2 ∧ (B (k + 1)).ball ⊆ (B k).ball

/-- Bob's first `k + 1` moves. -/
def history (B : ℕ → Move) (k : ℕ) : Fin (k + 1) → Move := fun j => B j

/-- **`(α, β, c, ρ)`-potential winning** (BFS Definition 4.1, `X = ℝ`, `H` = singletons).
Alice wins if the radii do not tend to `0`, or the outcome lies in a deleted set, or the
outcome lies in `S`. -/
def PotentialWinning (S : Set ℝ) (α β c ρ : ℝ) : Prop :=
  ∃ σ : Strategy, σ.Legal α c ∧ ∀ B : ℕ → Move, BobLegal β ρ B →
    Tendsto (fun k => (B k).2) atTop (𝓝 0) →
    ∀ x, (∀ k, x ∈ (B k).ball) →
      x ∈ S ∨ ∃ k i p, σ k (history B k) i = some p ∧ dist x p.1 ≤ p.2

/-! ## Elementary properties (proved) -/

theorem PotentialWinning.mono_set {S T : Set ℝ} {α β c ρ : ℝ} (h : PotentialWinning S α β c ρ)
    (hST : S ⊆ T) : PotentialWinning T α β c ρ := by
  obtain ⟨σ, hσ, hw⟩ := h
  exact ⟨σ, hσ, fun B hB ht x hx => (hw B hB ht x hx).imp (fun h => hST h) id⟩

/-- Monotone in `α` (BFS Prop. 4.5), for `c ≥ 0`. -/
theorem PotentialWinning.mono_alpha {S : Set ℝ} {α α' β c ρ : ℝ} (h : PotentialWinning S α β c ρ)
    (hc : 0 ≤ c) (hα : 0 ≤ α) (hαα' : α ≤ α') : PotentialWinning S α' β c ρ := by
  obtain ⟨σ, hσ, hw⟩ := h
  refine ⟨σ, fun k hist hpos => ⟨(hσ k hist hpos).1, (hσ k hist hpos).2.trans ?_⟩, hw⟩
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (mul_nonneg hα hpos.le)
    (mul_le_mul_of_nonneg_right hαα' hpos.le) hc)

/-- Monotone in `ρ` (BFS Prop. 4.5): fewer opening moves for Bob. -/
theorem PotentialWinning.mono_rho {S : Set ℝ} {α β c ρ ρ' : ℝ} (h : PotentialWinning S α β c ρ)
    (hρ : ρ ≤ ρ') : PotentialWinning S α β c ρ' := by
  obtain ⟨σ, hσ, hw⟩ := h
  exact ⟨σ, hσ, fun B hB => hw B ⟨hρ.trans hB.1, hB.2⟩⟩

/-- **Intersection property** (BFS Proposition 4.4, two sets): Alice interleaves the two
strategies on even and odd indices, and the `c`-budgets add. -/
theorem PotentialWinning.inter {S₁ S₂ : Set ℝ} {α₁ α₂ β c ρ : ℝ} (hc : 0 < c)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (h₁ : PotentialWinning S₁ α₁ β c ρ) (h₂ : PotentialWinning S₂ α₂ β c ρ) :
    PotentialWinning (S₁ ∩ S₂) ((α₁ ^ c + α₂ ^ c) ^ c⁻¹) β c ρ := by
  obtain ⟨σ₁, hσ₁, hw₁⟩ := h₁
  obtain ⟨σ₂, hσ₂, hw₂⟩ := h₂
  let σ : Strategy := fun k h i => if i % 2 = 0 then σ₁ k h (i / 2) else σ₂ k h (i / 2)
  have e0 : ∀ k h j, σ k h (2 * j) = σ₁ k h j := by
    intro k h j
    simp only [σ, Nat.mul_mod_right, if_true]
    congr 1
    omega
  have e1 : ∀ k h j, σ k h (2 * j + 1) = σ₂ k h j := by
    intro k h j
    simp only [σ]
    rw [if_neg (by omega)]
    congr 1
    omega
  refine ⟨σ, fun k h hpos => ⟨?_, ?_⟩, ?_⟩
  · intro i p hp
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [e0] at hp
      exact (hσ₁ k h hpos).1 j p hp
    · rw [e1] at hp
      exact (hσ₂ k h hpos).1 j p hp
  · rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
    simp only [e0, e1]
    set r := (h (Fin.last k)).2
    have hn₁ : 0 ≤ (α₁ * r) ^ c := Real.rpow_nonneg (mul_nonneg hα₁ hpos.le) c
    have hn₂ : 0 ≤ (α₂ * r) ^ c := Real.rpow_nonneg (mul_nonneg hα₂ hpos.le) c
    calc _ ≤ ENNReal.ofReal ((α₁ * r) ^ c) + ENNReal.ofReal ((α₂ * r) ^ c) :=
          add_le_add (hσ₁ k h hpos).2 (hσ₂ k h hpos).2
      _ = _ := by
          rw [← ENNReal.ofReal_add hn₁ hn₂]
          congr 1
          have hs : 0 ≤ α₁ ^ c + α₂ ^ c :=
            add_nonneg (Real.rpow_nonneg hα₁ c) (Real.rpow_nonneg hα₂ c)
          rw [Real.mul_rpow (Real.rpow_nonneg hs _) hpos.le, Real.mul_rpow hα₁ hpos.le,
            Real.mul_rpow hα₂ hpos.le, Real.rpow_inv_rpow hs hc.ne']
          ring
  · intro B hB ht x hx
    rcases hw₁ B hB ht x hx with h1 | ⟨k, i, p, hp, hd⟩
    · rcases hw₂ B hB ht x hx with h2 | ⟨k, i, p, hp, hd⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨k, 2 * i + 1, p, by rw [e1]; exact hp, hd⟩
    · exact Or.inr ⟨k, 2 * i, p, by rw [e0]; exact hp, hd⟩

/-! ## The sets -/

/-- `E C = {ξ : ‖bⁿξ‖ > b^{−C} for every b ≥ 2, n ≥ 0}`: the Bugeaud 10.36 set at exponent `C`. -/
def E (C : ℝ) : Set ℝ :=
  {ξ | ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, (b : ℝ) ^ (-C) < dnear ((b : ℝ) ^ n * ξ)}

/-- `U = ⋃_C E C`: uniformly badly approximable to every base, some exponent. -/
def U : Set ℝ := ⋃ C : ℝ, E C

/-- The base-2 part of `E C`. -/
def E₂ (C : ℝ) : Set ℝ := {ξ | ∀ n : ℕ, (2 : ℝ) ^ (-C) < dnear ((2 : ℝ) ^ n * ξ)}

/-- `BA₁(ε) = ℝ ∖ ⋃_{p/q} B(p/q, ε q^{−2})` (BFS §3). -/
def BA (ε : ℝ) : Set ℝ := {x | ∀ (p : ℤ) (q : ℕ), 0 < q → ε / (q : ℝ) ^ 2 < |x - p / q|}

/-- The badly approximable numbers. -/
def Bad : Set ℝ := ⋃ ε : ℝ, ⋃ _ : 0 < ε, BA ε

theorem E_subset_E₂ (C : ℝ) : E C ⊆ E₂ C := fun _ hξ n => by
  simpa using hξ 2 le_rfl n

theorem E_subset_U (C : ℝ) : E C ⊆ U := subset_iUnion E C

/-- `UniformBad.exists_uniformBad_allBases_24`, restated: `E 24` is nonempty. -/
theorem E_24_nonempty : (E 24).Nonempty := by
  obtain ⟨ξ, -, h⟩ := UniformBad.exists_uniformBad_allBases_24
  exact ⟨ξ, h⟩

/-! ## Cited inputs -/

namespace Literature

/-- **Broderick–Fishman–Simmons, Acta Arith. 188 (2019), Theorem 5.5** (arXiv:1703.09015,
label `theorempotentialHD`), for `X = ℝ`, `H` = singletons, and `J` the topological support of
an Ahlfors `δ`-regular measure (which is absolutely `(δ, H)`-decaying, their Example 5.2, so
`η = δ`).  Verbatim: "Let `S ⊂ X` be `(α,β,c,ρ,H)`-potential winning, with `c < η` and
`β ≤ 1/4`.  Then for every ball `B₀ ⊂ X` centered in `J` with `rad(B₀) ≥ ρ`, we have
`dim_A(S ∩ J ∩ B₀) ≥ δ − K₁ α^η/|log β| > 0` if `α^c ≤ (1 − β^{η−c})/K₂`, where `K₁, K₂` are
large constants independent of `α, β, c, ρ`."  `dim_A` (Ahlfors dimension) is `≤ dim_H`, so this
`dim_H` form is weaker.  Instances used: `J = [0,1]`, `δ = 1`; `J = cantorSet`,
`δ = log 2/log 3`. -/
def BFSPotentialDim (J : Set ℝ) (δ : ℝ) : Prop :=
  ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
    ∀ (S : Set ℝ) (α β c ρ : ℝ), 0 < α → 0 < β → β ≤ 1 / 4 → 0 < c → c < δ → 0 < ρ →
      α ^ c ≤ (1 - β ^ (δ - c)) / K₂ → PotentialWinning S α β c ρ →
      ∀ x₀ ∈ J, ∀ r₀ : ℝ, ρ ≤ r₀ →
        ENNReal.ofReal (δ - K₁ * α ^ δ / |Real.log β|) ≤ dimH (S ∩ J ∩ closedBall x₀ r₀)

/-- BFS Theorem 5.5 on `[0, 1]` with Lebesgue measure. -/
def BFSDimInterval : Prop := BFSPotentialDim (Icc 0 1) 1

/-- BFS Theorem 5.5 on the middle-third Cantor set with its Ahlfors `log 2/log 3`-regular
Cantor measure. -/
def BFSDimCantor : Prop := BFSPotentialDim cantorSet (Real.log 2 / Real.log 3)

/-- **BFS Lemma 3.10** (`BA₁(ε)` is `(2ε/((1−2ε)β), β, β/2)`-absolute winning for
`0 < ε < 1/2`, `(ε/(1−ε))² ≤ β < 1`), read as potential winning for every `c > 0`: their
Remark 4.2 notes the proof only uses that the outcome avoids the deleted set (so `c = 0`
potential winning), and one deletion of radius `≤ αρ_k` meets every `c`-budget (Prop. 4.5). -/
def BFSBadPotential : Prop :=
  ∀ ε β c : ℝ, 0 < ε → ε < 1 / 2 → (ε / (1 - ε)) ^ 2 ≤ β → β < 1 → 0 < c →
    PotentialWinning (BA ε) (2 * ε / ((1 - 2 * ε) * β)) β c (β / 2)

end Literature

/-! ## Headline 1: `E C` is potential winning with `α ≍ 2^{−C}` -/

/-- The statement of headline 1, as a `Prop` so that the wiring below is sorry-free. -/
def EPotentialWinning : Prop :=
  ∀ β ρ : ℝ, 0 < β → β < 1 → 0 < ρ →
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, 3 ≤ C → PotentialWinning (E C) (K * 2 ^ (-C)) β (1 / 2) ρ

/-! ### Proof of headline 1: a stateless early-charging strategy -/

/-- Geometric tail: `Σ_{n : b^{-n} ≤ X} b^{-n/2} ≤ 4 √X` for `b ≥ 2`. -/
theorem tsum_level_le {b X : ℝ} (hb : 2 ≤ b) (hX : 0 < X) :
    ∑' n : ℕ, (if (b ^ n)⁻¹ ≤ X then ENNReal.ofReal (Real.sqrt (b ^ n)⁻¹) else 0)
      ≤ ENNReal.ofReal (4 * Real.sqrt X) := by
  set q : ℝ := Real.sqrt b⁻¹ with hq
  have hb0 : 0 < b := by linarith
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq34 : q ≤ 3 / 4 := by
    rw [hq, Real.sqrt_le_left (by norm_num)]
    rw [inv_le_comm₀ hb0 (by norm_num)]; linarith
  have hsq : ∀ n : ℕ, Real.sqrt (b ^ n)⁻¹ = q ^ n := by
    intro n
    have h2 : (q ^ n) ^ 2 = (b ^ n)⁻¹ := by
      rw [← pow_mul, mul_comm, pow_mul, hq, Real.sq_sqrt (inv_nonneg.2 hb0.le), inv_pow]
    rw [← h2, Real.sqrt_sq (pow_nonneg hq0 n)]
  have hex : ∃ n : ℕ, (b ^ n)⁻¹ ≤ X := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hX (show b⁻¹ < 1 by
      rw [inv_lt_one₀ hb0]; linarith)
    exact ⟨n, by rw [← inv_pow]; exact hn.le⟩
  classical
  set n0 := Nat.find hex
  have hn0 : (b ^ n0)⁻¹ ≤ X := Nat.find_spec hex
  set f : ℕ → ℝ≥0∞ := fun n => if (b ^ n)⁻¹ ≤ X then ENNReal.ofReal (Real.sqrt (b ^ n)⁻¹) else 0
  have hsupp : Function.support f ⊆ Set.range (fun m : ℕ => m + n0) := by
    intro n hn
    have : (b ^ n)⁻¹ ≤ X := by
      by_contra h; exact hn (by simp [f, h])
    have := Nat.find_min' hex this
    exact ⟨n - n0, by simp only; omega⟩
  rw [← (add_left_injective n0).tsum_eq hsupp]
  calc ∑' m, f (m + n0) ≤ ∑' m : ℕ, ENNReal.ofReal (Real.sqrt X) * ENNReal.ofReal q ^ m := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        simp only [f]
        split_ifs
        · rw [hsq, pow_add, ← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq0 _)
          rw [← hsq]; exact Real.sqrt_le_sqrt hn0
        · exact bot_le
    _ = ENNReal.ofReal (Real.sqrt X) * (1 - ENNReal.ofReal q)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (Real.sqrt X) * 4 := by
        gcongr
        rw [ENNReal.inv_le_iff_inv_le, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0]
        rw [show (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/4) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (4 * Real.sqrt X) := by
        rw [mul_comm, ENNReal.ofReal_mul (by norm_num)]; simp

/-- At most 5 integers lie within 2 of `y`. -/
theorem tsum_int_near_le (y : ℝ) (c : ℝ≥0∞) :
    ∑' a : ℤ, (if |(a : ℝ) - y| ≤ 2 then c else 0) ≤ 5 * c := by
  classical
  set s := Finset.Icc ⌈y - 2⌉ ⌊y + 2⌋
  rw [tsum_eq_sum (s := s)]
  · calc ∑ a ∈ s, (if |(a : ℝ) - y| ≤ 2 then c else 0) ≤ ∑ _a ∈ s, c :=
          Finset.sum_le_sum fun a _ => by split_ifs <;> simp
      _ = s.card * c := by simp
      _ ≤ 5 * c := by
          gcongr
          rw [Int.card_Icc]
          have h1 : (⌊y + 2⌋ : ℝ) ≤ y + 2 := Int.floor_le _
          have h2 : y - 2 ≤ (⌈y - 2⌉ : ℝ) := Int.le_ceil _
          have : ⌊y + 2⌋ - ⌈y - 2⌉ ≤ 4 := by
            have : ((⌊y + 2⌋ - ⌈y - 2⌉ : ℤ) : ℝ) ≤ 4 := by push_cast; linarith
            exact_mod_cast this
          norm_cast; omega
  · intro a ha
    rw [if_neg]
    intro h
    apply ha
    rw [abs_le] at h
    simp only [s, Finset.mem_Icc]
    exact ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩


/-- `Σ_{b ≥ 2} b^{−C/2} ≤ S · 2^{−C/2}` uniformly in `C ≥ 3`. -/
theorem exists_tsum_base_le : ∃ S : ℝ, 0 ≤ S ∧ ∀ C : ℝ, 3 ≤ C →
    ∑' b : ℕ, (if 2 ≤ b then ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) else 0)
      ≤ ENNReal.ofReal (S * Real.sqrt ((2 : ℝ) ^ (-C))) := by
  have hsum : Summable (fun b : ℕ => (b : ℝ) ^ (-(3 / 2) : ℝ)) :=
    Real.summable_nat_rpow.2 (by norm_num)
  set T := ∑' b : ℕ, (b : ℝ) ^ (-(3 / 2) : ℝ)
  have hT : 0 ≤ T := tsum_nonneg fun b => Real.rpow_nonneg (Nat.cast_nonneg b) _
  refine ⟨(2 : ℝ) ^ (3 / 2 : ℝ) * T, by positivity, fun C hC => ?_⟩
  set s := Real.sqrt ((2 : ℝ) ^ (-C))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have key : ∀ b : ℕ, (if 2 ≤ b then ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) else 0) ≤
      ENNReal.ofReal (s * (2 : ℝ) ^ (3 / 2 : ℝ) * (b : ℝ) ^ (-(3 / 2) : ℝ)) := by
    intro b
    split_ifs with hb
    · refine ENNReal.ofReal_le_ofReal ?_
      have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hb0 : (0 : ℝ) < b := by linarith
      have hs' : s = (2 : ℝ) ^ (-(C * (1 / 2))) := by
        simp only [s]; rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; ring_nf
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hb0.le, hs', show -C * (1 / 2) = -(C * (1 / 2)) by ring]
      have h1 : (b : ℝ) ^ (-(C * (1 / 2))) =
          (2 : ℝ) ^ (-(C * (1 / 2))) * (2 / b) ^ (C * (1 / 2)) := by
        generalize C * (1 / 2) = x
        rw [Real.div_rpow (by norm_num) hb0.le, mul_div, ← Real.rpow_add (by norm_num),
          neg_add_cancel, Real.rpow_zero, Real.rpow_neg hb0.le, one_div]
      have h2 : (2 / (b : ℝ)) ^ (C * (1 / 2)) ≤ (2 / b) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by positivity) (div_le_one_of_le₀ hb2 hb0.le)
          (by linarith)
      have h3 : (2 / (b : ℝ)) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * (b : ℝ) ^ (-(3 / 2) : ℝ) := by
        rw [Real.div_rpow (by norm_num) hb0.le, Real.rpow_neg hb0.le, div_eq_mul_inv]
      rw [h1, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h2.trans h3.le) (by positivity)
    · exact bot_le
  calc _ ≤ ∑' b : ℕ, ENNReal.ofReal (s * (2 : ℝ) ^ (3 / 2 : ℝ) * (b : ℝ) ^ (-(3 / 2) : ℝ)) :=
        ENNReal.tsum_le_tsum key
    _ = ENNReal.ofReal (∑' b : ℕ, s * (2 : ℝ) ^ (3 / 2 : ℝ) * (b : ℝ) ^ (-(3 / 2) : ℝ)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun b => by positivity) (hsum.mul_left _)).symm
    _ = _ := by rw [tsum_mul_left]; congr 1; ring


/-- The obstacle charge of one triple `(b, n, a)` at a turn with centre `x`, radius `r`. -/
noncomputable def charge (C M x r : ℝ) (t : ℕ × ℕ × ℤ) : Option (ℝ × ℝ) :=
  if 2 ≤ t.1 ∧ r ≤ ((t.1 : ℝ) ^ t.2.1)⁻¹ ∧ ((t.1 : ℝ) ^ t.2.1)⁻¹ ≤ M * r ∧
      |(t.2.2 : ℝ) - (t.1 : ℝ) ^ t.2.1 * x| ≤ 2 then
    some ((t.2.2 : ℝ) / (t.1 : ℝ) ^ t.2.1, (t.1 : ℝ) ^ (-C) / (t.1 : ℝ) ^ t.2.1)
  else none

theorem charge_pos {C M x r : ℝ} {t : ℕ × ℕ × ℤ} {p : ℝ × ℝ} (h : charge C M x r t = some p) :
    0 < p.2 := by
  unfold charge at h
  split_ifs at h with hc
  cases h
  have : (0 : ℝ) < t.1 := by exact_mod_cast (lt_of_lt_of_le two_pos hc.1)
  positivity

/-- One turn's `√`-budget. -/
theorem tsum_charge_le {S C M x r : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hS : ∑' b : ℕ, (if 2 ≤ b then ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) else 0)
      ≤ ENNReal.ofReal (S * Real.sqrt ((2 : ℝ) ^ (-C)))) :
    ∑' t : ℕ × ℕ × ℤ, budgetTerm (1 / 2) (charge C M x r t)
      ≤ ENNReal.ofReal (20 * S * Real.sqrt ((2 : ℝ) ^ (-C)) * Real.sqrt (M * r)) := by
  have hMr : 0 < M * r := mul_pos hM hr
  have hpt : ∀ t : ℕ × ℕ × ℤ, budgetTerm (1 / 2) (charge C M x r t) ≤
      (if 2 ≤ t.1 then (if ((t.1 : ℝ) ^ t.2.1)⁻¹ ≤ M * r then
        ENNReal.ofReal (Real.sqrt ((t.1 : ℝ) ^ (-C))) *
          ENNReal.ofReal (Real.sqrt ((t.1 : ℝ) ^ t.2.1)⁻¹) else 0) else 0) *
      (if |(t.2.2 : ℝ) - (t.1 : ℝ) ^ t.2.1 * x| ≤ 2 then 1 else 0) := by
    intro t
    unfold charge
    split_ifs with h1 h2 h3 h4 <;> simp_all [budgetTerm]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      Real.sqrt_div' _ (pow_nonneg (Nat.cast_nonneg _) _), div_eq_mul_inv,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  calc _ ≤ ∑' t : ℕ × ℕ × ℤ, _ := ENNReal.tsum_le_tsum hpt
    _ = ∑' b : ℕ, ∑' n : ℕ, ∑' a : ℤ, _ := by
        rw [ENNReal.tsum_prod']; congr 1; ext b; rw [ENNReal.tsum_prod']
    _ ≤ ∑' b : ℕ, ∑' n : ℕ, 5 * (if 2 ≤ b then (if ((b : ℝ) ^ n)⁻¹ ≤ M * r then
        ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) *
          ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ n)⁻¹) else 0) else 0) := by
        refine ENNReal.tsum_le_tsum fun b => ENNReal.tsum_le_tsum fun n => ?_
        show ∑' a : ℤ, (if 2 ≤ b then (if ((b : ℝ) ^ n)⁻¹ ≤ M * r then
          ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) *
            ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ n)⁻¹) else 0) else 0) *
          (if |(a : ℝ) - (b : ℝ) ^ n * x| ≤ 2 then 1 else 0) ≤ _
        rw [ENNReal.tsum_mul_left]
        refine (mul_le_mul_right (tsum_int_near_le _ 1) _).trans ?_
        rw [mul_one, mul_comm]
    _ = ∑' b : ℕ, 5 * (if 2 ≤ b then ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) *
          ∑' n : ℕ, (if ((b : ℝ) ^ n)⁻¹ ≤ M * r then
            ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ n)⁻¹) else 0) else 0) := by
        refine tsum_congr fun b => ?_
        split_ifs
        · rw [ENNReal.tsum_mul_left]
          congr 1; rw [← ENNReal.tsum_mul_left]; refine tsum_congr fun n => ?_; split_ifs <;> simp
        · simp
    _ ≤ ∑' b : ℕ, 5 * ((if 2 ≤ b then ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) else 0) *
          ENNReal.ofReal (4 * Real.sqrt (M * r))) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        gcongr
        split_ifs with hb
        · gcongr
          exact tsum_level_le (by exact_mod_cast hb) hMr
        · simp
    _ = 5 * ENNReal.ofReal (4 * Real.sqrt (M * r)) * ∑' b : ℕ,
          (if 2 ≤ b then ENNReal.ofReal (Real.sqrt ((b : ℝ) ^ (-C))) else 0) := by
        rw [← ENNReal.tsum_mul_left]; refine tsum_congr fun b => ?_; ring
    _ ≤ 5 * ENNReal.ofReal (4 * Real.sqrt (M * r)) *
          ENNReal.ofReal (S * Real.sqrt ((2 : ℝ) ^ (-C))) := by gcongr
    _ = _ := by
        rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring


/-- **Headline 1 (new).**  For all `0 < β < 1` and `ρ > 0` there is `K > 0` such that for every
`C ≥ 3` the Bugeaud 10.36 set `E C` is `(K·2^{−C}, β, 1/2, ρ)`-potential winning.

*Strategy.*  On Bob's turn `k`, Alice deletes every obstacle `N(a/bⁿ, b^{−C−n})` (`b ≥ 2`,
`n ≥ 0`, `a ∈ ℤ`) that meets `B_k` and whose level satisfies `ρ_k ≤ b^{−n}`, and
`ρ_{k−1} > b^{−n}` (no condition at `k = 0`).
*Legality.*  Centres of one level are `b^{−n} ≥ ρ_k` apart and obstacles are shorter than
`b^{−n}/8`, so `≤ 4` meet `B_k`.  For `k ≥ 1`, `b^{−n} ∈ [ρ_k, ρ_k/β)`, at most
`1 + log_b(1/β)` levels, radius `< b^{−C}ρ_k/β`; so the `√`-budget is
`≤ 4 β^{−1/2} Σ_{b≥2} (1 + log_b(1/β)) b^{−C/2} · ρ_k^{1/2}`, and
`Σ_b b^{−C/2} ≤ 2^{−C/2} Σ_b (2/b)^{3/2}` for `C ≥ 3`.  At `k = 0` (and at the first turn with
`ρ_k ≤ 1`, where `ρ_k ≥ min(ρ, β)`) the levels with `b^{−n} ≥ ρ_k` sum to
`≤ 4 (1 − 2^{−1/2})^{−1} Σ_b b^{−C/2}`, against `(αρ_k)^{1/2} ≥ (α min(ρ, β))^{1/2}`.
*Win.*  If the outcome `x` lies in an obstacle, that obstacle meets every `B_k`; since
`ρ_k → 0` it is charged on the first `k` with `ρ_k ≤ b^{−n}`, so `x` is in a deleted set.
Otherwise `‖bⁿx‖ > b^{−C}` for all `b, n`, i.e. `x ∈ E C`.

*Proved.*  The formal strategy is a stateless variant (`charge`): on turn `k` Alice deletes
every `N(a/bⁿ, b^{−C−n})` with `ρ_k ≤ b^{−n} ≤ M ρ_k` (`M = 1/β + 1/ρ`) and
`|a − bⁿ x_k| ≤ 2`; an obstacle may be charged more than once.  At most 5 centres per level
(`tsum_int_near_le`), a geometric sum over levels (`tsum_level_le`, `≤ 4√(Mρ_k)`) and
`Σ_b b^{−C/2} ≤ S·2^{−C/2}` (`exists_tsum_base_le`) give the budget (`tsum_charge_le`) with
`K = (20 S √M + 1)²`.  The first turn with `ρ_k ≤ b^{−n}` has `b^{−n} ≤ M ρ_k`. -/
theorem potentialWinning_E : EPotentialWinning := by
  intro β ρ hβ hβ1 hρ
  obtain ⟨S, hS0, hS⟩ := exists_tsum_base_le
  set M : ℝ := 1 / β + 1 / ρ with hM
  have hM0 : 0 < M := by positivity
  set K : ℝ := (20 * S * Real.sqrt M + 1) ^ 2
  refine ⟨K, by positivity, fun C hC => ?_⟩
  let σ : Strategy := fun k h i =>
    charge C M (h (Fin.last k)).1 (h (Fin.last k)).2 (Denumerable.ofNat (ℕ × ℕ × ℤ) i)
  refine ⟨σ, fun k h hpos => ⟨fun i p hp => charge_pos hp, ?_⟩, ?_⟩
  · set x := (h (Fin.last k)).1
    set r := (h (Fin.last k)).2
    have e : ∑' i : ℕ, budgetTerm (1 / 2) (σ k h i) =
        ∑' t : ℕ × ℕ × ℤ, budgetTerm (1 / 2) (charge C M x r t) :=
      (Denumerable.eqv (ℕ × ℕ × ℤ)).symm.tsum_eq (fun t => budgetTerm (1 / 2) (charge C M x r t))
    rw [e]
    refine (tsum_charge_le hM0 hpos (hS C hC)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity : (0:ℝ) ≤ K * 2 ^ (-C)) r,
      Real.sqrt_mul hM0.le, Real.sqrt_mul (by positivity : (0:ℝ) ≤ K),
      Real.sqrt_sq (by positivity)]
    have h1 : 0 ≤ Real.sqrt ((2 : ℝ) ^ (-C)) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
    nlinarith [mul_nonneg h1 h2]
  · intro B hB ht x hx
    by_cases hxE : x ∈ E C
    · exact Or.inl hxE
    right
    simp only [E, mem_setOf_eq, not_forall, not_lt] at hxE
    obtain ⟨b, hb, n, hbn⟩ := hxE
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le two_pos hb)
    have hbn0 : (0 : ℝ) < (b : ℝ) ^ n := pow_pos hb0 n
    set lvl : ℝ := ((b : ℝ) ^ n)⁻¹
    have hlvl : 0 < lvl := inv_pos.2 hbn0
    have hex : ∃ k, (B k).2 ≤ lvl :=
      ((ht.eventually (gt_mem_nhds hlvl)).exists).imp fun k hk => hk.le
    classical
    set k := Nat.find hex
    have hk : (B k).2 ≤ lvl := Nat.find_spec hex
    have hrpos : ∀ j, ρ ≤ (B 0).2 → 0 < (B j).2 := by
      intro j _
      induction j with
      | zero => linarith [hB.1]
      | succ j ih => nlinarith [(hB.2 j).1]
    have hlvlM : lvl ≤ M * (B k).2 := by
      rcases Nat.eq_zero_or_pos k with h0 | hs
      · rw [h0]
        have : lvl ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (le_trans (by norm_num) hb)))
        have h0' : 1 ≤ (B 0).2 / ρ := (one_le_div hρ).2 hB.1
        calc lvl ≤ 1 := this
          _ ≤ (B 0).2 / ρ := h0'
          _ ≤ M * (B 0).2 := by
            rw [hM, add_mul, div_eq_mul_one_div, mul_comm]
            have : 0 ≤ 1 / β * (B 0).2 := by have := hrpos 0 hB.1; positivity
            linarith
      · have hnot : ¬ (B (k - 1)).2 ≤ lvl := Nat.find_min hex (by omega)
        have hstep := (hB.2 (k - 1)).1
        rw [show k - 1 + 1 = k by omega] at hstep
        have hpos' := hrpos (k - 1) hB.1
        rw [hM, add_mul]
        have : lvl ≤ 1 / β * (B k).2 := by
          rw [one_div, inv_mul_eq_div, le_div_iff₀ hβ]; nlinarith
        have : 0 ≤ 1 / ρ * (B k).2 := by have := hrpos k hB.1; positivity
        linarith
    set a : ℤ := round ((b : ℝ) ^ n * x)
    have hxa : |(b : ℝ) ^ n * x - a| ≤ (b : ℝ) ^ (-C) := hbn
    have hxk : |x - (B k).1| ≤ (B k).2 := by
      have := hx k; simpa [Move.ball, Real.dist_eq] using this
    have hbC : (b : ℝ) ^ (-C) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (le_trans (by norm_num) hb)) (by linarith)
    have hhist : history B k (Fin.last k) = B k := by simp [history]
    refine ⟨k, Encodable.encode ((b, n, a) : ℕ × ℕ × ℤ),
      ((a : ℝ) / (b : ℝ) ^ n, (b : ℝ) ^ (-C) / (b : ℝ) ^ n), ?_, ?_⟩
    · show charge C M (history B k (Fin.last k)).1 (history B k (Fin.last k)).2
        (Denumerable.ofNat (ℕ × ℕ × ℤ) (Encodable.encode ((b, n, a) : ℕ × ℕ × ℤ))) = _
      rw [Denumerable.ofNat_encode, hhist]
      unfold charge
      rw [if_pos]
      refine ⟨hb, hk, hlvlM, ?_⟩
      have h1 : |(a : ℝ) - (b : ℝ) ^ n * (B k).1| ≤
          |(b : ℝ) ^ n * x - a| + (b : ℝ) ^ n * |x - (B k).1| := by
        rw [← abs_of_pos hbn0, ← abs_mul, abs_of_pos hbn0]
        calc _ = |-((b : ℝ) ^ n * x - a) + (b : ℝ) ^ n * (x - (B k).1)| := by ring_nf
          _ ≤ _ := (abs_add_le _ _).trans (by rw [abs_neg])
      have h2 : (b : ℝ) ^ n * |x - (B k).1| ≤ 1 := by
        calc _ ≤ (b : ℝ) ^ n * lvl := mul_le_mul_of_nonneg_left (hxk.trans hk) hbn0.le
          _ = 1 := mul_inv_cancel₀ hbn0.ne'
      linarith
    · show dist x ((a : ℝ) / (b : ℝ) ^ n) ≤ (b : ℝ) ^ (-C) / (b : ℝ) ^ n
      rw [Real.dist_eq, le_div_iff₀ hbn0]
      calc |x - a / (b : ℝ) ^ n| * (b : ℝ) ^ n = |(b : ℝ) ^ n * x - a| := by
            rw [← abs_of_pos hbn0, ← abs_mul, abs_of_pos hbn0]; congr 1; field_simp
        _ ≤ _ := hxa

/-! ## Headline 2: the base-2 upper bound -/

/-! ### Proof of headline 2: run-free words and a dyadic cover -/

/-- Indices `a < 2^N` whose `N`-bit word has no window of `m` equal bits. -/
def runFree (m N : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ N)).filter fun a =>
    ∀ i < N + 1, i + m ≤ N → (a / 2 ^ i) % 2 ^ m ≠ 0 ∧ (a / 2 ^ i) % 2 ^ m ≠ 2 ^ m - 1

/-- Append a run of `j` bits opposite to the last bit of `a'`. -/
def appendRun (j a' : ℕ) : ℕ := a' * 2 ^ j + if a' % 2 = 0 then 2 ^ j - 1 else 0

theorem div_mem_runFree {m N j a : ℕ} (ha : a ∈ runFree m N) (hj : j ≤ N) :
    a / 2 ^ j ∈ runFree m (N - j) := by
  simp only [runFree, Finset.mem_filter, Finset.mem_range] at ha ⊢
  refine ⟨?_, fun i _ hi => ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hj]; exact ha.1
  · rw [Nat.div_div_eq_div_mul, ← pow_add]
    exact ha.2 (j + i) (by omega) (by omega)

theorem runFree_subset {m N : ℕ} (hN : m ≤ N) :
    runFree m N ⊆ (Finset.Ico 1 m).biUnion fun j => (runFree m (N - j)).image (appendRun j) := by
  intro a ha
  have hw := (Finset.mem_filter.1 ha).2 0 (by omega) (by omega)
  simp only [pow_zero, Nat.div_one] at hw
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; have := hw.1; simp [Nat.mod_one] at this
    · exact h
  simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image]
  rcases Nat.mod_two_eq_zero_or_one a with h2 | h2
  · -- trailing run of zeros
    have hex : ∃ j, a % 2 ^ (j + 1) ≠ 0 := ⟨m - 1, by rw [Nat.sub_add_cancel hm]; exact hw.1⟩
    classical
    set j := Nat.find hex
    have hspec : a % 2 ^ (j + 1) ≠ 0 := Nat.find_spec hex
    have hj1 : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      rw [this] at hspec; exact hspec (by simpa using h2)
    have hjm : j < m := by
      have := Nat.find_min' hex (show a % 2 ^ (m - 1 + 1) ≠ 0 by
        rw [Nat.sub_add_cancel hm]; exact hw.1)
      omega
    have hz : a % 2 ^ j = 0 := by
      have := Nat.find_min hex (show j - 1 < j by omega)
      rw [Nat.sub_add_cancel hj1] at this; push Not at this; exact this
    have hodd : (a / 2 ^ j) % 2 = 1 := by
      have := hspec
      rw [Nat.mod_pow_succ, hz, zero_add] at this
      rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ j) with h | h
      · rw [h, mul_zero] at this; exact absurd rfl this
      · exact h
    refine ⟨j, ⟨hj1, hjm⟩, a / 2 ^ j, div_mem_runFree ha (by omega), ?_⟩
    simp only [appendRun, hodd, one_ne_zero, if_false, add_zero]
    have := Nat.div_add_mod a (2 ^ j)
    rw [hz] at this; linarith
  · -- trailing run of ones
    have hex : ∃ j, a % 2 ^ (j + 1) ≠ 2 ^ (j + 1) - 1 :=
      ⟨m - 1, by rw [Nat.sub_add_cancel hm]; exact hw.2⟩
    classical
    set j := Nat.find hex
    have hspec : a % 2 ^ (j + 1) ≠ 2 ^ (j + 1) - 1 := Nat.find_spec hex
    have hj1 : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      rw [this] at hspec; exact hspec (by simpa using h2)
    have hjm : j < m := by
      have := Nat.find_min' hex (show a % 2 ^ (m - 1 + 1) ≠ 2 ^ (m - 1 + 1) - 1 by
        rw [Nat.sub_add_cancel hm]; exact hw.2)
      omega
    have hz : a % 2 ^ j = 2 ^ j - 1 := by
      have := Nat.find_min hex (show j - 1 < j by omega)
      rw [Nat.sub_add_cancel hj1] at this; push Not at this; exact this
    have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have heven : (a / 2 ^ j) % 2 = 0 := by
      have := hspec
      rw [Nat.mod_pow_succ, hz, pow_succ] at this
      rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ j) with h | h
      · exact h
      · rw [h] at this; omega
    refine ⟨j, ⟨hj1, hjm⟩, a / 2 ^ j, div_mem_runFree ha (by omega), ?_⟩
    simp only [appendRun, heven, if_true]
    have := Nat.div_add_mod a (2 ^ j)
    rw [hz] at this; linarith

theorem card_runFree_le_sum {m N : ℕ} (hN : m ≤ N) :
    (runFree m N).card ≤ ∑ j ∈ Finset.Ico 1 m, (runFree m (N - j)).card :=
  (Finset.card_le_card (runFree_subset hN)).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le))

theorem geom_telescope (ν : ℝ) {m N : ℕ} (h1 : 1 ≤ m) (h : m ≤ N) :
    (ν - 1) * ∑ j ∈ Finset.Ico 1 m, ν ^ (N - j) = ν ^ N - ν ^ (N + 1 - m) := by
  induction m, h1 using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, mul_add, ih (by omega),
      show N + 1 - m = N - m + 1 by omega, show N + 1 - (m + 1) = N - m by omega, pow_succ]
    ring

/-- The growth rate `μ = 2 − 2^{1−m}`. -/
noncomputable def runRate (m : ℕ) : ℝ := 2 - 2 / 2 ^ m

theorem runRate_key {m : ℕ} (hm : 1 ≤ m) : runRate m ^ (m - 1) * (2 - runRate m) ≤ 1 := by
  have hε : runRate m = 2 * (1 - 1 / 2 ^ m) := by unfold runRate; ring
  have h0 : 0 ≤ 1 - 1 / (2 : ℝ) ^ m := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have h1 : 1 - 1 / (2 : ℝ) ^ m ≤ 1 := by
    have : 0 ≤ 1 / (2 : ℝ) ^ m := by positivity
    linarith
  calc runRate m ^ (m - 1) * (2 - runRate m)
      = (1 - 1 / 2 ^ m) ^ (m - 1) * (2 ^ (m - 1) * 2 / 2 ^ m) := by
        rw [hε, mul_pow]; ring
    _ = (1 - 1 / 2 ^ m) ^ (m - 1) := by
        rw [← pow_succ, Nat.sub_add_cancel hm, div_self (by positivity), mul_one]
    _ ≤ 1 := pow_le_one₀ h0 h1

theorem card_runFree_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ((runFree m N).card : ℝ) ≤ 2 * runRate m ^ N := by
  have hν1 : 1 ≤ runRate m := by
    unfold runRate
    have : (2 : ℝ) / 2 ^ m ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    linarith
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases lt_or_ge N m with hN | hN
  · have hc : ((runFree m N).card : ℝ) ≤ 2 ^ N := by
      have : (runFree m N).card ≤ 2 ^ N :=
        (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
      exact_mod_cast this
    refine hc.trans ?_
    have hε : runRate m = 2 * (1 + (-(1 / 2 ^ m))) := by unfold runRate; ring
    rw [hε, mul_pow]
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / 2 ^ m) by
      have : 1 / (2 : ℝ) ^ m ≤ 1 := by
        rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
      linarith) N
    have hN2 : (N : ℝ) * (1 / 2 ^ m) ≤ 1 / 2 := by
      have : (N : ℝ) + 1 ≤ 2 ^ (m - 1) := by
        have := Nat.lt_two_pow_self (n := m - 1)
        exact_mod_cast (show N + 1 ≤ 2 ^ (m - 1) by omega)
      have e : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hm]
      rw [e, mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) (m - 1)]
    have : (0 : ℝ) < 2 ^ N := by positivity
    nlinarith
  · have hrec := card_runFree_le_sum hN
    have hsum : (∑ j ∈ Finset.Ico 1 m, ((runFree m (N - j)).card : ℝ)) ≤
        2 * ∑ j ∈ Finset.Ico 1 m, runRate m ^ (N - j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => ih _ (by simp at hj; omega)
    have hcast : ((runFree m N).card : ℝ) ≤ ∑ j ∈ Finset.Ico 1 m, ((runFree m (N - j)).card : ℝ) := by
      exact_mod_cast hrec
    refine hcast.trans (hsum.trans ?_)
    gcongr
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have : m = 1 := by omega
      subst this; simp; positivity
    have hν : 1 < runRate m := by
      unfold runRate
      have : (2 : ℝ) / 2 ^ m < 1 := by
        rw [div_lt_one (by positivity)]
        calc (2 : ℝ) < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm2
      linarith
    refine le_of_mul_le_mul_left ?_ (sub_pos.2 hν)
    rw [geom_telescope _ hm hN]
    set ν := runRate m
    set P := ν ^ (N + 1 - m)
    have hP : 0 ≤ P := by positivity
    have e1 : ν ^ N = P * ν ^ (m - 1) := by
      rw [← pow_add]; congr 1; omega
    have hk := mul_le_mul_of_nonneg_left (runRate_key hm) hP
    rw [e1]
    nlinarith

open NormalNumbers.UniformBad (dnear dnear_le_abs_sub) in
theorem floor_mem_runFree {C : ℝ} {m : ℕ} (hCm : C ≤ m) {ξ : ℝ} (hξ : ξ ∈ E₂ C) {z : ℤ}
    (hz : (z : ℝ) ≤ ξ) (hz1 : ξ < z + 1) (N : ℕ) :
    ⌊(2 : ℝ) ^ N * (ξ - z)⌋₊ ∈ runFree m N := by
  have hx0 : 0 ≤ ξ - z := by linarith
  have hεC : 1 / (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (-C) := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  simp only [runFree, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, fun i _ hi => ?_⟩
  · rw [Nat.floor_lt (by positivity)]
    push_cast
    have : (0 : ℝ) < 2 ^ N := by positivity
    nlinarith
  set n := N - i - m
  set y := (2 : ℝ) ^ n * (ξ - z) with hy
  have hy0 : 0 ≤ y := by positivity
  have hN : (2 : ℝ) ^ N * (ξ - z) / (2 ^ i : ℕ) = (2 : ℝ) ^ m * y := by
    rw [hy]; push_cast
    rw [show N = n + m + i by omega, pow_add, pow_add]; field_simp
  set u := ⌊(2 : ℝ) ^ m * y⌋₊
  have hu : ⌊(2 : ℝ) ^ N * (ξ - z)⌋₊ / 2 ^ i = u := by
    rw [← Nat.floor_div_natCast, hN]
  have hq : u / 2 ^ m = ⌊y⌋₊ := by
    simp only [u]
    rw [← Nat.floor_div_natCast]; push_cast; congr 1; field_simp
  rw [hu]
  set q := ⌊y⌋₊
  have hdecomp : (u : ℝ) = 2 ^ m * q + (u % 2 ^ m : ℕ) := by
    have := Nat.div_add_mod u (2 ^ m)
    rw [hq] at this
    exact_mod_cast this.symm
  have hfl1 : (u : ℝ) ≤ 2 ^ m * y := Nat.floor_le (by positivity)
  have hfl2 : 2 ^ m * y < u + 1 := Nat.lt_floor_add_one _
  have hpm : (0 : ℝ) < 2 ^ m := by positivity
  have hE := hξ n
  have hint : (2 : ℝ) ^ n * ξ - (((2 : ℤ) ^ n * z + q : ℤ) : ℝ) = y - q := by
    push_cast; rw [hy]; ring
  have hint1 : (((2 : ℤ) ^ n * z + q + 1 : ℤ) : ℝ) - (2 : ℝ) ^ n * ξ = q + 1 - y := by
    push_cast; rw [hy]; ring
  constructor
  · intro h0
    rw [h0] at hdecomp
    push_cast at hdecomp
    have h1 : y - q < 1 / 2 ^ m := by
      rw [lt_div_iff₀ hpm]; nlinarith
    have := dnear_le_abs_sub ((2 : ℝ) ^ n * ξ) ((2 : ℤ) ^ n * z + q)
    rw [hint, abs_of_nonneg (by nlinarith)] at this
    linarith
  · intro h1
    rw [h1] at hdecomp
    have hp1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    push_cast [hp1] at hdecomp
    have h2 : q + 1 - y ≤ 1 / 2 ^ m := by
      rw [le_div_iff₀ hpm]; nlinarith
    have := dnear_le_abs_sub ((2 : ℝ) ^ n * ξ) ((2 : ℤ) ^ n * z + q + 1)
    rw [abs_sub_comm, hint1, abs_of_nonneg (by nlinarith)] at this
    linarith

theorem one_le_runRate {m : ℕ} (hm : 1 ≤ m) : 1 ≤ runRate m := by
  unfold runRate
  have : (2 : ℝ) / 2 ^ m ≤ 1 := by
    rw [div_le_one (by positivity)]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  linarith

theorem dimH_E₂_Ico_le {C : ℝ} {m : ℕ} (hm : 1 ≤ m) (hCm : C ≤ m) (z : ℤ) :
    dimH (E₂ C ∩ Ico (z : ℝ) (z + 1)) ≤ ENNReal.ofReal (Real.logb 2 (runRate m)) := by
  set ν := runRate m
  have hν1 := one_le_runRate hm
  set d := Real.logb 2 ν
  have hd0 : 0 ≤ d := Real.logb_nonneg (by norm_num) hν1
  have h2d : (2 : ℝ) ^ d = ν := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  rw [show ENNReal.ofReal d = ((d.toNNReal : NNReal) : ℝ≥0∞) from rfl]
  apply dimH_le_of_hausdorffMeasure_ne_top
  rw [Real.coe_toNNReal _ hd0]
  refine ne_top_of_le_ne_top (b := 2) ENNReal.ofNat_ne_top ?_
  refine (MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (ι := fun N => ↥(runFree m N)) (l := atTop) d _
    (fun N => ENNReal.ofReal ((1 / 2 : ℝ) ^ N)) ?_
    (fun N a => Icc ((z : ℝ) + (a : ℕ) / 2 ^ N) (z + ((a : ℕ) + 1) / 2 ^ N)) ?_ ?_).trans ?_
  · rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  · refine Eventually.of_forall fun N a => ?_
    rw [Real.ediam_Icc]
    refine le_of_eq (congrArg _ ?_)
    rw [one_div_pow]; ring
  · refine Eventually.of_forall fun N ξ hξ => ?_
    simp only [mem_iUnion]
    have hz : (z : ℝ) ≤ ξ := hξ.2.1
    have hx0 : 0 ≤ ξ - z := by linarith
    have hpos : (0 : ℝ) < 2 ^ N := by positivity
    refine ⟨⟨_, floor_mem_runFree hCm hξ.1 hξ.2.1 hξ.2.2 N⟩, ?_, ?_⟩
    · have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ N * (ξ - z) by positivity)
      simp only
      rw [← le_sub_iff_add_le', div_le_iff₀ hpos]; linarith
    · have := Nat.lt_floor_add_one ((2 : ℝ) ^ N * (ξ - z))
      simp only
      rw [← sub_le_iff_le_add', le_div_iff₀ hpos]; linarith
  · refine (liminf_le_liminf (Eventually.of_forall fun N => ?_)).trans_eq (liminf_const (2 : ℝ≥0∞))
    calc ∑ a : ↥(runFree m N), ediam (Icc ((z : ℝ) + (a : ℕ) / 2 ^ N) (z + ((a : ℕ) + 1) / 2 ^ N)) ^ d
        = ∑ _a : ↥(runFree m N), ENNReal.ofReal (1 / ν ^ N) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Real.ediam_Icc, show (z : ℝ) + ((a : ℕ) + 1) / 2 ^ N - (z + (a : ℕ) / 2 ^ N) =
            (1 / 2) ^ N by rw [one_div_pow]; ring,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hd0]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
            Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, h2d, Real.rpow_natCast, one_div_pow]
      _ = (runFree m N).card * ENNReal.ofReal (1 / ν ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ 2 := by
          have hc := card_runFree_le hm N
          have hνN : 0 < ν ^ N := by positivity
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_one_div, div_le_iff₀ hνN]; linarith

/-- **Headline 2.**  `dim_H {ξ : ‖2ⁿξ‖ > 2^{−C} ∀ n} ≤ 1 − 2^{−(C+1)}` for `C ≥ 1`.

*Proof sketch.*  With `m = ⌈C⌉`, such `ξ` has no run of `m` equal binary digits (a run of `m`
zeros after position `n` gives `{2ⁿξ} ≤ 2^{−m} ≤ 2^{−C}`, ones symmetrically).  Words of length
`N` with all runs `< m` number `a_N = a_{N−1} + ⋯ + a_{N−m+1}`, so `a_N ≤ 2μ^N` for any `μ`
with `μ^{m−1}(2 − μ) ≤ 1`; `μ = 2 − 2^{1−m}` qualifies.  Covering `E₂ C ∩ [j, j+1]` by `a_N`
dyadic intervals gives `dim_H ≤ log₂ μ = 1 + log₂(1 − 2^{−m}) ≤ 1 − 2^{−m} ≤ 1 − 2^{−(C+1)}`,
and `E₂ C` is a countable union of translates.

*Proved* (`card_runFree_le`, `floor_mem_runFree`, `dimH_E₂_Ico_le`). -/
theorem dimH_E₂_le {C : ℝ} (hC : 1 ≤ C) :
    dimH (E₂ C) ≤ ENNReal.ofReal (1 - 2 ^ (-(C + 1))) := by
  set m := ⌈C⌉₊
  have hCm : C ≤ m := Nat.le_ceil C
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := hC.trans hCm
    exact_mod_cast this
  have hmC : (m : ℝ) < C + 1 := Nat.ceil_lt_add_one (by linarith)
  have hcov : E₂ C ⊆ ⋃ z : ℤ, (E₂ C ∩ Ico (z : ℝ) (z + 1)) := fun ξ hξ =>
    mem_iUnion.2 ⟨⌊ξ⌋, hξ, Int.floor_le ξ, Int.lt_floor_add_one ξ⟩
  refine (dimH_mono hcov).trans ?_
  rw [dimH_iUnion]
  refine iSup_le fun z => (dimH_E₂_Ico_le hm1 hCm z).trans (ENNReal.ofReal_le_ofReal ?_)
  -- logb 2 (2 (1 - ε)) ≤ 1 - ε ≤ 1 - 2^{-(C+1)}
  set ε : ℝ := 1 / 2 ^ m
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := by
    simp only [ε]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 1 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm1
    linarith
  have hεC : (2 : ℝ) ^ (-(C + 1)) ≤ ε := by
    simp only [ε]
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hν : runRate m = 2 * (1 - ε) := by unfold runRate; simp only [ε]; ring
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  rw [hν, Real.logb, Real.log_mul (by norm_num) (by linarith), div_le_iff₀ hl2]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - ε by linarith)
  nlinarith

/-! ## Wiring -/

theorem dimH_le_one (s : Set ℝ) : dimH s ≤ 1 :=
  (dimH_mono (subset_univ s)).trans_eq Real.dimH_univ

theorem two_rpow_neg_anti {C C₀ : ℝ} (h : C₀ ≤ C) : (2 : ℝ) ^ (-C) ≤ (2 : ℝ) ^ (-C₀) :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg h)

/-- For `K, X > 0` there is `C₀ ≥ 3` with `K·2^{−C} ≤ X` for all `C ≥ C₀`. -/
theorem exists_C₀ {K X : ℝ} (hK : 0 < K) (hX : 0 < X) :
    ∃ C₀ : ℝ, 3 ≤ C₀ ∧ ∀ C, C₀ ≤ C → K * (2 : ℝ) ^ (-C) ≤ X := by
  refine ⟨max 3 (Real.logb 2 (K / X)), le_max_left _ _, fun C hC => ?_⟩
  have h1 : (2 : ℝ) ^ (-C) ≤ (2 : ℝ) ^ (-Real.logb 2 (K / X)) :=
    two_rpow_neg_anti ((le_max_right _ _).trans hC)
  rw [Real.rpow_neg (by norm_num) (Real.logb 2 (K / X)),
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at h1
  calc K * 2 ^ (-C) ≤ K * (K / X)⁻¹ := mul_le_mul_of_nonneg_left h1 hK.le
    _ = X := by field_simp

theorem abs_log_quarter : |Real.log (1 / 4 : ℝ)| = Real.log 4 := by
  rw [one_div, Real.log_inv, abs_neg, abs_of_pos (Real.log_pos (by norm_num))]

/-- The BFS side condition on `[0,1]` with `β = 1/4`, `c = 1/2`. -/
theorem cond_interval {K₂ α : ℝ} (hK₂ : 0 < K₂) (_hα : 0 ≤ α) (h : α ≤ 1 / (4 * K₂ ^ 2)) :
    α ^ (1 / 2 : ℝ) ≤ (1 - (1 / 4 : ℝ) ^ ((1 : ℝ) - 1 / 2)) / K₂ := by
  have hq : (1 / 4 : ℝ) ^ ((1 : ℝ) - 1 / 2) = 1 / 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e : (1 / (2 * K₂)) ^ 2 = 1 / (4 * K₂ ^ 2) := by field_simp; ring
  rw [hq, ← Real.sqrt_eq_rpow]
  calc √α ≤ √((1 / (2 * K₂)) ^ 2) := Real.sqrt_le_sqrt (by rw [e]; exact h)
    _ = 1 / (2 * K₂) := Real.sqrt_sq (by positivity)
    _ = (1 - 1 / 2) / K₂ := by field_simp; ring

/-- `(√a + √b)² < η` when `a + b < η/2`, in the exponent form `BFS (4.4)` produces. -/
theorem sum_sqrt_rpow_lt {a b η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b < η / 2) :
    (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)⁻¹ < η := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num,
    Real.rpow_two]
  nlinarith [sq_nonneg (√a - √b), Real.sq_sqrt ha, Real.sq_sqrt hb]

theorem sum_sqrt_rpow_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 < (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)⁻¹ := by
  apply Real.rpow_pos_of_pos
  have := Real.rpow_pos_of_pos ha (1 / 2 : ℝ)
  have := Real.rpow_nonneg hb (1 / 2 : ℝ)
  linarith

theorem half_lt_log2_div_log3 : (1 / 2 : ℝ) < Real.log 2 / Real.log 3 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ h3]
  have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

/-- The generic step: if `S` is `(α, 1/4, 1/2, r)`-potential winning for arbitrarily small `α`,
then `dim_H (S ∩ J) ≥ δ`, given BFS Theorem 5.5 on `J`. -/
theorem le_dimH_of_potentialWinning {J : Set ℝ} {δ : ℝ} (hJ : Literature.BFSPotentialDim J δ)
    (hδ : 1 / 2 < δ) {S : Set ℝ} {x₀ r : ℝ} (hx₀ : x₀ ∈ J) (hr : 0 < r)
    (hS : ∀ η : ℝ, 0 < η → ∃ α, 0 < α ∧ α < η ∧ PotentialWinning S α (1 / 4) (1 / 2) r) :
    ENNReal.ofReal δ ≤ dimH (S ∩ J) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hBFS⟩ := hJ
  have hδ0 : 0 < δ := by linarith
  set M : ℝ := (1 - (1 / 4 : ℝ) ^ (δ - 1 / 2)) / K₂ with hM
  have hq : (1 / 4 : ℝ) ^ (δ - 1 / 2) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hMpos : 0 < M := div_pos (by linarith) hK₂
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine le_of_forall_lt fun t ht => ?_
  have htop : t ≠ ⊤ := ne_top_of_lt ht
  set t' := t.toReal with ht'def
  have ht' : t' < δ := by
    have h2 := ht
    rw [← ENNReal.ofReal_toReal htop] at h2
    exact (ENNReal.ofReal_lt_ofReal_iff hδ0).1 h2
  have ht0 : 0 ≤ t' := ENNReal.toReal_nonneg
  set g := δ - t' with hgdef
  have hg : 0 < g := by linarith
  have hX : 0 < g * Real.log 4 / (2 * K₁) := by positivity
  set η := min (M ^ 2) ((g * Real.log 4 / (2 * K₁)) ^ δ⁻¹)
  have hη : 0 < η := lt_min (by positivity) (Real.rpow_pos_of_pos hX _)
  obtain ⟨α, hα, hαη, hPW⟩ := hS η hη
  have hcond : α ^ (1 / 2 : ℝ) ≤ (1 - (1 / 4 : ℝ) ^ (δ - 1 / 2)) / K₂ := by
    rw [← Real.sqrt_eq_rpow, ← hM]
    calc √α ≤ √(M ^ 2) := Real.sqrt_le_sqrt (hαη.le.trans (min_le_left _ _))
      _ = M := Real.sqrt_sq hMpos.le
  have hsmall : K₁ * α ^ δ / |Real.log (1 / 4)| < g := by
    rw [abs_log_quarter]
    have h1 : α ^ δ < g * Real.log 4 / (2 * K₁) := by
      calc α ^ δ < ((g * Real.log 4 / (2 * K₁)) ^ δ⁻¹) ^ δ :=
            Real.rpow_lt_rpow hα.le (hαη.trans_le (min_le_right _ _)) hδ0
        _ = _ := Real.rpow_inv_rpow hX.le hδ0.ne'
    rw [div_lt_iff₀ hL]
    calc K₁ * α ^ δ < K₁ * (g * Real.log 4 / (2 * K₁)) := mul_lt_mul_of_pos_left h1 hK₁
      _ = g * Real.log 4 / 2 := by field_simp
      _ < g * Real.log 4 := by linarith [mul_pos hg hL]
  have hdim := hBFS S α (1 / 4) (1 / 2) r hα (by norm_num) le_rfl (by norm_num) hδ hr hcond hPW
    x₀ hx₀ r le_rfl
  calc t = ENNReal.ofReal t' := (ENNReal.ofReal_toReal htop).symm
    _ < ENNReal.ofReal (δ - K₁ * α ^ δ / |Real.log (1 / 4)|) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    _ ≤ dimH (S ∩ J ∩ closedBall x₀ r) := hdim
    _ ≤ dimH (S ∩ J) := dimH_mono inter_subset_left

/-- **`1 − dim_H E C ≍ 2^{−C}`** (conditional on headline 1 and BFS 5.5 on `[0,1]`; the upper
half is headline 2). -/
theorem codim_E_asymp (hE : EPotentialWinning) (hJ : Literature.BFSDimInterval) :
    ∃ κ C₀ : ℝ, 0 < κ ∧ ∀ C : ℝ, C₀ ≤ C →
      ENNReal.ofReal (1 - κ * 2 ^ (-C)) ≤ dimH (E C) ∧
        dimH (E C) ≤ ENNReal.ofReal (1 - 2 ^ (-(C + 1))) := by
  obtain ⟨K, hK, hPW⟩ := hE (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K₁, K₂, hK₁, hK₂, hBFS⟩ := hJ
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨C₀, hC₀3, hC₀⟩ := exists_C₀ hK (show 0 < 1 / (4 * K₂ ^ 2) by positivity)
  refine ⟨K₁ * K / Real.log 4, C₀, by positivity, fun C hC => ⟨?_, ?_⟩⟩
  · have hC3 : 3 ≤ C := hC₀3.trans hC
    have hα : 0 < K * (2 : ℝ) ^ (-C) := mul_pos hK (by positivity)
    have hdim := hBFS (E C) _ (1 / 4) (1 / 2) (1 / 2) hα (by norm_num) le_rfl (by norm_num)
      (by norm_num) (by norm_num) (cond_interval hK₂ hα.le (hC₀ C hC)) (hPW C hC3) (1 / 2)
      ⟨by norm_num, by norm_num⟩ (1 / 2) le_rfl
    rw [Real.rpow_one, abs_log_quarter] at hdim
    calc ENNReal.ofReal (1 - K₁ * K / Real.log 4 * 2 ^ (-C))
        = ENNReal.ofReal (1 - K₁ * (K * 2 ^ (-C)) / Real.log 4) := by congr 1; ring
      _ ≤ _ := hdim
      _ ≤ dimH (E C) := dimH_mono (inter_subset_left.trans inter_subset_left)
  · exact (dimH_mono (E_subset_E₂ C)).trans (dimH_E₂_le (by linarith))

/-- `U` is `(α, 1/4, 1/2, ρ)`-potential winning for arbitrarily small `α`. -/
theorem smallPW_U (hE : EPotentialWinning) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ η : ℝ, 0 < η → ∃ α, 0 < α ∧ α < η ∧ PotentialWinning U α (1 / 4) (1 / 2) ρ := by
  intro η hη
  obtain ⟨K, hK, hPW⟩ := hE (1 / 4) ρ (by norm_num) (by norm_num) hρ
  obtain ⟨C₀, hC₀3, hC₀⟩ := exists_C₀ hK (half_pos hη)
  exact ⟨K * 2 ^ (-C₀), mul_pos hK (by positivity), (hC₀ C₀ le_rfl).trans_lt (half_lt_self hη),
    (hPW C₀ hC₀3).mono_set (E_subset_U C₀)⟩

/-- **`dim_H U = 1`** (conditional on headline 1 and BFS 5.5 on `[0,1]`). -/
theorem dimH_U_eq_one_of (hE : EPotentialWinning) (hJ : Literature.BFSDimInterval) :
    dimH U = 1 := by
  refine le_antisymm (dimH_le_one U) ?_
  have h := le_dimH_of_potentialWinning hJ (by norm_num : (1 / 2 : ℝ) < 1)
    (⟨by norm_num, by norm_num⟩ : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) < 1 / 2)
    (smallPW_U hE (by norm_num : (0 : ℝ) < 1 / 2))
  rw [ENNReal.ofReal_one] at h
  exact h.trans (dimH_mono inter_subset_left)

/-- **`dim_H (U ∩ cantorSet) ≥ log 2/log 3`** (conditional on headline 1 and BFS 5.5 on the
Cantor set). -/
theorem le_dimH_U_inter_cantor_of (hE : EPotentialWinning) (hJ : Literature.BFSDimCantor) :
    ENNReal.ofReal (Real.log 2 / Real.log 3) ≤ dimH (U ∩ cantorSet) :=
  le_dimH_of_potentialWinning hJ half_lt_log2_div_log3 zero_mem_cantorSet
    (by norm_num : (0 : ℝ) < 1 / 2) (smallPW_U hE (by norm_num))

/-- `U ∩ Bad` is `(α, 1/4, 1/2, 1/8)`-potential winning for arbitrarily small `α`. -/
theorem smallPW_U_Bad (hE : EPotentialWinning) (hB : Literature.BFSBadPotential) :
    ∀ η : ℝ, 0 < η → ∃ α, 0 < α ∧ α < η ∧
      PotentialWinning (U ∩ Bad) α (1 / 4) (1 / 2) (1 / 8) := by
  intro η hη
  obtain ⟨K, hK, hPW⟩ := hE (1 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀3, hC₀⟩ := exists_C₀ hK (show 0 < η / 8 by positivity)
  set ε := min (1 / 4 : ℝ) (η / 64) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε4 : ε ≤ 1 / 4 := min_le_left _ _
  have hεη : ε ≤ η / 64 := min_le_right _ _
  have hcondε : (ε / (1 - ε)) ^ 2 ≤ 1 / 4 := by
    have h1 : ε / (1 - ε) ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc (ε / (1 - ε)) ^ 2 ≤ (1 / 2) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg hε.le (by linarith)) h1 2
      _ = 1 / 4 := by norm_num
  have hBA := hB ε (1 / 4) (1 / 2) hε (by linarith) hcondε (by norm_num) (by norm_num)
  rw [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at hBA
  set a := 2 * ε / ((1 - 2 * ε) * (1 / 4)) with hadef
  have hden : 0 < (1 - 2 * ε) * (1 / 4) := by nlinarith
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hden.le
  have ha : a ≤ η / 4 := by
    rw [hadef, div_le_iff₀ hden]
    nlinarith
  set b := K * (2 : ℝ) ^ (-C₀)
  have hb : 0 < b := mul_pos hK (by positivity)
  have hI := (hPW C₀ hC₀3).inter (by norm_num) hb.le ha0 hBA
  refine ⟨_, sum_sqrt_rpow_pos hb ha0, sum_sqrt_rpow_lt hb.le ha0 ?_, hI.mono_set ?_⟩
  · have := hC₀ C₀ le_rfl
    linarith
  · rintro x ⟨hx1, hx2⟩
    exact ⟨E_subset_U C₀ hx1, mem_iUnion₂.2 ⟨ε, hε, hx2⟩⟩

/-- **`dim_H (U ∩ BAD ∩ cantorSet) ≥ log 2/log 3`** (conditional on headline 1, BFS 5.5 on the
Cantor set, and BFS Lemma 3.10). -/
theorem le_dimH_U_inter_Bad_inter_cantor_of (hE : EPotentialWinning)
    (hJ : Literature.BFSDimCantor) (hB : Literature.BFSBadPotential) :
    ENNReal.ofReal (Real.log 2 / Real.log 3) ≤ dimH (U ∩ Bad ∩ cantorSet) :=
  le_dimH_of_potentialWinning hJ half_lt_log2_div_log3 zero_mem_cantorSet
    (by norm_num : (0 : ℝ) < 1 / 8) (smallPW_U_Bad hE hB)

/-! ## Guards (known-false siblings) -/

/-- A fixed `E C` misses the gap `(−2^{−C}, 2^{−C})` (`b = 2`, `n = 0`). -/
theorem E_disjoint_gap (C : ℝ) : Disjoint (E C) (Ioo (-(2 : ℝ) ^ (-C)) ((2 : ℝ) ^ (-C))) := by
  rw [Set.disjoint_left]
  intro ξ hξ hgap
  have h := hξ 2 le_rfl 0
  simp only [Nat.cast_ofNat, pow_zero, one_mul] at h
  have h0 := dnear_le_abs_sub ξ 0
  simp only [Int.cast_zero, sub_zero] at h0
  have : |ξ| < (2 : ℝ) ^ (-C) := abs_lt.2 hgap
  linarith

/-- **Guard: one fixed exponent is not winning.**  For each `C`, `E C` is not
`(α, 1/4, 1/2, 2^{−C}/2)`-potential winning for small `α`: Bob opens inside the gap. -/
theorem not_potentialWinning_E_small (hJ : Literature.BFSDimInterval) (C : ℝ) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ →
      ¬ PotentialWinning (E C) α (1 / 4) (1 / 2) ((2 : ℝ) ^ (-C) / 2) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hBFS⟩ := hJ
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨min (1 / (4 * K₂ ^ 2)) (Real.log 4 / K₁), lt_min (by positivity) (div_pos hL hK₁),
    fun α hα hα₀ hPW => ?_⟩
  have hr : 0 < (2 : ℝ) ^ (-C) / 2 := by positivity
  have hdim := hBFS (E C) α (1 / 4) (1 / 2) _ hα (by norm_num) le_rfl (by norm_num)
    (by norm_num) hr (cond_interval hK₂ hα.le (hα₀.le.trans (min_le_left _ _))) hPW 0
    ⟨le_rfl, zero_le_one⟩ _ le_rfl
  have hempty : E C ∩ Icc 0 1 ∩ closedBall 0 ((2 : ℝ) ^ (-C) / 2) = ∅ := by
    ext ξ
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hξ hb
    rw [mem_closedBall, Real.dist_eq, sub_zero] at hb
    exact disjoint_left.1 (E_disjoint_gap C) hξ.1 (abs_lt.1 (by linarith))
  rw [hempty, dimH_empty, Real.rpow_one, abs_log_quarter, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at hdim
  have h1 : K₁ * α < Real.log 4 := by
    have := hα₀.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hK₁, mul_comm] at this
  have h2 : K₁ * α / Real.log 4 < 1 := by rwa [div_lt_one hL]
  linarith

/-- **Guard: normality is not winning** (given headline 1).  No set of base-`b` normal numbers
is `(α, 1/4, 1/2, 1/2)`-potential winning for all `α > 0`: `U` meets no normal number. -/
theorem not_potentialWinning_isNormal (hE : EPotentialWinning) (hJ : Literature.BFSDimInterval)
    {b : ℕ} (hb : 2 ≤ b) :
    ¬ ∀ α : ℝ, 0 < α → PotentialWinning {x | IsNormal b x} α (1 / 4) (1 / 2) (1 / 2) := by
  intro hN
  have hempty : U ∩ {x | IsNormal b x} = ∅ := by
    ext ξ
    simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hU hn
    obtain ⟨C, hC⟩ := mem_iUnion.1 hU
    exact UniformBad.not_isNormal_of_uniformBad hb (hC b hb) hn
  have hS : ∀ η : ℝ, 0 < η → ∃ α, 0 < α ∧ α < η ∧
      PotentialWinning (U ∩ {x | IsNormal b x}) α (1 / 4) (1 / 2) (1 / 2) := by
    intro η hη
    obtain ⟨α₁, hα₁, hα₁η, hPW₁⟩ := smallPW_U hE (by norm_num : (0 : ℝ) < 1 / 2) (η / 8)
      (by positivity)
    have hI := hPW₁.inter (by norm_num) hα₁.le (by positivity : (0 : ℝ) ≤ η / 8)
      (hN (η / 8) (by positivity))
    exact ⟨_, sum_sqrt_rpow_pos hα₁ (by positivity), sum_sqrt_rpow_lt hα₁.le (by positivity)
      (by linarith), hI⟩
  have h := le_dimH_of_potentialWinning hJ (by norm_num : (1 / 2 : ℝ) < 1)
    (⟨by norm_num, by norm_num⟩ : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) < 1 / 2) hS
  rw [hempty, empty_inter, dimH_empty, ENNReal.ofReal_one] at h
  exact one_ne_zero (le_antisymm h bot_le)

end NormalNumbers.SchmidtGames
