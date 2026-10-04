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

1. **`potentialWinning_E`** (`sorry`, the new combinatorial core).  For all `0 < β < 1`, `ρ > 0`
   there is `K` with `E C` `(K·2^{−C}, β, 1/2, ρ)`-potential winning for every `C ≥ 3`, in the
   potential game of Fishman–Simmons–Urbański / Broderick–Fishman–Simmons (`PotentialWinning`).
2. **`dimH_E₂_le`** (`sorry`, a base-2 covering count).
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

Confidence: mathematics 90%, Lean 65% (2–4 laps). -/
theorem potentialWinning_E : EPotentialWinning := by
  sorry

/-! ## Headline 2: the base-2 upper bound -/

/-- **Headline 2.**  `dim_H {ξ : ‖2ⁿξ‖ > 2^{−C} ∀ n} ≤ 1 − 2^{−(C+1)}` for `C ≥ 1`.

*Proof sketch.*  With `m = ⌈C⌉`, such `ξ` has no run of `m` equal binary digits (a run of `m`
zeros after position `n` gives `{2ⁿξ} ≤ 2^{−m} ≤ 2^{−C}`, ones symmetrically).  Words of length
`N` with all runs `< m` number `a_N = a_{N−1} + ⋯ + a_{N−m+1}`, so `a_N ≤ 2μ^N` for any `μ`
with `μ^{m−1}(2 − μ) ≤ 1`; `μ = 2 − 2^{1−m}` qualifies.  Covering `E₂ C ∩ [j, j+1]` by `a_N`
dyadic intervals gives `dim_H ≤ log₂ μ = 1 + log₂(1 − 2^{−m}) ≤ 1 − 2^{−m} ≤ 1 − 2^{−(C+1)}`,
and `E₂ C` is a countable union of translates.

Confidence: mathematics 97%, Lean 55%. -/
theorem dimH_E₂_le {C : ℝ} (hC : 1 ≤ C) :
    dimH (E₂ C) ≤ ENNReal.ofReal (1 - 2 ^ (-(C + 1))) := by
  sorry

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
