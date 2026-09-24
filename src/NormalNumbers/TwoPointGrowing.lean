import NormalNumbers.TwoPointWorry

/-!
# The growing-`w` re-plumb of the averaged two-point leaf

Lap 1 (`TwoPointWorry.lean`) refuted the *argument* that the fixed-`w` quantifier order makes
`TwoPointWeightedAvg` equivalent to the pointwise open problem; lap 2's probe
(`probes/twopoint_async_2026_09_24.py`) then showed the arithmetic table is **not** asynchronous —
every pair's correlation decays monotonically — so the logical room lap 1 found is not where a
proof will come from.  What is left is kickoff item 2: run the pair average over `p, q ≤ w(N)`
with `w(N) → ∞` *with* `N`, which is the regime in which MRT-style averaging (and the large sieve
in the multiplier) actually buys something, and which is what the quantitative Kátai/BSZ
inequality really consumes.

This file states that leaf and relates it to the ratified one.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **THE GROWING-`w` LEAF.**  The pair average runs over `p, q ≤ w(N)` for some cutoff growing
with `N`.  This is the form the quantitative Kátai/BSZ inequality consumes. -/
def TwoPointWeightedAvgGrowing (b : ℕ) (t : ℝ) : Prop :=
  ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
    Tendsto (fun N => twoPointAvgSum b t (w N) N) atTop (𝓝 0)

/-- The abstract-shape version, for reasoning about quantifier structure alone. -/
def AvgShapeGrowing (G : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧ Tendsto (fun N => avgTable G (w N) N) atTop (𝓝 0)

lemma twoPointWeightedAvgGrowing_iff_avgShapeGrowing (b : ℕ) (t : ℝ) :
    TwoPointWeightedAvgGrowing b t ↔
      AvgShapeGrowing (fun p q N =>
        ‖fullMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) N‖) :=
  Iff.rfl

/-! ### The re-plumb is a weakening, not a strengthening

The fixed-`w` shape gives, for each `ε`, a threshold `w_ε` beyond which the average is eventually
`< ε` in `N`.  Diagonalising over `ε = 1/(k+1)` produces a single slowly growing cutoff `w(N)`
along which the average tends to `0`.  So `AvgShape → AvgShapeGrowing`: the growing leaf is at
most as strong as the ratified one, and attacking it cannot smuggle in extra strength. -/

/-! #### Diagonal bookkeeping -/

/-- A strictly increasing majorant of `N₀`. -/
private def stair (N₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => N₀ 0
  | (k + 1) => max (stair N₀ k + 1) (N₀ (k + 1))

private lemma le_stair (N₀ : ℕ → ℕ) : ∀ k, N₀ k ≤ stair N₀ k
  | 0 => le_rfl
  | (k + 1) => le_max_right _ _

private lemma self_le_stair (N₀ : ℕ → ℕ) : ∀ k, k ≤ stair N₀ k
  | 0 => Nat.zero_le _
  | (k + 1) => by
      have := self_le_stair N₀ k
      have : stair N₀ k + 1 ≤ stair N₀ (k + 1) := le_max_left _ _
      omega

/-- A strictly increasing majorant of `W₀`. -/
private def ramp (W₀ : ℕ → ℕ) (k : ℕ) : ℕ := (Finset.range (k + 1)).sup W₀ + k

private lemma le_ramp (W₀ : ℕ → ℕ) (k : ℕ) : W₀ k ≤ ramp W₀ k :=
  le_trans (Finset.le_sup (f := W₀) (Finset.self_mem_range_succ k)) (Nat.le_add_right _ _)

private lemma self_le_ramp (W₀ : ℕ → ℕ) (k : ℕ) : k ≤ ramp W₀ k := Nat.le_add_left _ _

lemma avgTable_nonneg (G : ℕ → ℕ → ℕ → ℝ) (hG : ∀ p q N, 0 ≤ G p q N) (w N : ℕ) :
    0 ≤ avgTable G w N := by
  refine div_nonneg (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_) (by positivity)
  split
  · exact le_rfl
  · exact hG p q N

/-- **The re-plumb is a weakening.**  Diagonalising the fixed-`w` shape over `ε = 1/(k+1)`
produces a single cutoff `w(N) → ∞` along which the pair average tends to `0`. -/
theorem avgShapeGrowing_of_avgShape (G : ℕ → ℕ → ℕ → ℝ) (hG : ∀ p q N, 0 ≤ G p q N)
    (h : AvgShape G) : AvgShapeGrowing G := by
  classical
  -- `W₀ k` : a cutoff beyond which the inner statement holds at level `1/(k+1)`
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1) := fun k => by positivity
  choose W₀ hW₀ using fun k : ℕ => Filter.eventually_atTop.mp (h (1 / (k + 1)) (hpos k))
  set W : ℕ → ℕ := ramp W₀ with hW
  have hWspec : ∀ k, ∀ᶠ N : ℕ in atTop, avgTable G (W k) N < 1 / (k + 1) := fun k =>
    hW₀ k (W k) (le_ramp W₀ k)
  choose N₀ hN₀ using fun k : ℕ => Filter.eventually_atTop.mp (hWspec k)
  set S : ℕ → ℕ := stair N₀ with hS
  set kIdx : ℕ → ℕ := fun N => Nat.findGreatest (fun k => S k ≤ N) N with hkIdx
  -- the two facts about `kIdx`
  have hk_ge : ∀ k₀ N : ℕ, 1 ≤ k₀ → S k₀ ≤ N → k₀ ≤ kIdx N := by
    intro k₀ N hk₀ hSN
    exact Nat.le_findGreatest (P := fun k => S k ≤ N) (le_trans (self_le_stair N₀ k₀) hSN) hSN
  have hk_spec : ∀ k₀ N : ℕ, 1 ≤ k₀ → S k₀ ≤ N → S (kIdx N) ≤ N := by
    intro k₀ N hk₀ hSN
    exact Nat.findGreatest_spec (P := fun k => S k ≤ N) (m := k₀) (le_trans (self_le_stair N₀ k₀) hSN) hSN
  refine ⟨fun N => W (kIdx N), ?_, ?_⟩
  · refine tendsto_atTop.mpr fun M => ?_
    filter_upwards [Filter.eventually_ge_atTop (S (M + 1))] with N hN
    have h1 : M + 1 ≤ kIdx N := hk_ge (M + 1) N (by omega) hN
    exact le_trans (by omega) (le_trans h1 (self_le_ramp W₀ (kIdx N)))
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / ε)
    refine ⟨S (k₀ + 1), fun N hN => ?_⟩
    have hk1 : k₀ + 1 ≤ kIdx N := hk_ge (k₀ + 1) N (by omega) hN
    have hspec : S (kIdx N) ≤ N := hk_spec (k₀ + 1) N (by omega) hN
    have hlt : avgTable G (W (kIdx N)) N < 1 / ((kIdx N : ℝ) + 1) :=
      hN₀ (kIdx N) N (le_trans (le_stair N₀ (kIdx N)) hspec)
    have hnn : 0 ≤ avgTable G (W (kIdx N)) N := avgTable_nonneg G hG _ _
    have hcast : ((k₀ : ℝ) + 1) ≤ ((kIdx N : ℝ) + 1) := by
      have : (k₀ : ℝ) ≤ (kIdx N : ℝ) := by exact_mod_cast le_trans (by omega) hk1
      linarith
    have hεk : 1 / ((k₀ : ℝ) + 1) < ε := by
      have hk0 : (0 : ℝ) < (k₀ : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hk0]
      have : 1 / ε < (k₀ : ℝ) := hk₀
      rw [div_lt_iff₀ hε] at this
      nlinarith
    have hmono : 1 / ((kIdx N : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity) hcast
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith


/-- **The re-plumb, concretely.**  The ratified leaf implies the growing-`w` leaf, so the
re-plumb never asks for more than `twoPointWeightedAvg_all` already grants. -/
theorem twoPointWeightedAvgGrowing_of_twoPointWeightedAvg (b : ℕ) (t : ℝ)
    (h : TwoPointWeightedAvg b t) : TwoPointWeightedAvgGrowing b t :=
  avgShapeGrowing_of_avgShape _ (fun _ _ _ => norm_nonneg _) h

end NormalNumbers.CastingOut
