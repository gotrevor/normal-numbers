/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.BaryBlockCount
import NormalNumbers.DigitInterval

/-!
# W5 groundwork — d-ary cells and Becher–Yuhjtman Proposition 12

The t-brick machinery (B–Y Definitions 10–11, Lemma 13) nests a CF cylinder
inside one d-ary interval — or two consecutive ones — per base `d ≤ t`.
This file sets up the d-ary cells and proves Prop 12:

* `daryCell d m j r` — the union of `r` consecutive d-ary intervals of
  order `m` starting at index `j` (bricks use `r = 1` or `r = 2`).
* `volume_daryCell` — its Lebesgue measure is `r/d^m`.
* `interval_subset_daryCell_two` (**Prop 12**): every interval of length
  `< d^(−m)` lies in the union of two consecutive d-ary intervals of
  order `m` (explicitly, the one containing its left endpoint and its
  right neighbour).
-/

namespace NormalNumbers

open MeasureTheory

/-- The union of `r` consecutive d-ary intervals of order `m`, starting at
index `j` (as a half-open interval `[j/d^m, (j+r)/d^m)`). -/
def daryCell (d m : ℕ) (j : ℤ) (r : ℕ) : Set ℝ :=
  Set.Ico ((j : ℝ) / d ^ m) (((j : ℝ) + r) / d ^ m)

/-- The Lebesgue measure of `r` consecutive order-`m` cells is `r/d^m`. -/
theorem volume_daryCell (d m : ℕ) (hd : 1 ≤ d) (j : ℤ) (r : ℕ) :
    volume (daryCell d m j r) = ENNReal.ofReal ((r : ℝ) / d ^ m) := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ m := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  rw [daryCell, Real.volume_Ico]
  congr 1
  field_simp
  ring

/-- **B–Y Proposition 12**: an interval of length `< d^(−m)` is contained in
the union of two consecutive d-ary intervals of order `m` — namely the cell
of its left endpoint and the next one. -/
theorem interval_subset_daryCell_two (d m : ℕ) (hd : 1 ≤ d) {a c : ℝ}
    (h : c - a < 1 / d ^ m) :
    Set.Icc a c ⊆ daryCell d m ⌊a * d ^ m⌋ 2 := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ m := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  intro x hx
  obtain ⟨hax, hxc⟩ := hx
  constructor
  · -- `⌊a·d^m⌋/d^m ≤ a ≤ x`
    rw [div_le_iff₀ hdpow]
    calc (⌊a * d ^ m⌋ : ℝ) ≤ a * d ^ m := Int.floor_le _
      _ ≤ x * d ^ m := by nlinarith
  · -- `x ≤ c < a + d^(−m) < (⌊a·d^m⌋ + 2)/d^m`
    rw [lt_div_iff₀ hdpow]
    have hfl : a * d ^ m < (⌊a * d ^ m⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hc : c * d ^ m < a * d ^ m + 1 := by
      have := (sub_lt_iff_lt_add.1 h)
      calc c * d ^ m < (1 / d ^ m + a) * d ^ m := by nlinarith
        _ = a * d ^ m + 1 := by field_simp; ring
    push_cast
    nlinarith

attribute [local instance] Classical.propDecidable

/-- The `ε`-bad blocks of length `k` in base `d` — the Lemma 8 filter:
some digit's count deviates from the fair share `k/d` by at least `εk`. -/
noncomputable def badBlocks (d k : ℕ) (ε : ℝ) : Finset (Fin k → Fin d) :=
  Finset.univ.filter fun u =>
    ∃ s : Fin d, ε * k ≤ |(digitCount s u : ℝ) - k / d|

/-- Lemma 8 in `badBlocks` form. -/
theorem card_badBlocks_le (d k : ℕ) (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hεd : (d : ℝ) * ε ≤ 1) :
    ((badBlocks d k ε).card : ℝ)
      ≤ 2 * (d : ℝ) ^ (k + 1) * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6) := by
  have h := card_baryDiscrepancy_ge_le d k hd hε0 hεd
  calc ((badBlocks d k ε).card : ℝ)
      = ((Finset.univ.filter fun u : Fin k → Fin d =>
          ∃ s : Fin d, ε * k ≤ |(digitCount s u : ℝ) - k / d|).card : ℝ) := by
        rw [badBlocks]
    _ ≤ _ := by exact_mod_cast h
  
/-- **The d-ary bad zone is exponentially small**: inside one d-ary cell of
order `m0`, the union of the order-`(m0+k)` sub-cells carrying an `ε`-bad
new block has measure at most `2d·e^{−dε²k/6}·d^{−m0}`, i.e. `2d·e^{−dε²k/6}`
times the measure of the cell. -/
theorem volume_daryBadZone_le (d m0 k : ℕ) (hd : 1 ≤ d) (j0 : ℤ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεd : (d : ℝ) * ε ≤ 1) :
    volume (⋃ β ∈ badBlocks d k ε,
      daryCell d (m0 + k)
        (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1)
      ≤ ENNReal.ofReal
          (2 * d * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6) / d ^ m0) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc volume (⋃ β ∈ badBlocks d k ε,
      daryCell d (m0 + k)
        (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1)
      ≤ ∑ β ∈ badBlocks d k ε,
          volume (daryCell d (m0 + k)
            (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _β ∈ badBlocks d k ε,
          ENNReal.ofReal ((1 : ℝ) / d ^ (m0 + k)) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [volume_daryCell d (m0 + k) hd _ 1]
        norm_num
    _ = ENNReal.ofReal (((badBlocks d k ε).card : ℝ) / d ^ (m0 + k)) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal
          ((2 * (d : ℝ) ^ (k + 1) * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6))
            / d ^ (m0 + k)) := by
        apply ENNReal.ofReal_le_ofReal
        have hcard := card_badBlocks_le d k hd hε0 hεd
        gcongr
    _ = ENNReal.ofReal
          (2 * d * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6) / d ^ m0) := by
        congr 1
        rw [pow_add, pow_succ]
        field_simp
        ring

/-- The order-`(m0+k)` bad zone inside the order-`m0` cell at `j0`: the
union of the sub-cells whose new length-`k` block is `ε`-bad. -/
noncomputable def daryBadZone (d m0 : ℕ) (j0 : ℤ) (ε : ℝ) (k : ℕ) : Set ℝ :=
  ⋃ β ∈ badBlocks d k ε,
    daryCell d (m0 + k)
      (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1

theorem volume_daryBadZone_le' (d m0 : ℕ) (hd : 1 ≤ d) (j0 : ℤ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεd : (d : ℝ) * ε ≤ 1) (k : ℕ) :
    volume (daryBadZone d m0 j0 ε k)
      ≤ ENNReal.ofReal
          (2 * d / d ^ m0 * Real.exp (-((d : ℝ) * ε ^ 2) / 6) ^ k) := by
  have h := volume_daryBadZone_le d m0 k hd j0 hε0 hεd
  rw [daryBadZone]
  refine h.trans (le_of_eq ?_)
  congr 1
  have harg : (k : ℝ) * (-((d : ℝ) * ε ^ 2) / 6) = -((d : ℝ) * ε ^ 2 * k) / 6 := by
    ring
  rw [← Real.exp_nat_mul, harg]
  ring

/-- **Summed d-ary bad zone**: the union of the bad zones over all new-block
lengths `k ≥ kmin` is still exponentially small in `kmin` relative to the
cell — total measure `≤ (2d/d^m0)·ρ^kmin/(1−ρ)` with `ρ = e^{−dε²/6}`. -/
theorem volume_iUnion_daryBadZone_le (d m0 : ℕ) (hd : 1 ≤ d) (j0 : ℤ)
    {ε : ℝ} (hε0 : 0 < ε) (hεd : (d : ℝ) * ε ≤ 1) (kmin : ℕ) :
    volume (⋃ k : ℕ, ⋃ (_ : kmin ≤ k), daryBadZone d m0 j0 ε k)
      ≤ ENNReal.ofReal
          (2 * d / d ^ m0 * Real.exp (-((d : ℝ) * ε ^ 2) / 6) ^ kmin
            / (1 - Real.exp (-((d : ℝ) * ε ^ 2) / 6))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set ρ : ℝ := Real.exp (-((d : ℝ) * ε ^ 2) / 6) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff]
    have : 0 < (d : ℝ) * ε ^ 2 := by positivity
    linarith
  set A : ℝ := 2 * d / d ^ m0 with hA
  have hA0 : 0 < A := by positivity
  have hsub : (⋃ k : ℕ, ⋃ (_ : kmin ≤ k), daryBadZone d m0 j0 ε k)
      ⊆ ⋃ i : ℕ, daryBadZone d m0 j0 ε (kmin + i) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨k, hk, hxk⟩ := hx
    exact ⟨k - kmin, by rwa [Nat.add_sub_cancel' hk]⟩
  calc volume (⋃ k : ℕ, ⋃ (_ : kmin ≤ k), daryBadZone d m0 j0 ε k)
      ≤ volume (⋃ i : ℕ, daryBadZone d m0 j0 ε (kmin + i)) :=
        measure_mono hsub
    _ ≤ ∑' i : ℕ, volume (daryBadZone d m0 j0 ε (kmin + i)) :=
        measure_iUnion_le _
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (A * ρ ^ kmin * ρ ^ i) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        refine (volume_daryBadZone_le' d m0 hd j0 hε0.le hεd (kmin + i)).trans
          (le_of_eq ?_)
        rw [← hρ, ← hA, pow_add]
        ring_nf
    _ = ENNReal.ofReal (A * ρ ^ kmin) * ∑' i : ℕ, ENNReal.ofReal ρ ^ i := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun i => ?_
        rw [← ENNReal.ofReal_pow hρ0.le,
          ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (A * ρ ^ kmin) * (1 - ENNReal.ofReal ρ)⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (A * ρ ^ kmin / (1 - ρ)) := by
        have h1 : (1 : ENNReal) - ENNReal.ofReal ρ = ENNReal.ofReal (1 - ρ) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hρ0.le]
        rw [h1, ← ENNReal.ofReal_inv_of_pos (by linarith),
          ← ENNReal.ofReal_mul (by positivity)]
        rw [div_eq_mul_inv]

/-- Every index `v < d^k` is the value of a length-`k` digit block. -/
theorem exists_block_of_lt (d : ℕ) : ∀ (k : ℕ) {v : ℕ}, v < d ^ k →
    ∃ β : Fin k → Fin d, blockNatVal d (List.ofFn fun i => (β i : ℕ)) = v := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have hv0 : v = 0 := by simpa [Nat.lt_one_iff] using hv
    subst hv0
    exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
    intro v hv
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at hv
      · exact h
    have ha : v / d ^ n < d := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos hd (n := n))]
      calc v < d ^ (n + 1) := hv
        _ = d * d ^ n := by ring
    obtain ⟨β', hβ'⟩ := ih (Nat.mod_lt v (Nat.pow_pos hd (n := n)))
    refine ⟨Fin.cons ⟨v / d ^ n, ha⟩ β', ?_⟩
    have hofn : (List.ofFn fun i : Fin (n + 1) =>
        ((Fin.cons ⟨v / d ^ n, ha⟩ β' : Fin (n + 1) → Fin d) i : ℕ))
        = (v / d ^ n) :: (List.ofFn fun i : Fin n => (β' i : ℕ)) := by
      rw [List.ofFn_succ]
      simp
    rw [hofn, blockNatVal_cons, hβ', List.length_ofFn]
    exact Nat.div_add_mod' v (d ^ n)

/-- A point of an order-`m0` cell lies in the order-`(m0+k)` sub-cell of its
own digit block; the sub-cell index is `j0·d^k +` a block value `< d^k`. -/
theorem floor_subCell_bounds (d m0 k : ℕ) (hd : 1 ≤ d) (j0 : ℤ) {x : ℝ}
    (hx : x ∈ daryCell d m0 j0 1) :
    j0 * d ^ k ≤ ⌊x * d ^ (m0 + k)⌋ ∧
      ⌊x * d ^ (m0 + k)⌋ < (j0 + 1) * d ^ k ∧
      x ∈ daryCell d (m0 + k) ⌊x * d ^ (m0 + k)⌋ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpow0 : (0 : ℝ) < (d : ℝ) ^ m0 := by positivity
  have hpowk : (0 : ℝ) < (d : ℝ) ^ k := by positivity
  have hpow : (0 : ℝ) < (d : ℝ) ^ (m0 + k) := by positivity
  obtain ⟨hxl, hxr⟩ := hx
  have hxl' : (j0 : ℝ) * d ^ k ≤ x * d ^ (m0 + k) := by
    rw [div_le_iff₀ hpow0] at hxl
    calc (j0 : ℝ) * d ^ k ≤ x * d ^ m0 * d ^ k := by nlinarith
      _ = x * d ^ (m0 + k) := by rw [pow_add]; ring
  have hxr' : x * d ^ (m0 + k) < ((j0 : ℝ) + 1) * d ^ k := by
    rw [lt_div_iff₀ hpow0] at hxr
    have h1 : x * d ^ m0 < (j0 : ℝ) + 1 := by
      push_cast at hxr ⊢
      linarith
    calc x * d ^ (m0 + k) = x * d ^ m0 * d ^ k := by rw [pow_add]; ring
      _ < ((j0 : ℝ) + 1) * d ^ k := by nlinarith
  have hlo : j0 * d ^ k ≤ ⌊x * d ^ (m0 + k)⌋ := by
    apply Int.le_floor.2
    push_cast
    exact hxl'
  have hhi : ⌊x * d ^ (m0 + k)⌋ < (j0 + 1) * d ^ k := by
    apply Int.floor_lt.2
    push_cast
    exact hxr'
  refine ⟨hlo, hhi, ?_, ?_⟩
  · rw [div_le_iff₀ hpow]
    exact Int.floor_le _
  · rw [lt_div_iff₀ hpow]
    push_cast
    exact Int.lt_floor_add_one _
  
/-- **Bad-zone avoidance ⇒ good block**: a point of the order-`m0` cell that
avoids the order-`(m0+k)` bad zone lies in the sub-cell of a *good* block. -/
theorem exists_goodBlock_of_notMem_badZone (d m0 k : ℕ) (hd : 1 ≤ d)
    (j0 : ℤ) {ε : ℝ} {x : ℝ} (hx : x ∈ daryCell d m0 j0 1)
    (hbad : x ∉ daryBadZone d m0 j0 ε k) :
    ∃ β : Fin k → Fin d, β ∉ badBlocks d k ε ∧
      x ∈ daryCell d (m0 + k)
        (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1 := by
  obtain ⟨hlo, hhi, hmem⟩ := floor_subCell_bounds d m0 k hd j0 hx
  set F := ⌊x * d ^ (m0 + k)⌋ with hF
  clear_value F
  have hcast : ((d : ℤ)) ^ k = ((d ^ k : ℕ) : ℤ) := by push_cast; ring
  rw [add_mul, one_mul] at hhi
  have hv : (F - j0 * d ^ k).toNat < d ^ k := by omega
  obtain ⟨β, hβ⟩ := exists_block_of_lt d k hv
  refine ⟨β, ?_, ?_⟩
  · intro hmem_bad
    apply hbad
    rw [daryBadZone]
    refine Set.mem_biUnion hmem_bad ?_
    have hidx : j0 * d ^ k
        + (blockNatVal d (List.ofFn fun i => (β i : ℕ)) : ℤ) = F := by
      rw [hβ]
      omega
    rwa [hidx]
  · have hidx : j0 * d ^ k
        + (blockNatVal d (List.ofFn fun i => (β i : ℕ)) : ℤ) = F := by
      rw [hβ]
      omega
    rwa [hidx]

/-- Generic geometric union bound: if `volume (S k) ≤ A·ρ^k` with `ρ < 1`,
the tail union over `k ≥ kmin` has measure `≤ A·ρ^kmin/(1−ρ)`. -/
theorem volume_iUnion_geom_le {S : ℕ → Set ℝ} {A ρ : ℝ} (hA : 0 ≤ A)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h : ∀ k, volume (S k) ≤ ENNReal.ofReal (A * ρ ^ k)) (kmin : ℕ) :
    volume (⋃ k : ℕ, ⋃ (_ : kmin ≤ k), S k)
      ≤ ENNReal.ofReal (A * ρ ^ kmin / (1 - ρ)) := by
  have hsub : (⋃ k : ℕ, ⋃ (_ : kmin ≤ k), S k) ⊆ ⋃ i : ℕ, S (kmin + i) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨k, hk, hxk⟩ := hx
    exact ⟨k - kmin, by rwa [Nat.add_sub_cancel' hk]⟩
  calc volume (⋃ k : ℕ, ⋃ (_ : kmin ≤ k), S k)
      ≤ volume (⋃ i : ℕ, S (kmin + i)) := measure_mono hsub
    _ ≤ ∑' i : ℕ, volume (S (kmin + i)) := measure_iUnion_le _
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (A * ρ ^ kmin * ρ ^ i) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        refine (h (kmin + i)).trans (le_of_eq ?_)
        rw [pow_add]
        ring_nf
    _ = ENNReal.ofReal (A * ρ ^ kmin) * ∑' i : ℕ, ENNReal.ofReal ρ ^ i := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun i => ?_
        rw [← ENNReal.ofReal_pow hρ0.le,
          ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (A * ρ ^ kmin) * (1 - ENNReal.ofReal ρ)⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (A * ρ ^ kmin / (1 - ρ)) := by
        have h1 : (1 : ENNReal) - ENNReal.ofReal ρ = ENNReal.ofReal (1 - ρ) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hρ0.le]
        rw [h1, ← ENNReal.ofReal_inv_of_pos (by linarith),
          ← ENNReal.ofReal_mul (by positivity)]
        rw [div_eq_mul_inv]

/-- The neighbour-widened bad zone: each bad sub-cell together with its two
neighbours.  Avoiding this zone makes *every* cell within distance 1 of the
point's own cell good — what a two-cell `τ_d` needs. -/
noncomputable def daryBadZoneWide (d m0 : ℕ) (j0 : ℤ) (ε : ℝ) (k : ℕ) :
    Set ℝ :=
  ⋃ β ∈ badBlocks d k ε,
    daryCell d (m0 + k)
      (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ)) - 1) 3

theorem volume_daryBadZoneWide_le (d m0 : ℕ) (hd : 1 ≤ d) (j0 : ℤ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεd : (d : ℝ) * ε ≤ 1) (k : ℕ) :
    volume (daryBadZoneWide d m0 j0 ε k)
      ≤ ENNReal.ofReal
          (6 * d / d ^ m0 * Real.exp (-((d : ℝ) * ε ^ 2) / 6) ^ k) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc volume (daryBadZoneWide d m0 j0 ε k)
      ≤ ∑ β ∈ badBlocks d k ε,
          volume (daryCell d (m0 + k)
            (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ)) - 1)
            3) := measure_biUnion_finset_le _ _
    _ = ∑ _β ∈ badBlocks d k ε,
          ENNReal.ofReal ((3 : ℝ) / d ^ (m0 + k)) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [volume_daryCell d (m0 + k) hd _ 3]
        norm_num
    _ = ENNReal.ofReal (((badBlocks d k ε).card : ℝ) * 3 / d ^ (m0 + k)) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal
          (6 * d / d ^ m0 * Real.exp (-((d : ℝ) * ε ^ 2) / 6) ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        have hcard := card_badBlocks_le d k hd hε0 hεd
        have hexp : Real.exp (-((d : ℝ) * ε ^ 2) / 6) ^ k
            = Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [hexp]
        rw [div_le_iff₀ (by positivity), pow_add]
        have hpow : (0 : ℝ) < (d : ℝ) ^ m0 := by positivity
        calc ((badBlocks d k ε).card : ℝ) * 3
            ≤ (2 * (d : ℝ) ^ (k + 1)
                * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6)) * 3 := by
              have h0 : (0 : ℝ) ≤ 3 := by norm_num
              nlinarith [Real.exp_pos (-((d : ℝ) * ε ^ 2 * k) / 6)]
          _ = 6 * d / d ^ m0 * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6)
                * (d ^ m0 * d ^ k) := by
              rw [pow_succ]
              field_simp
              ring
    _ = _ := rfl

/-- Summed widened bad zone over all block lengths `k ≥ kmin`. -/
theorem volume_iUnion_daryBadZoneWide_le (d m0 : ℕ) (hd : 1 ≤ d) (j0 : ℤ)
    {ε : ℝ} (hε0 : 0 < ε) (hεd : (d : ℝ) * ε ≤ 1) (kmin : ℕ) :
    volume (⋃ k : ℕ, ⋃ (_ : kmin ≤ k), daryBadZoneWide d m0 j0 ε k)
      ≤ ENNReal.ofReal
          (6 * d / d ^ m0 * Real.exp (-((d : ℝ) * ε ^ 2) / 6) ^ kmin
            / (1 - Real.exp (-((d : ℝ) * ε ^ 2) / 6))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine volume_iUnion_geom_le (by positivity) (Real.exp_pos _) ?_
    (fun k => volume_daryBadZoneWide_le d m0 hd j0 hε0.le hεd k) kmin
  rw [Real.exp_lt_one_iff]
  have : 0 < (d : ℝ) * ε ^ 2 := by positivity
  linarith

/-- **Wide avoidance**: if `x` (in the base cell) avoids the widened bad
zone at length `k`, every bad sub-cell is at distance `≥ 2` from `x`'s own
sub-cell. -/
theorem badBlock_cell_far (d m0 k : ℕ) (hd : 1 ≤ d) (j0 : ℤ) {ε : ℝ}
    {x : ℝ} (hx : x ∈ daryCell d m0 j0 1)
    (hbad : x ∉ daryBadZoneWide d m0 j0 ε k) :
    ∀ β ∈ badBlocks d k ε,
      1 < |(j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ)) : ℤ)
            - ⌊x * d ^ (m0 + k)⌋| := by
  intro β hβ
  by_contra hnear
  push Not at hnear
  apply hbad
  rw [daryBadZoneWide]
  refine Set.mem_biUnion hβ ?_
  obtain ⟨-, -, hmem⟩ := floor_subCell_bounds d m0 k hd j0 hx
  obtain ⟨hml, hmr⟩ := hmem
  set I : ℤ := j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))
    with hI
  set F : ℤ := ⌊x * d ^ (m0 + k)⌋ with hF
  have habs : I - 1 ≤ F ∧ F + 1 ≤ I + 2 := by
    rw [abs_le] at hnear
    omega
  have hpow : (0 : ℝ) < (d : ℝ) ^ (m0 + k) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  constructor
  · rw [div_le_iff₀ hpow]
    rw [div_le_iff₀ hpow] at hml
    have : ((I : ℝ) - 1) ≤ (F : ℝ) := by exact_mod_cast habs.1
    push_cast
    push_cast at hml
    linarith
  · rw [lt_div_iff₀ hpow]
    rw [lt_div_iff₀ hpow] at hmr
    have : ((F : ℝ) + 1) ≤ (I : ℝ) + 2 := by exact_mod_cast habs.2
    push_cast
    push_cast at hmr
    linarith

end NormalNumbers
