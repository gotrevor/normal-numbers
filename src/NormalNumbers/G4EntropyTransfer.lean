/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPositions
import NormalNumbers.G4EntropyRate
import NormalNumbers.Bridge
import NormalNumbers.Counting

/-!
# Entropy expedition §6: the transfer targets, and the refutation of `T_E`

The brief freezes three transfer statements over the *same* sampling family.  Here the family
is indexed by `i : ℕ` through `k₄ = 40000 + i`, `K = 4k₄` (so `K ≥ 160000`, the range where
`entropy_E1` holds), and the statements are

* `E0 x` — `H₂(Z^x_K)/(m_K H_K) → 1`;
* `T_E`  — `∀ x ∈ [0,1), E0 x → IsNormal 2 x`   (the brief's **primary** target).

`E0_primeLambertFour` upgrades `entropy_E1` to the genuine limit statement for `x = G₄`.

`T_E` is then **false**.  The witness is `G₄` masked to the sampled positions: `maskedReal`
keeps the digits of `G₄` at every position some scale actually samples and sets every other
digit to `0`.  By `G4EntropyLocality` the masked number has literally the same joint law at
every scale, so it satisfies `E0`; by `G4EntropyPositions` the sampled positions have density
`≤ 1/4`, so fewer than a quarter of its digits are `1` and it is not normal.

This is the outcome the brief calls for: *a precise counterexample satisfying the exact
premise*.  It says that no statement about this arithmetic sample alone — however strong —
can imply ordinary normality: the sample simply does not look at enough digits.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The frozen sampling family -/

/-- The block length `m_K = k₄` at family index `i`. -/
def kk (i : ℕ) : ℕ := 40000 + i

/-- The scale `K = 4k₄` at family index `i`. -/
def KK (i : ℕ) : ℕ := 4 * kk i

lemma KK_ge (i : ℕ) : 160000 ≤ KK i := by unfold KK kk; omega

lemma KK_one_le (i : ℕ) : 1 ≤ KK i := by have := KK_ge i; omega

lemma KK_hundred (i : ℕ) : 100 ≤ KK i := by have := KK_ge i; omega

/-- The grid at family index `i`. -/
noncomputable def gridAt (i : ℕ) : GridParams := gridOf (KK i) (N (KK i)) (KK_one_le i)

lemma b₀_lt_X_at (i : ℕ) : (gridAt i).b₀ < X (KK i) := b₀_lt_X (KK_hundred i)

/-- The digit positions the scale-`i` sample reads. -/
noncomputable def sampledPosAt (i : ℕ) : Finset ℕ :=
  sampledPos (gridAt i) (X (KK i)) (kk i)

/-- A digit position read by *some* admissible scale. -/
def IsSampled (j : ℕ) : Prop := ∃ i, j ∈ sampledPosAt i

noncomputable instance : DecidablePred IsSampled := Classical.decPred _

/-- The joint quantized sample law at family index `i`. -/
noncomputable def jointLawAt (i : ℕ) (x : ℝ) :
    FinLaw ((gridAt i).Atom → Fin (2 ^ kk i)) :=
  jointLaw (gridAt i) (b₀_lt_X_at i) (kk i) x

/-- The maximal entropy `m_K · H_K` at family index `i`. -/
noncomputable def maxH (i : ℕ) : ℝ := (kk i : ℝ) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ)

/-! ### The transfer targets (brief §6) -/

/-- **E0**: the sample entropy is asymptotically maximal. -/
def E0 (x : ℝ) : Prop :=
  Tendsto (fun i => (jointLawAt i x).H₂ / maxH i) atTop (nhds 1)

/-- **`T_E`** (brief §6, the primary transfer target): `E0` implies ordinary binary
normality, for every `x ∈ [0,1)`. -/
def T_E : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → E0 x → IsNormal 2 x

/-! ### `E0` holds for `G₄` -/

lemma card_Atom_gridAt (i : ℕ) :
    Fintype.card (gridAt i).Atom = (KK i ^ 2 + 1) ^ KK i := by
  show Fintype.card (Fin (KK i) → Fin (KK i ^ 2 + 1)) = (KK i ^ 2 + 1) ^ KK i
  simp

lemma maxH_pos (i : ℕ) : 0 < maxH i := by
  unfold maxH
  have h1 : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have h2 : (0 : ℝ) < (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    have : 0 < (KK i ^ 2 + 1) ^ KK i := pow_pos (by omega) _
    exact_mod_cast this
  positivity

set_option maxHeartbeats 1000000 in
/-- The ratio is at most `1` (the alphabet bound). -/
theorem ratio_le_one (i : ℕ) (x : ℝ) : (jointLawAt i x).H₂ / maxH i ≤ 1 := by
  have h := H₂_jointLaw_le_mul (gridAt i) (b₀_lt_X_at i) (kk i) x
  rw [card_Atom_gridAt i] at h
  rw [div_le_one (maxH_pos i)]
  exact h.trans_eq (by unfold maxH; push_cast; ring)

set_option maxHeartbeats 1000000 in
/-- The ratio is at least `1 − 200/√K` (from `entropy_E1`). -/
theorem one_sub_le_ratio (i : ℕ) :
    1 - 200 / Real.sqrt (KK i) ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ / maxH i := by
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have := KK_ge i
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : (0 : ℝ) < Real.sqrt (KK i) := Real.sqrt_pos.2 hKpos
  have hSsq : Real.sqrt (KK i) * Real.sqrt (KK i) = (KK i : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by
    unfold KK; push_cast; ring
  rw [le_div_iff₀ (maxH_pos i)]
  refine le_trans ?_ hE1.le
  -- `(1 − 200/√K)·(k₄ H) ≤ k₄ H − 50 √K H` because `200 k₄ = 50 K = 50 √K·√K`
  have hH : (0 : ℝ) ≤ (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by positivity
  have hkey : (200 / Real.sqrt (KK i)) * (kk i : ℝ) = 50 * Real.sqrt (KK i) := by
    field_simp
    nlinarith [hSsq, hk4]
  unfold maxH
  have : (1 - 200 / Real.sqrt (KK i)) * ((kk i : ℝ) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ))
      = (kk i : ℝ) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ)
        - ((200 / Real.sqrt (KK i)) * (kk i : ℝ)) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    ring
  rw [this, hkey]

lemma tendsto_KK_atTop : Tendsto (fun i => (KK i : ℝ)) atTop atTop := by
  have : ∀ i : ℕ, (i : ℝ) ≤ (KK i : ℝ) := by
    intro i
    have : i ≤ KK i := by unfold KK kk; omega
    exact_mod_cast this
  exact tendsto_atTop_mono this tendsto_natCast_atTop_atTop

lemma tendsto_deficit : Tendsto (fun i => 200 / Real.sqrt (KK i)) atTop (nhds 0) := by
  have h : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
  have h2 : Tendsto (fun i => (Real.sqrt (KK i))⁻¹) atTop (nhds 0) := by
    exact h.inv_tendsto_atTop
  have h3 := h2.const_mul (200 : ℝ)
  simpa [div_eq_mul_inv] using h3

/-- **`E0` holds for `G₄`** — the brief's qualitative target, as a genuine limit. -/
theorem E0_primeLambertFour : E0 (primeLambertAtBase 4) := by
  have hlo : Tendsto (fun i => 1 - 200 / Real.sqrt (KK i)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub tendsto_deficit
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun i => one_sub_le_ratio i) (fun i => ratio_le_one i _)


/-! ### The sampled positions have density at most `1/4`

The count of `G4EntropyPositions` is `|S_K ∩ [0,L)| ≤ H_K·m_K·⌊L/(2 d_min)⌋`, and for the
implemented schedule `d_min = 1 + Q·D₀` with `Q ≥ U ≥ B^K` and `D₀ = K·U`, so
`2 d_min ≥ K·B^{2K}` — which beats `2^{i+3}·H_K·m_K` with room to spare.  Scales with
`2 d_min > L` contribute nothing, so at each `L` only the indices `i < L` matter and the
geometric series closes the sum at `L/4`. -/

/-- `d_min` at family index `i`: a lower bound for every multiplier `d_α`. -/
def dmin (i : ℕ) : ℕ := 1 + gridQ (KK i) (N (KK i)) * gridD₀ (KK i) (N (KK i))

lemma dmin_le_d (i : ℕ) (α : (gridAt i).Atom) : dmin i ≤ (gridAt i).d α :=
  gridOf_dmin_le (KK_one_le i) α

/-- The top term of `gridSum`. -/
lemma pow_le_gridSum {K : ℕ} (B : ℕ) (hK : 1 ≤ K) : B ^ K ≤ gridSum K B := by
  have hmem : (⟨K - 1, by omega⟩ : Fin K) ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
  have := Finset.single_le_sum (f := fun i : Fin K => B ^ ((i : ℕ) + 1))
    (fun i _ => Nat.zero_le _) hmem
  simpa [gridSum, show K - 1 + 1 = K by omega] using this

lemma pow_le_gridUmax {K N : ℕ} (hK : 1 ≤ K) : gridB K N ^ K ≤ gridUmax K N := by
  have h1 : gridB K N ^ K ≤ gridSum K (gridB K N) := pow_le_gridSum _ hK
  have h2 : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc gridB K N ^ K ≤ gridSum K (gridB K N) := h1
    _ = 1 * gridSum K (gridB K N) := (one_mul _).symm
    _ ≤ K ^ 2 * gridSum K (gridB K N) := Nat.mul_le_mul_right _ h2
    _ = gridUmax K N := rfl

lemma one_le_gridD₀ {K N : ℕ} (hK : 1 ≤ K) : 1 ≤ gridD₀ K N := by
  have h1 : 1 ≤ gridB K N ^ K := Nat.one_le_pow _ _ (by unfold gridB; omega)
  have h2 : gridB K N ^ K ≤ gridUmax K N := pow_le_gridUmax hK
  unfold gridD₀
  have : 1 * 1 ≤ K * gridUmax K N := Nat.mul_le_mul hK (le_trans h1 h2)
  omega

lemma two_mul_succ_le_gridB_sq {K N : ℕ} (hK : 2 ≤ K) : 2 * (K ^ 2 + 1) ≤ gridB K N ^ 2 := by
  have hcube : K ^ 3 ≤ gridB K N := by
    have h : K ^ 2 * K ≤ K ^ 2 * (K + N) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have hc : K ^ 3 = K ^ 2 * K := by ring
    unfold gridB
    omega
  have h2 : (K ^ 3) ^ 2 ≤ gridB K N ^ 2 := Nat.pow_le_pow_left hcube 2
  have hK2 : 4 ≤ K ^ 2 := by simpa using Nat.pow_le_pow_left hK 2
  have h3 : 2 * (K ^ 2 + 1) ≤ (K ^ 3) ^ 2 := by
    have ht : (K ^ 3) ^ 2 = K ^ 2 * (K ^ 2 * K ^ 2) := by ring
    rw [ht]
    nlinarith [hK2]
  omega

/-- **The decisive size inequality**: `2^{i+3}·H_K·m_K ≤ 2 d_min`.  `Q·D₀ ≥ K·B^{2K}` while
the left side is at most `(2(K²+1))^K·K`, and `2(K²+1) ≤ B²`. -/
theorem key_size (i : ℕ) :
    2 ^ (i + 3) * ((KK i ^ 2 + 1) ^ KK i * kk i) ≤ 2 * dmin i := by
  set K := KK i with hK
  set k := kk i with hk
  have hkK : k ≤ K := by rw [hK, hk]; unfold KK; omega
  have hik : i + 3 ≤ k := by rw [hk]; unfold kk; omega
  have hK2 : 2 ≤ K := by have := KK_ge i; omega
  have hK1 : 1 ≤ K := by omega
  -- left side
  have hL1 : 2 ^ (i + 3) ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) (by omega)
  have hL : 2 ^ (i + 3) * ((K ^ 2 + 1) ^ K * k) ≤ (2 * (K ^ 2 + 1)) ^ K * K := by
    calc 2 ^ (i + 3) * ((K ^ 2 + 1) ^ K * k)
        ≤ 2 ^ K * ((K ^ 2 + 1) ^ K * K) := Nat.mul_le_mul hL1 (Nat.mul_le_mul_left _ hkK)
      _ = (2 * (K ^ 2 + 1)) ^ K * K := by rw [mul_pow]; ring
  -- right side
  have hU : gridB K (N K) ^ K ≤ gridUmax K (N K) := pow_le_gridUmax hK1
  have hQ : gridUmax K (N K) ≤ gridQ K (N K) := by
    have := gridQ_gt K (N K); omega
  have hR : (gridB K (N K) ^ 2) ^ K * K
      ≤ gridQ K (N K) * gridD₀ K (N K) := by
    have hD : gridD₀ K (N K) = K * gridUmax K (N K) := rfl
    have h1 : gridB K (N K) ^ K * (K * gridB K (N K) ^ K)
        ≤ gridUmax K (N K) * (K * gridUmax K (N K)) :=
      Nat.mul_le_mul hU (Nat.mul_le_mul_left _ hU)
    have h2 : (gridB K (N K) ^ 2) ^ K * K
        = gridB K (N K) ^ K * (K * gridB K (N K) ^ K) := by
      rw [← pow_mul, mul_comm 2 K, pow_mul]
      ring
    rw [h2, hD]
    exact le_trans h1 (Nat.mul_le_mul_right _ hQ)
  have hB : 2 * (K ^ 2 + 1) ≤ gridB K (N K) ^ 2 := two_mul_succ_le_gridB_sq hK2
  have hBK : (2 * (K ^ 2 + 1)) ^ K ≤ (gridB K (N K) ^ 2) ^ K := Nat.pow_le_pow_left hB K
  calc 2 ^ (i + 3) * ((K ^ 2 + 1) ^ K * k)
      ≤ (2 * (K ^ 2 + 1)) ^ K * K := hL
    _ ≤ (gridB K (N K) ^ 2) ^ K * K := Nat.mul_le_mul_right _ hBK
    _ ≤ gridQ K (N K) * gridD₀ K (N K) := hR
    _ ≤ 2 * dmin i := by unfold dmin; rw [← hK]; omega

/-- `a·⌊L/(a·b)⌋ ≤ ⌊L/b⌋`. -/
lemma mul_div_mul_le (a b L : ℕ) : a * (L / (a * b)) ≤ L / b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  refine (Nat.le_div_iff_mul_le hb).2 ?_
  calc a * (L / (a * b)) * b = (L / (a * b)) * (a * b) := by ring
    _ ≤ L := Nat.div_mul_le_self _ _

/-- **Scale `i` contributes at most `L/2^{i+3}` positions below `L`.** -/
theorem card_sampledPosAt_lt_le (i L : ℕ) :
    ((sampledPosAt i).filter (fun j => j < L)).card ≤ L / 2 ^ (i + 3) := by
  have hApos : 0 < (KK i ^ 2 + 1) ^ KK i * kk i :=
    Nat.mul_pos (pow_pos (by omega) _) (by unfold kk; omega)
  have h2pos : 0 < 2 ^ (i + 3) := pow_pos (by omega) _
  have hkey : (KK i ^ 2 + 1) ^ KK i * kk i * 2 ^ (i + 3) ≤ 2 * dmin i := by
    have hk := key_size i
    calc (KK i ^ 2 + 1) ^ KK i * kk i * 2 ^ (i + 3)
        = 2 ^ (i + 3) * ((KK i ^ 2 + 1) ^ KK i * kk i) := by ring
      _ ≤ 2 * dmin i := hk
  have hdiv : L / (2 * dmin i) ≤ L / ((KK i ^ 2 + 1) ^ KK i * kk i * 2 ^ (i + 3)) :=
    Nat.div_le_div_left hkey (Nat.mul_pos hApos h2pos)
  have hcount : ((sampledPosAt i).filter (fun j => j < L)).card
      ≤ (KK i ^ 2 + 1) ^ KK i * kk i * (L / (2 * dmin i)) :=
    card_sampledPos_gridOf_le (KK_one_le i) (X (KK i)) (kk i) L
  calc ((sampledPosAt i).filter (fun j => j < L)).card
      ≤ (KK i ^ 2 + 1) ^ KK i * kk i * (L / (2 * dmin i)) := hcount
    _ ≤ (KK i ^ 2 + 1) ^ KK i * kk i
          * (L / ((KK i ^ 2 + 1) ^ KK i * kk i * 2 ^ (i + 3))) := Nat.mul_le_mul_left _ hdiv
    _ ≤ L / 2 ^ (i + 3) := mul_div_mul_le _ _ _

/-- Scale `i` never puts a position below `2 d_min(i)`, and `i < 2 d_min(i)`. -/
theorem le_of_mem_sampledPosAt {i j : ℕ} (hj : j ∈ sampledPosAt i) : i < j := by
  obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (gridAt i)).1 hj
  have hd : (gridAt i).d α ≤ kIdx (gridAt i) n α :=
    kIdx_ge_d (gridAt i) (gridOf_t_nonconstant (KK_one_le i)) hn α
  have hdm : dmin i ≤ (gridAt i).d α := dmin_le_d i α
  have hiQ : i ≤ gridQ (KK i) (N (KK i)) := by
    have h1 := gridQ_gt (KK i) (N (KK i))
    have h2 : i ≤ KK i := by unfold KK kk; omega
    omega
  have hD1 : 1 ≤ gridD₀ (KK i) (N (KK i)) := one_le_gridD₀ (KK_one_le i)
  have hiD : i ≤ gridQ (KK i) (N (KK i)) * gridD₀ (KK i) (N (KK i)) :=
    le_trans hiQ (Nat.le_mul_of_pos_right _ hD1)
  have : i < dmin i := by unfold dmin; omega
  omega

/-- The finite geometric bound `∑_{i<M} ⌊A/2^i⌋ ≤ 2A`. -/
lemma sum_div_two_pow_le : ∀ (M A : ℕ), ∑ i ∈ Finset.range M, A / 2 ^ i ≤ 2 * A := by
  intro M
  induction M with
  | zero => intro A; simp
  | succ M ih =>
    intro A
    rw [Finset.sum_range_succ']
    have hstep : ∀ i ∈ Finset.range M, A / 2 ^ (i + 1) = (A / 2) / 2 ^ i := by
      intro i _
      rw [Nat.div_div_eq_div_mul, pow_succ]
      ring_nf
    rw [Finset.sum_congr rfl hstep]
    have h1 := ih (A / 2)
    have h2 : 2 * (A / 2) ≤ A := Nat.mul_div_le A 2
    simp only [pow_zero, Nat.div_one]
    omega

/-- **The sampled positions have density at most `1/4`.**  This is the statement `T_E` would
have to contradict. -/
theorem card_isSampled_le (L : ℕ) :
    ((Finset.range L).filter IsSampled).card ≤ L / 4 := by
  have hsub : (Finset.range L).filter IsSampled
      ⊆ (Finset.range L).biUnion (fun i => (sampledPosAt i).filter (fun j => j < L)) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjL, i, hji⟩ := hj
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 ?_, Finset.mem_filter.2 ⟨hji, hjL⟩⟩
    exact lt_trans (le_of_mem_sampledPosAt hji) hjL
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum fun i _ => card_sampledPosAt_lt_le i L) ?_
  have hrw : ∀ i ∈ Finset.range L, L / 2 ^ (i + 3) = (L / 8) / 2 ^ i := by
    intro i _
    rw [Nat.div_div_eq_div_mul, pow_add]
    ring_nf
  rw [Finset.sum_congr rfl hrw]
  have h := sum_div_two_pow_le L (L / 8)
  have h8 : 8 * (L / 8) ≤ L := Nat.mul_div_le L 8
  have h4 : 2 * (L / 8) ≤ L / 4 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  omega


end NormalNumbers.G4.Sched
