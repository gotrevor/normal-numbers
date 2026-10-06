/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorFiveMoment
import NormalNumbers.CantorExactExponent

/-!
# Base-5 coin points: head/tail split and prefix approximants

Head `hdF free ω n = Σ_{i<n} dᵢ 5^{n−1−i}`, tail `tlF`, and the prefix approximant `fA` read
from a coin prefix of length `D` (`⌈D/2⌉` digits, the last possibly half-known), with
`fA (pre ω D) ≤ ptF free ω ≤ fA (pre ω D) + 2^{−D}` (`fA_bounds`).
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorFiveNormal

open CantorFiveMoment CantorLiouville Derandomize

/-! ## Head and tail -/

def hdF (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, ptDigitF free ω i * 5 ^ (n - 1 - i)

theorem hdF_succ (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    hdF free ω (n + 1) = 5 * hdF free ω n + ptDigitF free ω n := by
  unfold hdF
  rw [Finset.sum_range_succ, Finset.mul_sum, show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, pow_succ]; ring

theorem hdF_congr (free : ℕ → Bool) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : ∀ j < n, ptDigitF free ω j = ptDigitF free ω' j) : hdF free ω n = hdF free ω' n := by
  unfold hdF
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem headF_eq (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    ((hdF free ω n : ℕ) : ℝ) / 5 ^ n =
      ∑ i ∈ Finset.range n, (ptDigitF free ω i : ℝ) / 5 ^ (i + 1) := by
  unfold hdF
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
    show n - 1 - i + (i + 1) = n by omega]

noncomputable def tlF (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑' k, (ptDigitF free ω (k + n) : ℝ) / (5 : ℝ) ^ (k + n + 1)

theorem ptF_split (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    ptF free ω = (hdF free ω n : ℝ) / 5 ^ n + tlF free ω n := by
  rw [headF_eq, ptF, realOfDigits, tlF]
  simp only [Nat.cast_ofNat]
  exact ((summable_ptDigitF free ω).sum_add_tsum_nat_add n).symm

theorem summable_tlF (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    Summable fun k => (ptDigitF free ω (k + n) : ℝ) / (5 : ℝ) ^ (k + n + 1) :=
  (summable_ptDigitF free ω).comp_injective (add_left_injective n)

theorem tlF_nonneg (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : 0 ≤ tlF free ω n :=
  tsum_nonneg fun k => by positivity

theorem tsum_four_geom (n : ℕ) :
    Summable (fun k : ℕ => (4 : ℝ) / 5 ^ (k + n + 1)) ∧
      ∑' k : ℕ, (4 : ℝ) / 5 ^ (k + n + 1) = 1 / 5 ^ n := by
  have hterm : (fun k : ℕ => (4 : ℝ) / 5 ^ (k + n + 1)) =
      fun k => 4 / 5 ^ (n + 1) * (5⁻¹ : ℝ) ^ k := by
    funext k; rw [inv_pow]; field_simp; ring
  have hgeo := summable_geometric_of_lt_one (r := (5 : ℝ)⁻¹) (by norm_num) (by norm_num)
  refine ⟨by rw [hterm]; exact hgeo.mul_left _, ?_⟩
  rw [hterm, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]
  field_simp; norm_num

theorem tlF_le (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : tlF free ω n ≤ 1 / 5 ^ n := by
  rw [← (tsum_four_geom n).2, tlF]
  refine (summable_tlF free ω n).tsum_le_tsum (fun k => ?_) (tsum_four_geom n).1
  have : (ptDigitF free ω (k + n) : ℝ) ≤ 4 := by exact_mod_cast ptDigitF_le_four _ _ _
  exact div_le_div_of_nonneg_right this (by positivity)

/-! ## Prefix approximants -/

/-- Digit `i` read from a coin prefix (missing coins read as `false`). -/
def fDig (free : ℕ → Bool) (p : List Bool) (i : ℕ) : ℕ :=
  bif free i then 3 * (bif p.getD (2 * i) false then 1 else 0) +
    (bif p.getD (2 * i + 1) false then 1 else 0) else 0

/-- Head numerator of `N` digits read from a prefix. -/
def fNum (free : ℕ → Bool) (N : ℕ) (p : List Bool) : ℕ :=
  ((List.range N).map fun i => fDig free p i * 5 ^ (N - 1 - i)).sum

/-- Number of digits a prefix of length `D` touches: `⌈D/2⌉`. -/
def fLen (D : ℕ) : ℕ := (D + 1) / 2

theorem fDig_eq (free : ℕ → Bool) (p : List Bool) (i : ℕ) :
    fDig free p i = ptDigitF free (fun j => p.getD j false) i := by
  unfold fDig ptDigitF
  dsimp only
  generalize p.getD (2 * i) false = a
  generalize p.getD (2 * i + 1) false = b
  cases free i <;> cases a <;> cases b <;> rfl

theorem fNum_eq (free : ℕ → Bool) (N : ℕ) (p : List Bool) :
    fNum free N p = hdF free (fun j => p.getD j false) N := by
  rw [fNum, ComputableNormalB.list_sum_range_map, hdF]
  exact Finset.sum_congr rfl fun i _ => by rw [fDig_eq]

theorem getD_pre' (ω : ℕ → Bool) (D j : ℕ) :
    (pre ω D).getD j false = if j < D then ω j else false := by
  split_ifs with h
  · exact getD_pre ω h
  · simp [pre, List.getD_eq_getElem?_getD, h]

/-- Lower approximation from a coin prefix. -/
noncomputable def fA (free : ℕ → Bool) (p : List Bool) : ℝ :=
  (fNum free (fLen p.length) p : ℝ) / 5 ^ fLen p.length

theorem ptDigitF_mono (free : ℕ → Bool) (ω ω' : ℕ → Bool) (h : ∀ j, ω' j = true → ω j = true)
    (i : ℕ) : ptDigitF free ω' i ≤ ptDigitF free ω i := by
  unfold ptDigitF
  have h1 := h (2 * i)
  have h2 := h (2 * i + 1)
  split_ifs
  · cases hb1 : ω' (2 * i) <;> cases hb2 : ω' (2 * i + 1) <;>
      cases hc1 : ω (2 * i) <;> cases hc2 : ω (2 * i + 1) <;> simp_all
  · exact le_rfl

theorem hdF_mono (free : ℕ → Bool) (ω ω' : ℕ → Bool) (h : ∀ j, ω' j = true → ω j = true)
    (n : ℕ) : hdF free ω' n ≤ hdF free ω n :=
  Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (ptDigitF_mono free ω ω' h i)

theorem fA_bounds (free : ℕ → Bool) (ω : ℕ → Bool) (D : ℕ) :
    fA free (pre ω D) ≤ ptF free ω ∧ ptF free ω ≤ fA free (pre ω D) + (1 / 2 : ℝ) ^ D := by
  set ω' : ℕ → Bool := fun j => (pre ω D).getD j false
  have hω' : ∀ j, ω' j = if j < D then ω j else false := fun j => getD_pre' ω D j
  set L := fLen D
  have hA : fA free (pre ω D) = (hdF free ω' L : ℝ) / 5 ^ L := by
    rw [fA, length_pre, fNum_eq]
  have hmono : hdF free ω' L ≤ hdF free ω L := hdF_mono free ω ω' (fun j hj => by
    rw [hω'] at hj; split_ifs at hj; exact hj) L
  rw [hA, ptF_split free ω L]
  have h0 := tlF_nonneg free ω L
  have h1 := tlF_le free ω L
  have h5 : (0 : ℝ) < 5 ^ L := by positivity
  have hmonoR : (hdF free ω' L : ℝ) ≤ hdF free ω L := by exact_mod_cast hmono
  refine ⟨by
    have : (hdF free ω' L : ℝ) / 5 ^ L ≤ (hdF free ω L : ℝ) / 5 ^ L :=
      div_le_div_of_nonneg_right hmonoR h5.le
    linarith, ?_⟩
  rcases Nat.even_or_odd D with ⟨L', hL'⟩ | ⟨L', hL'⟩
  · -- `D = 2L'`: every touched digit is fully known
    have hL : L = L' := by simp only [L, fLen]; omega
    have heq : hdF free ω' L = hdF free ω L := by
      refine hdF_congr free ω' ω L fun j hj => ?_
      simp only [ptDigitF, hω', if_pos (show 2 * j < D by omega),
        if_pos (show 2 * j + 1 < D by omega)]
    rw [heq]
    have : (1 : ℝ) / 5 ^ L ≤ (1 / 2 : ℝ) ^ D := by
      rw [hL', ← two_mul, pow_mul, hL, one_div_pow, one_div_pow]
      apply one_div_le_one_div_of_le (by positivity)
      norm_num
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) L'
    linarith
  · -- `D = 2L' + 1`: digit `L'` misses its second coin
    have hL : L = L' + 1 := by simp only [L, fLen]; omega
    have hlow : hdF free ω' L' = hdF free ω L' := by
      refine hdF_congr free ω' ω L' fun j hj => ?_
      simp only [ptDigitF, hω', if_pos (show 2 * j < D by omega),
        if_pos (show 2 * j + 1 < D by omega)]
    have hdig : ptDigitF free ω L' ≤ ptDigitF free ω' L' + 1 := by
      simp only [ptDigitF, hω', if_pos (show 2 * L' < D by omega),
        if_neg (show ¬ 2 * L' + 1 < D by omega)]
      split_ifs <;> cases ω (2 * L') <;> cases ω (2 * L' + 1) <;> simp
    have hdiff : hdF free ω L ≤ hdF free ω' L + 1 := by
      rw [hL, hdF_succ, hdF_succ, hlow]
      omega
    have hdiffR : (hdF free ω L : ℝ) ≤ hdF free ω' L + 1 := by exact_mod_cast hdiff
    have : (2 : ℝ) / 5 ^ L ≤ (1 / 2 : ℝ) ^ D := by
      have e : (1 / 2 : ℝ) ^ (2 * L' + 1) = 1 / (2 * 4 ^ L') := by
        rw [pow_succ, pow_mul]; norm_num [one_div_pow, inv_pow]
      rw [hL', hL, e, pow_succ]
      have h4 : (4 : ℝ) ^ L' ≤ 5 ^ L' := pow_le_pow_left₀ (by norm_num) (by norm_num) L'
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) L']
    have : (hdF free ω L : ℝ) / 5 ^ L ≤ (hdF free ω' L : ℝ) / 5 ^ L + 1 / 5 ^ L := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hdiffR h5.le
    have : (2 : ℝ) / 5 ^ L = 1 / 5 ^ L + 1 / 5 ^ L := by ring
    linarith

/-! ## Wiring to the family derandomizer -/

section Wiring

open CantorLiouvilleAll DecayAeNormal CantorExactExponent

/-- Base-`b` floors of the approximant. -/
def fΨ (free : ℕ → Bool) (b m : ℕ) (p : List Bool) : ℕ :=
  fNum free (fLen p.length) p * b ^ m / 5 ^ fLen p.length

theorem fΨ_eq (free : ℕ → Bool) (b m : ℕ) (p : List Bool) :
    fΨ free b m p = ⌊fA free p * (b : ℝ) ^ m⌋₊ := by
  rw [fA, show (fNum free (fLen p.length) p : ℝ) / 5 ^ fLen p.length * (b : ℝ) ^ m =
    ((fNum free (fLen p.length) p * b ^ m : ℕ) : ℝ) / ((5 ^ fLen p.length : ℕ) : ℝ) by
      push_cast; ring,
    Nat.floor_div_eq_div, fΨ]

theorem fA_nonneg (free : ℕ → Bool) (p : List Bool) : 0 ≤ fA free p := by unfold fA; positivity

theorem primrec_fDig {free : ℕ → Bool} (hf : Primrec free) :
    Primrec₂ fun (p : List Bool) (i : ℕ) => fDig free p i := by
  have hb : ∀ k : ℕ → ℕ, Primrec k → Primrec fun x : List Bool × ℕ =>
      (bif x.1.getD (k x.2) false then 1 else 0 : ℕ) := fun k hk =>
    Primrec.cond ((Primrec.list_getD false).comp Primrec.fst (hk.comp Primrec.snd))
      (Primrec.const 1) (Primrec.const 0)
  have h1 := hb (fun i => 2 * i) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
  have h2 := hb (fun i => 2 * i + 1)
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
  exact (Primrec.cond (hf.comp Primrec.snd)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) h1) h2)
    (Primrec.const 0)).to₂

theorem primrec_fNum {free : ℕ → Bool} (hf : Primrec free) :
    Primrec₂ fun (N : ℕ) (p : List Bool) => fNum free N p := by
  have hd := primrec_fDig hf
  have hg : Primrec₂ fun (x : ℕ × List Bool) (i : ℕ) => fDig free x.2 i * 5 ^ (x.1 - 1 - i) :=
    (Primrec.nat_mul.comp (hd.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (ComputableNormal.primrec_pow.comp (Primrec.const 5)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.const 1)) Primrec.snd))).to₂
  exact ((primrec_sum_map (Primrec.list_range.comp Primrec.fst) hg).of_eq fun x => rfl).to₂

theorem primrec_fΨ {free : ℕ → Bool} (hf : Primrec free) :
    Primrec fun x : ℕ × ℕ × List Bool => fΨ free x.1 x.2.1 x.2.2 := by
  have hp : Primrec fun x : ℕ × ℕ × List Bool => x.2.2 := Primrec.snd.comp Primrec.snd
  have hL : Primrec fun x : ℕ × ℕ × List Bool => fLen x.2.2.length :=
    Primrec.nat_div.comp (Primrec.succ.comp (Primrec.list_length.comp hp)) (Primrec.const 2)
  exact Primrec.nat_div.comp (Primrec.nat_mul.comp ((primrec_fNum hf).comp hL hp)
    (ComputableNormal.primrec_pow.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
    (ComputableNormal.primrec_pow.comp (Primrec.const 5) hL)

/-- Second-moment decay profile, base 5. -/
noncomputable def fW (free : ℕ → Bool) (N : ℕ) : ℝ :=
  Real.exp (-(Real.log 2 / 2) * freeCount free (Nat.log 5 N / 2)) +
    ((max N 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

theorem fW_nonneg (free : ℕ → Bool) (N : ℕ) : 0 ≤ fW free N := by unfold fW; positivity

theorem fW_antitone (free : ℕ → Bool) : Antitone (fW free) := by
  intro m n hmn
  unfold fW
  have hF : freeCount free (Nat.log 5 m / 2) ≤ freeCount free (Nat.log 5 n / 2) := by
    unfold freeCount
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono
      (Nat.div_le_div_right (Nat.log_mono_right hmn))))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hFR : (freeCount free (Nat.log 5 m / 2) : ℝ) ≤ freeCount free (Nat.log 5 n / 2) := by
    exact_mod_cast hF
  gcongr ?_ + ?_
  · exact Real.exp_le_exp.2 (by nlinarith)
  · apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
    exact_mod_cast max_le_max hmn le_rfl

theorem f_secondMoment_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ptF free ω)‖ ^ 2 ∂coins ≤
      ((16 * b ^ 6 : ℕ) : ℝ) * |(h : ℝ)| * N ^ 2 * fW free N := by
  have hW : fW free N = Real.exp (-(Real.log 2 / 2) * freeCount free (Nat.log 5 N / 2)) +
      (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [fW, max_eq_left hN]
  rw [hW]
  refine (secondMoment_le_bF free hb h5 h hh N hN).trans (le_of_eq ?_)
  push_cast; ring

theorem log_five_lt : Real.log 5 < 21 / 10 := by
  have h : Real.log 5 < Real.log 6 := Real.log_lt_log (by norm_num) (by norm_num)
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have := Real.log_two_lt_d9
  have := log_three_lt
  linarith

theorem M_ge_five (j n : ℕ) (hj : 900 ≤ j) (hn1 : 1 ≤ n) (hen : Real.exp (Real.sqrt j) ≤ n) :
    Real.sqrt j / 5 ≤ ((Nat.log 5 n / 2 : ℕ) : ℝ) := by
  set L := Nat.log 5 n
  have hn : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : (n : ℝ) < 5 ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
  have hlog : Real.log n < (L + 1) * Real.log 5 := by
    have := Real.log_lt_log hn hlt
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hsq : Real.sqrt j ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn]; exact hen
  have h5 := log_five_lt
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hL : Real.sqrt j / (21 / 10) - 1 < L := by
    have : Real.sqrt j < (L + 1) * (21 / 10) := by nlinarith
    have : Real.sqrt j / (21 / 10) < L + 1 := by rw [div_lt_iff₀ (by norm_num)]; linarith
    linarith
  have hM : ((L : ℝ) - 1) / 2 ≤ ((L / 2 : ℕ) : ℝ) := by
    have : L ≤ 2 * (L / 2) + 1 := by omega
    have : (L : ℝ) ≤ 2 * ((L / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have h30 : 30 ≤ Real.sqrt j := by
    rw [show (30 : ℝ) = Real.sqrt 900 by rw [show (900:ℝ) = 30 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hj)
  linarith

theorem f_ev (free : ℕ → Bool)
    (hFree : ∀ᶠ M : ℝ in atTop, ∀ n : ℕ, (n : ℝ) = M → Real.sqrt M / 2 ≤ freeCount free n) :
    ∀ᶠ j in atTop, 8 ≤ clNr j ∧ clNr j ≤ clNs j ∧
      (clNr j : ℝ) ^ 6 * fW free (clNs j) ≤ 1 / ((j : ℝ) + 1) ^ 4 := by
  set c : ℝ := Real.log 2 / 2 with hcdef
  have hc : 0 < c := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have hc1 : c ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); rw [hcdef]; linarith
  have hNs1 : ∀ j, 1 ≤ clNs j := fun j => by
    have := exp_sqrt_le_clNs j
    have h1 : (1 : ℝ) ≤ clNs j := (Real.one_le_exp (Real.sqrt_nonneg _)).trans this
    exact_mod_cast h1
  have hMev : ∀ᶠ j : ℕ in atTop, Real.sqrt j / 5 ≤ ((Nat.log 5 (clNs j) / 2 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop 900] with j hj
    exact M_ge_five j _ hj (hNs1 j) (exp_sqrt_le_clNs j)
  have hMt : Tendsto (fun j : ℕ => ((Nat.log 5 (clNs j) / 2 : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop hMev ?_
    exact (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hA' := hMt.eventually hFree
  have hB := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (ev_log_le (r := 1 / 4) (ε := c / 126)
    (by norm_num) (by positivity))
  filter_upwards [hA', hB, hMev, eventually_ge_atTop 900] with j hjA hjB hjM hj100
  set s := Nat.sqrt j
  set M := Nat.log 5 (clNs j) / 2
  set F := freeCount free M
  set q : ℝ := (j : ℝ) ^ (1 / 4 : ℝ)
  have hjR : (900 : ℝ) ≤ j := by exact_mod_cast hj100
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hs1 : s * s ≤ j := Nat.sqrt_le j
  have hs4 : 4 ≤ s := Nat.le_sqrt.2 (by omega)
  have hsj : s ≤ j := by nlinarith
  refine ⟨by unfold clNr; omega, ?_, ?_⟩
  · unfold clNr clNs
    have : s + 1 ≤ 4 ^ s := Nat.lt_pow_self (n := s) (by norm_num : 1 < 4)
    nlinarith
  have hF : Real.sqrt M / 2 ≤ F := hjA M rfl
  have hq0 : 0 ≤ q := by positivity
  have hqsq : q ^ 2 = Real.sqrt j := by
    simp only [q]
    rw [← sqrt_sqrt_eq _ hj0, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hsqM : q / 3 ≤ Real.sqrt M := by
    refine le_trans ?_ (Real.sqrt_le_sqrt hjM)
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, hqsq]
    have := Real.sqrt_nonneg (j : ℝ)
    linarith
  set E := Real.exp (-(c * q / 6)) with hE
  have hE1 : Real.exp (-(Real.log 2 / 2) * F) ≤ E := by
    apply Real.exp_le_exp.2
    have : c * (q / 6) ≤ c * F := mul_le_mul_of_nonneg_left (by linarith) hc.le
    rw [← hcdef]; linarith
  have hq : q ≤ Real.sqrt j := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hE2 : ((max (clNs j) 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ E := by
    rw [max_eq_left (hNs1 j)]
    calc ((clNs j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (Real.exp (Real.sqrt j)) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (exp_sqrt_le_clNs j) (by norm_num)
      _ = Real.exp (-(Real.sqrt j / 2)) := by rw [← Real.exp_mul]; ring_nf
      _ ≤ E := by
          apply Real.exp_le_exp.2
          have : c * q ≤ 1 * Real.sqrt j := mul_le_mul hc1 hq hq0 (by norm_num)
          linarith
  have hW : fW free (clNs j) ≤ 2 * E := by unfold fW; linarith
  have hlogj : 21 * Real.log j ≤ c * q / 6 := by
    have := hjB
    linarith
  have hpow : (j : ℝ) ^ 21 ≤ Real.exp (c * q / 6) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < (j : ℝ) ^ 21), Real.log_pow]
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  have hEm : E * Real.exp (c * q / 6) = 1 := by rw [hE, ← Real.exp_add]; simp
  have h2j : (2 : ℝ) * (2 * j) ^ 10 ≤ (j : ℝ) ^ 21 := by
    have : (2 : ℝ) ^ 11 ≤ (j : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) (by linarith) 11
    calc (2 : ℝ) * (2 * j) ^ 10 = 2 ^ 11 * (j : ℝ) ^ 10 := by ring
      _ ≤ (j : ℝ) ^ 11 * (j : ℝ) ^ 10 := by gcongr
      _ = _ := by ring
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hkey : (2 : ℝ) * (2 * j) ^ 10 * E ≤ 1 := by
    calc (2 : ℝ) * (2 * j) ^ 10 * E ≤ Real.exp (c * q / 6) * E :=
          mul_le_mul_of_nonneg_right (h2j.trans hpow) hE0
      _ = 1 := by rw [mul_comm]; exact hEm
  have hnr : (clNr j : ℝ) ≤ 2 * j := by
    unfold clNr; push_cast
    have : (s : ℝ) ≤ j := by exact_mod_cast hsj
    linarith
  have hj1 : (j : ℝ) + 1 ≤ 2 * j := by linarith
  have hJ0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [le_div_iff₀ (by positivity)]
  calc (clNr j : ℝ) ^ 6 * fW free (clNs j) * ((j : ℝ) + 1) ^ 4
      ≤ (2 * j) ^ 6 * (2 * E) * (2 * j) ^ 4 := by
        gcongr
        exact fW_nonneg free _
    _ = 2 * (2 * j) ^ 10 * E := by ring
    _ ≤ 1 := hkey

theorem primrec_notFiveDvd : PrimrecPred fun b : ℕ => ¬ 5 ∣ b := by
  have : PrimrecPred fun b : ℕ => b % 5 ≠ 0 :=
    PrimrecPred.not (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 5))
      (Primrec.const 0))
  exact this.of_eq fun b => by rw [Nat.dvd_iff_mod_eq_zero]

/-- **Family derandomization, base 5**, for any primitive-recursive free set whose free count
beats `√M/2`. -/
theorem exists_computable_normal_avoid_F (free : ℕ → Bool) (hfp : Primrec free)
    (hFree : ∀ᶠ M : ℝ in atTop, ∀ n : ℕ, (n : ℝ) = M → Real.sqrt M / 2 ≤ freeCount free n)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 5 ∣ b → IsNormal b (ptF free e)) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false := by
  obtain ⟨e, hce, hn, j₁, hj⟩ := exists_computable_normal_sched_family (fΨ free) (primrec_fΨ hfp)
    (fA free) (fΨ_eq free) (fA_nonneg free) (ptF free) (measurable_ptF free) (fA_bounds free)
    (fun b => ¬ 5 ∣ b) primrec_notFiveDvd (fun b => 16 * b ^ 6) primrec_kappa
    (fW free) (fW_nonneg free) (fW_antitone free)
    (fun b hb h5 h hh N hN => f_secondMoment_b free hb h5 h hh N hN)
    clNs clNr primrec_clNs primrec_clNr tendsto_clNs clNs_ratio tendsto_clNr (f_ev free hFree) bad'
    hbad' d' hd' hmass
  exact ⟨e, hce, fun b hb h5 => hn b hb h5, j₁, hj⟩

end Wiring

end NormalNumbers.CantorFiveNormal
