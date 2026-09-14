/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPinsker
import NormalNumbers.G4EntropyDiagonal

/-!
# The `ℓ`-block coordinates of a sampled window

`ZSample_eq_blockVal` says the sampled value `Z^x_{K,α}(n)` is the `m`-bit binary window of `x`
at position `2·kIdx`.  The frequency theorem needs that window broken into its `ℓ`-bit *blocks*,
because the entropy of the whole window bounds the sum of the block entropies
(`FinLaw.H₂_le_sum_H₂_map`) and each block entropy bounds that block's word frequencies
(`sq_prob_sub_le_logb_card_sub_H₂`).

This module supplies the combinatorial layer, with no analysis in it at all.

* `blockVal_lt`, `blockVal_add` — the window value is an `m`-bit number, and a window splits as
  `blockVal y p (a+b) = blockVal y p a · 2^b + blockVal y (p+a) b`.  Everything else follows
  from these two.
* `blkAt m ℓ j : Fin (2^m) → Fin (2^ℓ)` — the `j`-th aligned `ℓ`-block of an `m`-bit value,
  namely `z / 2^(m − (j+1)ℓ) % 2^ℓ`.  The *last* index `j = m/ℓ` is the low-order `ℓ` bits
  (`m − (j+1)ℓ` truncates to `0`), which overlaps block `m/ℓ − 1` but sweeps up the `m % ℓ`
  leftover bits — that redundancy is exactly what makes the family jointly injective without
  assuming `ℓ ∣ m`.
* `blkAt_injective` — the `m/ℓ + 1` coordinates determine the window.  This is the hypothesis
  of `FinLaw.H₂_le_sum_H₂_map`, so it is the load-bearing statement of the module.
* `blkAt_blockVal` — the dictionary: for `(j+1)ℓ ≤ m` the `j`-th coordinate of a window of `x`
  is the `ℓ`-bit window of `x` at position `p + jℓ`.  This is what turns an entropy statement
  about the sample into a statement about the *digits* of `x`.
-/

open Finset

namespace NormalNumbers.G4Entropy

/-! ### Window arithmetic -/

/-- A length-`m` binary window is an `m`-bit number. -/
lemma blockVal_lt (y : ℝ) (p : ℕ) : ∀ m : ℕ, blockVal y p m < 2 ^ m := by
  intro m
  induction m with
  | zero => simp [blockVal]
  | succ m ih =>
    rw [blockVal_succ]
    have hd : digitOf 2 y (p + m) < 2 := digitOf_lt 2 le_rfl y _
    have : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega

/-- **Splitting a window.**  The first `a` digits contribute the high part, the next `b` the
low part. -/
lemma blockVal_add (y : ℝ) (p a : ℕ) : ∀ b : ℕ,
    blockVal y p (a + b) = blockVal y p a * 2 ^ b + blockVal y (p + a) b := by
  intro b
  induction b with
  | zero => simp [blockVal]
  | succ b ih =>
    have hassoc : p + (a + b) = (p + a) + b := by omega
    rw [show a + (b + 1) = (a + b) + 1 by omega, blockVal_succ, ih, blockVal_succ, hassoc]
    ring

/-! ### The block coordinates -/

/-- The `j`-th aligned `ℓ`-block of an `m`-bit value, read from the high end. -/
def blkAt (m ℓ j : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ ℓ) :=
  ⟨(z : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ, Nat.mod_lt _ (by positivity)⟩

@[simp] lemma blkAt_val (m ℓ j : ℕ) (z : Fin (2 ^ m)) :
    ((blkAt m ℓ j z : Fin (2 ^ ℓ)) : ℕ) = (z : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ := rfl

/-- The prefix recursion behind joint injectivity: agreeing on the first `j` blocks forces the
top `jℓ` bits to agree. -/
private lemma prefix_congr {m ℓ : ℕ} (hℓ : 0 < ℓ) {z z' : ℕ} (hz : z < 2 ^ m) (hz' : z' < 2 ^ m)
    (h : ∀ j < m / ℓ, z / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ
      = z' / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ) :
    ∀ j ≤ m / ℓ, z / 2 ^ (m - j * ℓ) = z' / 2 ^ (m - j * ℓ) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.zero_mul, Nat.sub_zero]
    rw [Nat.div_eq_of_lt hz, Nat.div_eq_of_lt hz']
  | succ j ih =>
    intro hj
    have hjr : j ≤ m / ℓ := by omega
    have hle : (j + 1) * ℓ ≤ m :=
      le_trans (Nat.mul_le_mul_right ℓ hj) (Nat.div_mul_le_self m ℓ)
    have hsplit : m - j * ℓ = (m - (j + 1) * ℓ) + ℓ := by
      have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
      omega
    have key : ∀ w : ℕ, w / 2 ^ (m - (j + 1) * ℓ)
        = 2 ^ ℓ * (w / 2 ^ (m - j * ℓ)) + (w / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := by
      intro w
      have hdd : w / 2 ^ (m - (j + 1) * ℓ) / 2 ^ ℓ = w / 2 ^ (m - j * ℓ) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add, ← hsplit]
      have hdm := Nat.div_add_mod (w / 2 ^ (m - (j + 1) * ℓ)) (2 ^ ℓ)
      rw [hdd] at hdm
      exact hdm.symm
    calc z / 2 ^ (m - (j + 1) * ℓ)
        = 2 ^ ℓ * (z / 2 ^ (m - j * ℓ)) + (z / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := key z
      _ = 2 ^ ℓ * (z' / 2 ^ (m - j * ℓ)) + (z' / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := by
          rw [ih hjr, h j (by omega)]
      _ = z' / 2 ^ (m - (j + 1) * ℓ) := (key z').symm

/-- **The `m/ℓ + 1` block coordinates determine the window.**  This is the joint-injectivity
hypothesis of `FinLaw.H₂_le_sum_H₂_map`.

No divisibility assumption: the last coordinate is the low `ℓ` bits, which overlaps the
previous block but covers the `m % ℓ` digits that the aligned blocks miss. -/
theorem blkAt_injective {m ℓ : ℕ} (hℓ : 0 < ℓ) :
    Function.Injective (fun z : Fin (2 ^ m) => fun j : Fin (m / ℓ + 1) => blkAt m ℓ j z) := by
  intro z z' hzz
  set r := m / ℓ with hr
  have hcoord : ∀ j : ℕ, j < r + 1 →
      (z : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ
        = (z' : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ := by
    intro j hj
    have := congrFun hzz ⟨j, hj⟩
    exact congrArg Fin.val this
  have hpre := prefix_congr hℓ z.isLt z'.isLt (fun j hj => hcoord j (by omega))
  -- the leftover `m % ℓ` bits
  have hmod : m % ℓ < ℓ := Nat.mod_lt _ hℓ
  have hdm : ℓ * r + m % ℓ = m := Nat.div_add_mod m ℓ
  have hrl : (r + 1) * ℓ = ℓ * r + ℓ := by ring
  have hlt : m < (r + 1) * ℓ := by omega
  have ht : m - r * ℓ = m % ℓ := by
    have : r * ℓ = ℓ * r := by ring
    omega
  have htop : (z : ℕ) / 2 ^ (m % ℓ) = (z' : ℕ) / 2 ^ (m % ℓ) := by
    have := hpre r le_rfl
    rwa [ht] at this
  have hlow : (z : ℕ) % 2 ^ (m % ℓ) = (z' : ℕ) % 2 ^ (m % ℓ) := by
    have hzero : m - (r + 1) * ℓ = 0 := by omega
    have hr1 := hcoord r (by omega)
    simp only [hzero, pow_zero, Nat.div_one] at hr1
    have hdvd : (2 : ℕ) ^ (m % ℓ) ∣ 2 ^ ℓ := pow_dvd_pow 2 hmod.le
    calc (z : ℕ) % 2 ^ (m % ℓ) = (z : ℕ) % 2 ^ ℓ % 2 ^ (m % ℓ) :=
          (Nat.mod_mod_of_dvd _ hdvd).symm
      _ = (z' : ℕ) % 2 ^ ℓ % 2 ^ (m % ℓ) := by rw [hr1]
      _ = (z' : ℕ) % 2 ^ (m % ℓ) := Nat.mod_mod_of_dvd _ hdvd
  refine Fin.ext ?_
  have hz := Nat.div_add_mod (z : ℕ) (2 ^ (m % ℓ))
  have hz' := Nat.div_add_mod (z' : ℕ) (2 ^ (m % ℓ))
  rw [htop, hlow] at hz
  omega

/-! ### The dictionary to digits -/

/-- **The `j`-th block coordinate of a window of `y` is the `ℓ`-bit window of `y` at
`p + jℓ`.** -/
theorem blkAt_blockVal (y : ℝ) (p m ℓ j : ℕ) (h : (j + 1) * ℓ ≤ m) :
    blkAt m ℓ j ⟨blockVal y p m, blockVal_lt y p m⟩
      = ⟨blockVal y (p + j * ℓ) ℓ, blockVal_lt y (p + j * ℓ) ℓ⟩ := by
  refine Fin.ext ?_
  rw [blkAt_val]
  set s := j * ℓ with hs
  set t := m - (j + 1) * ℓ with ht
  have hm : m = s + (ℓ + t) := by
    have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
    omega
  have hsplit : blockVal y p m
      = blockVal y (p + s + ℓ) t
        + (blockVal y (p + s) ℓ + blockVal y p s * 2 ^ ℓ) * 2 ^ t := by
    rw [hm, blockVal_add y p s (ℓ + t), blockVal_add y (p + s) ℓ t, pow_add]
    ring
  have hlowlt : blockVal y (p + s + ℓ) t < 2 ^ t := blockVal_lt _ _ _
  have hdiv : blockVal y p m / 2 ^ t
      = blockVal y (p + s) ℓ + blockVal y p s * 2 ^ ℓ := by
    rw [hsplit, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ t),
      Nat.div_eq_of_lt hlowlt]
    omega
  rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (blockVal_lt _ _ _)]


/-! ### The joint coordinate family and the deficit budget -/

/-- The `(α, j)` coordinate of a joint sample vector: the `j`-th `ℓ`-block of the window read
at atom `α`. -/
def blkCoord {A : Type*} (m ℓ : ℕ) (i : A × Fin (m / ℓ + 1)) (z : A → Fin (2 ^ m)) :
    Fin (2 ^ ℓ) :=
  blkAt m ℓ (i.2 : ℕ) (z i.1)

/-- The joint block coordinates determine the joint sample vector. -/
theorem blkCoord_injective {A : Type*} {m ℓ : ℕ} (hℓ : 0 < ℓ) :
    Function.Injective
      (fun z : A → Fin (2 ^ m) => fun i : A × Fin (m / ℓ + 1) => blkCoord m ℓ i z) := by
  intro z z' h
  funext α
  refine blkAt_injective (m := m) (ℓ := ℓ) hℓ ?_
  funext j
  exact congrFun h (α, j)

/-- Every block marginal has entropy at most `ℓ`, its alphabet being `2^ℓ` values. -/
lemma H₂_le_of_block {ℓ : ℕ} (M : FinLaw (Fin (2 ^ ℓ))) : M.H₂ ≤ (ℓ : ℝ) := by
  have hpos : 0 < Fintype.card (Fin (2 ^ ℓ)) := by
    simp only [Fintype.card_fin]; positivity
  refine (M.H₂_le_logb_card hpos).trans_eq ?_
  simp only [Fintype.card_fin]
  rw [show ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ by push_cast; ring]
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]

/-- **The deficit budget.**  A joint entropy within `Δ` of the maximum `m·|A|` leaves the block
marginals with a total entropy deficit of at most `|A|·ℓ + Δ`.

The `|A|·ℓ` slack is the price of the overlapping last block, which is what lets the statement
hold with no divisibility assumption between `ℓ` and `m`. -/
theorem sum_block_deficit_le {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : FinLaw (A → Fin (2 ^ m))) {Δ : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    ∑ i : A × Fin (m / ℓ + 1), ((ℓ : ℝ) - (L.map (blkCoord m ℓ i)).H₂)
      ≤ (Fintype.card A : ℝ) * (ℓ : ℝ) + Δ := by
  classical
  have hsub := L.H₂_le_sum_H₂_map (fun i : A × Fin (m / ℓ + 1) => blkCoord m ℓ i)
    (blkCoord_injective hℓ)
  have hcard : (Fintype.card (A × Fin (m / ℓ + 1)) : ℝ)
      = (Fintype.card A : ℝ) * ((m / ℓ : ℕ) + 1 : ℕ) := by
    simp [Fintype.card_prod]
  have hexp : ∑ i : A × Fin (m / ℓ + 1), ((ℓ : ℝ) - (L.map (blkCoord m ℓ i)).H₂)
      = (Fintype.card (A × Fin (m / ℓ + 1)) : ℝ) * (ℓ : ℝ)
        - ∑ i : A × Fin (m / ℓ + 1), (L.map (blkCoord m ℓ i)).H₂ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  -- `(r+1)·ℓ ≤ m + ℓ`
  have hrl : ((m / ℓ : ℕ) + 1 : ℕ) * (ℓ : ℝ) ≤ (m : ℝ) + (ℓ : ℝ) := by
    have hnat : (m / ℓ) * ℓ ≤ m := Nat.div_mul_le_self m ℓ
    have : ((m / ℓ * ℓ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnat
    push_cast at this ⊢
    nlinarith [this]
  have hA0 : (0 : ℝ) ≤ (Fintype.card A : ℝ) := by positivity
  rw [hexp, hcard]
  have hmul : (Fintype.card A : ℝ) * ((m / ℓ : ℕ) + 1 : ℕ) * (ℓ : ℝ)
      ≤ (Fintype.card A : ℝ) * ((m : ℝ) + (ℓ : ℝ)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hrl hA0
  nlinarith [hsub, hΔ, hmul]

/-! ### One coordinate: an entropy deficit bounds every word's bias -/

/-- **A near-maximal block entropy pins every word's probability.**  For a law on the `ℓ`-bit
alphabet, each single word's probability is within `√(2 log 2 · deficit)` of `2^{−ℓ}`. -/
theorem abs_prob_singleton_sub_le {ℓ : ℕ} (hℓ : 0 < ℓ) (M : FinLaw (Fin (2 ^ ℓ)))
    (w : Fin (2 ^ ℓ)) :
    |M.prob {w} - 1 / (2 : ℝ) ^ ℓ| ≤ Real.sqrt (2 * Real.log 2 * ((ℓ : ℝ) - M.H₂)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : Fintype.card (Fin (2 ^ ℓ)) = 2 ^ ℓ := Fintype.card_fin _
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hBc : ({w} : Finset (Fin (2 ^ ℓ)))ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton, hcard]
    omega
  have hkey := sq_prob_sub_le_logb_card_sub_H₂ M (Finset.singleton_nonempty w) hBc
  rw [Finset.card_singleton, hcard] at hkey
  have hlogb : Real.logb 2 ((2 ^ ℓ : ℕ) : ℝ) = (ℓ : ℝ) := by
    rw [show ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ by push_cast; ring]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  rw [hlogb] at hkey
  have hu : ((1 : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) = 1 / (2 : ℝ) ^ ℓ := by push_cast; ring
  rw [hu] at hkey
  set D : ℝ := (ℓ : ℝ) - M.H₂ with hD
  have hsq : (M.prob {w} - 1 / (2 : ℝ) ^ ℓ) ^ 2 ≤ 2 * Real.log 2 * D := by
    rw [div_le_iff₀ (by positivity)] at hkey
    nlinarith [hkey, hlog2]
  calc |M.prob {w} - 1 / (2 : ℝ) ^ ℓ|
      = Real.sqrt ((M.prob {w} - 1 / (2 : ℝ) ^ ℓ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * Real.log 2 * D) := Real.sqrt_le_sqrt hsq

/-! ### Averaging the square roots -/

/-- **√-averaging by AM-GM.**  If each `|g i − u|` is at most `√(e i)` and the `e i` sum to at
most `S`, then the average of the `g i` is within `S/(2tN) + t/2` of `u`, for every `t > 0`.
Taking `t` small and then `S/N` small is how the limit is extracted. -/
theorem abs_avg_sub_le {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι) (g e : ι → ℝ)
    (u S t : ℝ) (he : ∀ i, 0 ≤ e i) (hg : ∀ i, |g i - u| ≤ Real.sqrt (e i))
    (hS : ∑ i, e i ≤ S) (ht : 0 < t) :
    |(∑ i, g i) / (Fintype.card ι : ℝ) - u| ≤ S / (2 * t * (Fintype.card ι : ℝ)) + t / 2 := by
  have hN : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hι
  -- pointwise AM-GM
  have hstep : ∀ i, |g i - u| ≤ e i / (2 * t) + t / 2 := by
    intro i
    refine (hg i).trans ?_
    have hrhs : e i / (2 * t) + t / 2 = (e i + t ^ 2) / (2 * t) := by
      field_simp
    rw [hrhs, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t)]
    nlinarith [sq_nonneg (Real.sqrt (e i) - t), Real.sq_sqrt (he i)]
  have hrw : (∑ i, g i) / (Fintype.card ι : ℝ) - u
      = (∑ i, (g i - u)) / (Fintype.card ι : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    field_simp
  rw [hrw, abs_div, abs_of_pos hN]
  have habs : |∑ i, (g i - u)| ≤ ∑ i, |g i - u| := Finset.abs_sum_le_sum_abs _ _
  have hsum : ∑ i, |g i - u| ≤ (∑ i, e i) / (2 * t) + (Fintype.card ι : ℝ) * (t / 2) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
    calc ∑ i, |g i - u| ≤ ∑ i, (e i / (2 * t) + t / 2) := this
      _ = (∑ i, e i) / (2 * t) + (Fintype.card ι : ℝ) * (t / 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            ← Finset.sum_div]
  rw [div_le_iff₀ hN]
  have hSt : (∑ i, e i) / (2 * t) ≤ S / (2 * t) := by
    apply div_le_div_of_nonneg_right hS (by positivity)
  have hfin : (S / (2 * t * (Fintype.card ι : ℝ)) + t / 2) * (Fintype.card ι : ℝ)
      = S / (2 * t) + (Fintype.card ι : ℝ) * (t / 2) := by
    field_simp
  rw [hfin]
  linarith [habs, hsum, hSt]

/-! ### The pushforward of an empirical law is empirical -/

open Classical in
/-- Pushing an empirical law forward re-samples the composite statistic: the mass of `ω'` is the
sample density of `{i : g (f i) = ω'}`. -/
lemma map_empirical_p {ι Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']
    {S : Finset ι} (hS : S.Nonempty) (f : ι → Ω) (g : Ω → Ω') (ω' : Ω') :
    ((empirical S hS f).map g).p ω'
      = ((S.filter fun i => g (f i) = ω').card : ℝ) / S.card := by
  classical
  rw [FinLaw.map_p]
  simp only [empirical_p]
  rw [← Finset.sum_div]
  congr 1
  have hmaps : ∀ i ∈ S.filter (fun i => g (f i) = ω'),
      f i ∈ Finset.univ.filter (fun ω => g ω = ω') := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.1 hi).2
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hfib]
  push_cast
  refine Finset.sum_congr rfl fun ω hω => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
  have hfe : (S.filter fun i => g (f i) = ω').filter (fun a => f a = ω)
      = S.filter fun i => f i = ω := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]; exact hω⟩, h2⟩
  rw [hfe]

end NormalNumbers.G4Entropy
