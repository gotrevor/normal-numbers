/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSums
import NormalNumbers.LiteratureVandeheyDifferencing
import NormalNumbers.GrowingLocalizedLogExponent

/-!
# Sums of Stoneham constants with pairwise-coprime `c` are normal

Bailey–Borwein (Ramanujan J. 29, 2012, §4): "it is not known at the present time whether the sum
`α_{b,c₁} + α_{b,c₂}` is `b`-normal."  This file answers it for coprime `c₁, c₂`: every nonzero
rational combination of Stoneham constants `α_{b^{mᵢ}, cᵢ}` with the `cᵢ` pairwise coprime and
coprime to `b` is `b`-normal.  The coprimality is necessary: `α₂,₃ + α₄,₃` is not even simply
normal (`not_isSimplyNormal_stoneham_sum`).

Paper proof: `papers/2026-10-16-stoneham-sums-normal.md` (independently refereed, minor repairs
applied).  The one analytic input is Vandehey's Korobov-sum bound, here the cited
`VandeheyThm51`; the paper's (F3) is Vandehey's Corollary 1.2, which this file derives from it
(`vandeheyCor12_of_thm51`) rather than citing separately.
-/

namespace NormalNumbers.StonehamSumsNormal

open Finset NormalNumbers.G4 Literature.VandeheyDiff
open GrowingLocalizedLog

/-- **Vandehey, Corollary 1.2** (derived, not cited): for fixed `b`, a finite prime set `P`
coprime to `b`, and `ε > 0`, there are `δ > 0` and `C` such that for every `m ≥ 2` built from
`P`, every `a` coprime to `m`, and every `N ≥ m^ε`,
`|Σ_{n=1}^N e(a bⁿ/m)| ≤ C m^{−δ} N (1 + log m)`.  Vandehey §6.1: `N ≥ m` by the `k = 0`
case (his Lemma 2.3), `m^ε ≤ N ≤ m` by Theorem 5.1 at a `k` chosen from `ε`. -/
def VandeheyCor12 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ Nat.Coprime p b) →
    ∀ ε : ℝ, 0 < ε → ∃ δ C : ℝ, 0 < δ ∧
      ∀ (m : ℕ), 2 ≤ m → (∀ p, p.Prime → p ∣ m → p ∈ P) →
      ∀ (a : ℤ), IsCoprime a (m : ℤ) → ∀ N : ℕ, (m : ℝ) ^ ε ≤ N →
        ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)‖ ≤
          C * (m : ℝ) ^ (-δ) * N * (1 + Real.log m)

theorem vandeheyCor12_of_thm51 (hV : VandeheyThm51) : VandeheyCor12 := by
  intro b hb P hP ε hε
  let K : ℕ := ⌈1 / ε + 2⌉₊
  let s : ℝ := 1 / (2 : ℝ) ^ (K + 4)
  let δ : ℝ := min (1 / 2) (ε * s)
  let C : ℝ := ∑ k ∈ range (K + 1), ((constPair b P k).1 + (constPair b P k).2)
  have hs : 0 < s := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (mul_pos hε hs)
  refine ⟨δ, C, hδ, ?_⟩
  intro M hM hMP a ha N hMN
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hM0 : (0 : ℝ) < M := by positivity
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_rpow hM1 hε.le).trans hMN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  have hlog1 : 1 ≤ 1 + Real.log M := by linarith [Real.log_nonneg hM1]
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact sum_nonneg fun k _ => add_nonneg (constPair_nonneg b P k).1
      (constPair_nonneg b P k).2
  by_cases hMN' : M ≤ N
  · have hmain := hV b hb P hP M hM hMP a ha 0 N hNnat
    have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
    have hpowδ : (M : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (M : ℝ) ^ (-δ) := by
      exact Real.rpow_le_rpow_of_exponent_le hM1 (neg_le_neg hδhalf)
    have hroot : (M : ℝ) ^ (1 / 2 : ℝ) ≤
        (N : ℝ) * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        (M : ℝ) ^ (1 / 2 : ℝ) = (M : ℝ) ^ (1 + (-(1 / 2 : ℝ))) := by norm_num
        _ = (M : ℝ) ^ 1 * (M : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_add hM0 _ _
        _ = M * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ ≤ N * (M : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hMN')
            (Real.rpow_nonneg hM0.le _)
    have hcoeff : (constPair b P 0).1 + (constPair b P 0).2 ≤ C := by
      dsimp [C]
      apply single_le_sum (fun k _ => add_nonneg (constPair_nonneg b P k).1
        (constPair_nonneg b P k).2)
      simp
    have hA := (constPair_nonneg b P 0).1
    have hB := (constPair_nonneg b P 0).2
    calc
      ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / M)‖
          ≤ _ := hmain
      _ = ((constPair b P 0).1 * (M : ℝ) ^ (1 / 2 : ℝ) +
              (constPair b P 0).2 * (M : ℝ) ^ (-(1 / 2 : ℝ)) * N) *
            (1 + Real.log M) := by norm_num [alpha, expPair]
      _ ≤ (((constPair b P 0).1 + (constPair b P 0).2) *
              (N : ℝ) * (M : ℝ) ^ (-(1 / 2 : ℝ))) * (1 + Real.log M) := by
            gcongr
            nlinarith [mul_le_mul_of_nonneg_left hroot hA]
      _ ≤ (C * (N : ℝ) * (M : ℝ) ^ (-δ)) * (1 + Real.log M) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith [hlog1])
            calc
              ((constPair b P 0).1 + (constPair b P 0).2) * N *
                    (M : ℝ) ^ (-(1 / 2 : ℝ))
                  ≤ C * N * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by gcongr
              _ ≤ C * N * (M : ℝ) ^ (-δ) := by gcongr
      _ = C * (M : ℝ) ^ (-δ) * N * (1 + Real.log M) := by ring
  · have hNM : N < M := by omega
    have hN2 : 2 ≤ N := by
      by_contra hn
      have hNe : N = 1 := by omega
      subst N
      have hM1' : (1 : ℝ) < M := by exact_mod_cast hM
      have hpowgt : (1 : ℝ) < (M : ℝ) ^ ε := Real.one_lt_rpow hM1' hε
      norm_num at hMN
      linarith
    have hlogNM : Real.log N ≤ Real.log M :=
      Real.log_le_log hN0 (by exact_mod_cast hNM.le)
    have hLm : Real.log N ≤ 4 * Real.log M := by
      have := Real.log_nonneg hM1
      linarith
    obtain ⟨k, hk, hbound⟩ := vandehey_window_bound hV b hb P hP M hM hMP a ha N hN2 hLm
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hratio : Real.log M / Real.log N ≤ 1 / ε := by
      rw [div_le_iff₀ hlogN]
      have hlogpow := Real.log_le_log (by positivity : (0 : ℝ) < (M : ℝ) ^ ε) hMN
      rw [Real.log_rpow hM0] at hlogpow
      rw [show 1 / ε * Real.log N = Real.log N / ε by ring, le_div_iff₀ hε]
      simpa [mul_comm] using hlogpow
    have hkK : k ≤ K := by
      have hkR : (k : ℝ) ≤ 1 / ε + 2 := by linarith
      have hKR : 1 / ε + 2 ≤ (K : ℝ) := by
        dsimp [K]
        exact Nat.le_ceil _
      exact_mod_cast hkR.trans hKR
    have hcoeff : (constPair b P k).1 + (constPair b P k).2 ≤ C := by
      dsimp [C]
      apply single_le_sum (fun j _ => add_nonneg (constPair_nonneg b P j).1
        (constPair_nonneg b P j).2)
      simp only [mem_range]
      omega
    have hsk : s ≤ 1 / (2 : ℝ) ^ (k + 4) := by
      dsimp [s]
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpowSave : (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) ≤
        (N : ℝ) ^ (1 - s) := by
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have htheta : (2 : ℝ) ^ (-(k : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hlogpow : (1 + Real.log M) ^ ((2 : ℝ) ^ (-(k : ℝ))) ≤
        1 + Real.log M := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog1 htheta
    have hneg : (N : ℝ) ^ (-s) ≤ (M : ℝ) ^ (-ε * s) := by
      have ht := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hM0 ε) hMN
        (by linarith [hs] : -s ≤ 0)
      rw [← Real.rpow_mul hM0.le] at ht
      simpa [mul_assoc] using ht
    have hδeps : δ ≤ ε * s := min_le_right _ _
    have hdelta : (M : ℝ) ^ (-ε * s) ≤ (M : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    have hnegdelta : (N : ℝ) ^ (-s) ≤ (M : ℝ) ^ (-δ) := hneg.trans hdelta
    calc
      ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / M)‖
          ≤ ((constPair b P k).1 + (constPair b P k).2) *
              (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) *
                (1 + Real.log M) ^ ((2 : ℝ) ^ (-(k : ℝ))) := hbound
      _ ≤ C * (N : ℝ) ^ (1 - s) * (1 + Real.log M) := by gcongr
      _ = C * ((N : ℝ) * (N : ℝ) ^ (-s)) * (1 + Real.log M) := by
            rw [show 1 - s = 1 + (-s) by ring, Real.rpow_add hN0, Real.rpow_one]
      _ ≤ C * ((N : ℝ) * (M : ℝ) ^ (-δ)) * (1 + Real.log M) := by gcongr
      _ = C * (M : ℝ) ^ (-δ) * N * (1 + Real.log M) := by ring

/-! ### The rational orbit state -/

/-- The number of terms from the `i`-th Stoneham series which have entered the orbit by time `n`.
For the hypotheses of Theorem A this is the largest `K` with `m i * c i ^ K ≤ n`. -/
def stonehamK {r : ℕ} (c m : Fin r → ℕ) (i : Fin r) (n : ℕ) : ℕ :=
  Nat.log (c i) (n / m i)

lemma le_stonehamK_iff {r : ℕ} (c m : Fin r → ℕ) (i : Fin r) (n k : ℕ)
    (hc : 2 ≤ c i) (hm : 1 ≤ m i) (hk : 1 ≤ k) :
    k ≤ stonehamK c m i n ↔ m i * c i ^ k ≤ n := by
  unfold stonehamK
  by_cases hq : n / m i = 0
  · rw [hq, Nat.log_zero_right]
    constructor
    · omega
    · intro h
      have hp : c i ^ k ≤ n / m i := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < m i)]
        simpa [mul_comm] using h
      simp [hq] at hp
      omega
  · rw [Nat.le_log_iff_pow_le (by omega) hq,
      Nat.le_div_iff_mul_le (by omega : 0 < m i)]
    simp only [mul_comm]

/-- The rational truncation of `b^n · (L⁻¹ ∑ i, p i · α_{b^{m i},c i})` at all
terms whose base-`b` exponent is at most `n`. -/
noncomputable def stonehamState (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) : ℚ :=
  (1 / (L : ℚ)) * ∑ i, (p i : ℚ) *
    ∑ k ∈ Icc 1 (stonehamK c m i n),
      (b : ℚ) ^ (n - m i * c i ^ k) / (c i : ℚ) ^ k

/-- Lemma 2: between kicks, the rational state follows exact multiplication by the base. -/
lemma stonehamState_add_of_K_eq (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (s j : ℕ) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hK : ∀ i, stonehamK c m i (s + j) = stonehamK c m i s) :
    stonehamState b L c m p (s + j) = (b : ℚ) ^ j * stonehamState b L c m p s := by
  classical
  have hi : ∀ i : Fin r,
      ∑ k ∈ Icc 1 (stonehamK c m i (s + j)),
          (b : ℚ) ^ (s + j - m i * c i ^ k) / (c i : ℚ) ^ k =
        (b : ℚ) ^ j * ∑ k ∈ Icc 1 (stonehamK c m i s),
          (b : ℚ) ^ (s - m i * c i ^ k) / (c i : ℚ) ^ k := by
    intro i
    rw [hK i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := (Finset.mem_Icc.mp hk)
    have hkick : m i * c i ^ k ≤ s :=
      (le_stonehamK_iff c m i s k (hc i) (hm i) hk'.1).mp hk'.2
    have hsub : s + j - m i * c i ^ k = (s - m i * c i ^ k) + j := by omega
    rw [hsub, pow_add]
    ring
  rw [stonehamState, stonehamState]
  simp_rw [hi]
  have hsum : (∑ x, (p x : ℚ) * ((b : ℚ) ^ j *
        ∑ k ∈ Icc 1 (stonehamK c m x s),
          (b : ℚ) ^ (s - m x * c x ^ k) / (c x : ℚ) ^ k)) =
      (b : ℚ) ^ j * ∑ x, (p x : ℚ) *
        ∑ k ∈ Icc 1 (stonehamK c m x s),
          (b : ℚ) ^ (s - m x * c x ^ k) / (c x : ℚ) ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

/-- A finite sum of rationals which can all be written over `D` can itself be written over `D`. -/
lemma exists_int_div_nat_sum {a : Type*} [DecidableEq a] (s : Finset a) (f : a → ℚ)
    {D : ℕ} (_hD : D ≠ 0) (hf : ∀ x ∈ s, ∃ A : ℤ, f x = A / (D : ℚ)) :
    ∃ A : ℤ, ∑ x ∈ s, f x = A / (D : ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨A, hA⟩ := hf x (by simp)
      obtain ⟨B, hB⟩ := ih (fun y hy => hf y (by simp [hy]))
      refine ⟨A + B, ?_⟩
      rw [sum_insert hx, hA, hB]
      push_cast
      ring

/-- The explicit common denominator of the rational orbit state. -/
def stonehamStateDen (L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (n : ℕ) : ℕ :=
  L * ∏ i, c i ^ stonehamK c m i n

/-- Lemma 3(1), common-denominator part: the truncated orbit state has an integer numerator over
`L · ∏_i c_i^{K_i(n)}`.  In particular its reduced denominator divides this number. -/
lemma stonehamState_eq_int_div_den (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) (hL : L ≠ 0) (hc0 : ∀ i, c i ≠ 0) :
    ∃ A : ℤ, stonehamState b L c m p n = A / (stonehamStateDen L c m n : ℚ) := by
  classical
  let C : ℕ := ∏ i, c i ^ stonehamK c m i n
  have hC : C ≠ 0 := by
    dsimp [C]
    exact prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hc0 i)
  have hterm : ∀ (i : Fin r) (k : ℕ), k ∈ (Finset.Icc 1 (stonehamK c m i n)) →
      ∃ A : ℤ,
        (b : ℚ) ^ (n - m i * c i ^ k) / (c i : ℚ) ^ k = A / (C : ℚ) := by
    intro i k hk
    have hk_le : k ≤ stonehamK c m i n := (Finset.mem_Icc.mp hk).2
    have hd : c i ^ k ∣ C := by
      dsimp [C]
      refine dvd_trans (pow_dvd_pow (c i) hk_le) ?_
      exact Finset.dvd_prod_of_mem (fun j : Fin r => c j ^ stonehamK c m j n) (mem_univ i)
    obtain ⟨t, ht⟩ := hd
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht
      exact hC ht
    refine ⟨((b ^ (n - m i * c i ^ k) * t : ℕ) : ℤ), ?_⟩
    rw [ht]
    push_cast
    field_simp [hc0 i, ht0]
  have hi : ∀ i : Fin r, ∃ A : ℤ,
      (p i : ℚ) * ∑ k ∈ Icc 1 (stonehamK c m i n),
        (b : ℚ) ^ (n - m i * c i ^ k) / (c i : ℚ) ^ k = A / (C : ℚ) := by
    intro i
    obtain ⟨A, hA⟩ := exists_int_div_nat_sum (Icc 1 (stonehamK c m i n))
      (fun k => (b : ℚ) ^ (n - m i * c i ^ k) / (c i : ℚ) ^ k) hC (hterm i)
    refine ⟨p i * A, ?_⟩
    rw [hA]
    push_cast
    ring
  obtain ⟨A, hA⟩ := exists_int_div_nat_sum univ
    (fun i => (p i : ℚ) * ∑ k ∈ Icc 1 (stonehamK c m i n),
      (b : ℚ) ^ (n - m i * c i ^ k) / (c i : ℚ) ^ k) hC
    (fun i _ => hi i)
  refine ⟨A, ?_⟩
  rw [stonehamState, hA]
  dsimp [stonehamStateDen, C]
  push_cast
  field_simp

lemma stonehamState_den_dvd (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) (hL : L ≠ 0) (hc0 : ∀ i, c i ≠ 0) :
    (stonehamState b L c m p n).den ∣ stonehamStateDen L c m n := by
  obtain ⟨A, hA⟩ := stonehamState_eq_int_div_den b L c m p n hL hc0
  rw [hA]
  exact_mod_cast Rat.den_dvd A (stonehamStateDen L c m n)

/-- Each factor in the common denominator is at most the orbit time. -/
lemma stonehamK_pow_le {r : ℕ} (c m : Fin r → ℕ) (i : Fin r) (n : ℕ)
    (hn : n ≠ 0) : c i ^ stonehamK c m i n ≤ n := by
  unfold stonehamK
  by_cases hq : n / m i = 0
  · rw [hq, Nat.log_zero_right, pow_zero]
    exact Nat.one_le_iff_ne_zero.mpr hn
  · exact (Nat.pow_log_le_self (c i) hq).trans (Nat.div_le_self n (m i))

/-- Lemma 3(3), easy direction: the explicit common denominator is at most `L n^r`. -/
lemma stonehamStateDen_le (L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (n : ℕ)
    (hn : n ≠ 0) : stonehamStateDen L c m n ≤ L * n ^ r := by
  unfold stonehamStateDen
  gcongr
  calc
    ∏ i : Fin r, c i ^ stonehamK c m i n ≤ ∏ _i : Fin r, n := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => stonehamK_pow_le c m i n hn)
    _ = n ^ r := by simp

/-- Lemma 3(1), coprimality part: under the hypotheses of Proposition C, both the explicit and
reduced state denominators are coprime to the base. -/
lemma stonehamState_den_coprime (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) (hL : L ≠ 0) (hLb : Nat.Coprime L b)
    (hc0 : ∀ i, c i ≠ 0) (hcb : ∀ i, Nat.Coprime (c i) b) :
    Nat.Coprime (stonehamState b L c m p n).den b := by
  apply Nat.Coprime.of_dvd_left (stonehamState_den_dvd b L c m p n hL hc0)
  unfold stonehamStateDen
  exact Nat.Coprime.mul_left hLb
    (Nat.Coprime.prod_left fun i _ => (hcb i).pow_left (stonehamK c m i n))

/-- Lemma 3(1), smoothness part: every prime in the reduced state denominator already occurs in
`L` or in one of the fixed Stoneham parameters `c i`. -/
lemma prime_dvd_stonehamState_den (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n ℓ : ℕ) (hL : L ≠ 0) (hc0 : ∀ i, c i ≠ 0)
    (hℓ : ℓ.Prime) (hd : ℓ ∣ (stonehamState b L c m p n).den) :
    ℓ ∣ L ∨ ∃ i, ℓ ∣ c i := by
  have hbig : ℓ ∣ stonehamStateDen L c m n :=
    hd.trans (stonehamState_den_dvd b L c m p n hL hc0)
  rw [stonehamStateDen] at hbig
  rcases hℓ.dvd_mul.mp hbig with hL' | hprod
  · exact Or.inl hL'
  · rcases (Prime.dvd_finsetProd_iff hℓ.prime _).mp hprod with ⟨i, -, hi⟩
    exact Or.inr ⟨i, hℓ.dvd_of_dvd_pow hi⟩

/-- **Theorem A.**  Pairwise-coprime Stoneham families: every nonzero rational combination is
normal. -/
theorem isNormal_stonehamCombination (hV : VandeheyThm51)
    (b : ℕ) (hb : 2 ≤ b) {r : ℕ} (c m : Fin r → ℕ) (q : Fin r → ℚ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i) (hq : q ≠ 0) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (c i)) := by
  sorry

/-- **Headline.**  `α₂,₃ + α₂,₅` is normal in base 2 (Bailey's "Can we prove normality for
α2,3 + α2,5?"). -/
theorem isNormal_two_stoneham_three_add_five (hV : VandeheyThm51) :
    IsNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 2 5) := by
  let c : Fin 2 → ℕ := ![3, 5]
  let m : Fin 2 → ℕ := ![1, 1]
  let q : Fin 2 → ℚ := ![1, 1]
  have hc : ∀ i, 2 ≤ c i := by intro i; fin_cases i <;> norm_num [c]
  have hcop : Pairwise fun i j => Nat.Coprime (c i) (c j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [c]
    all_goals norm_num
  have hcb : ∀ i, Nat.Coprime (c i) 2 := by intro i; fin_cases i <;> norm_num [c]
  have hm : ∀ i, 1 ≤ m i := by intro i; fin_cases i <;> norm_num [m]
  have hq : q ≠ 0 := by
    intro h
    have := congrFun h (0 : Fin 2)
    norm_num [q] at this
  simpa [c, m, q, Fin.sum_univ_two] using
    isNormal_stonehamCombination hV 2 (by norm_num) c m q hc hcop hcb hm hq

end NormalNumbers.StonehamSumsNormal
