/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSums
import NormalNumbers.LiteratureVandeheyDifferencing
import NormalNumbers.GrowingLocalizedLogExponent
import NormalNumbers.DecayAeNormal

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

open Finset Filter Topology NormalNumbers.G4 Literature.VandeheyDiff
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

/-! ### The reduced-denominator lower bound -/

/-- Adding finitely many terms of strictly larger `ℓ`-adic valuation does not change the
valuation of a nonzero rational.  The nonvanishing conclusion is bundled with the valuation
identity so the induction does not lose information when the current valuation is zero. -/
lemma padicValRat_add_sum_eq_of_lt {a : Type*} [DecidableEq a]
    {ℓ : ℕ} [Fact ℓ.Prime] (q : ℚ) (hq : q ≠ 0) (s : Finset a) (f : a → ℚ)
    (hlt : ∀ i, i ∈ s → padicValRat ℓ q < padicValRat ℓ (f i)) :
    q + (∑ i ∈ s, f i) ≠ 0 ∧
      padicValRat ℓ (q + ∑ i ∈ s, f i) = padicValRat ℓ q := by
  induction s using Finset.induction_on with
  | empty => simpa using hq
  | @insert i s hi ih =>
      rw [sum_insert hi]
      obtain ⟨hrest0, hrest⟩ := ih (fun j hj => hlt j (by simp [hj]))
      by_cases hfi : f i = 0
      · simpa [hfi] using And.intro hrest0 hrest
      · have hsum0 : q + (∑ j ∈ s, f j) + f i ≠ 0 := by
          intro hz
          have heq : q + (∑ j ∈ s, f j) = -(f i) := by linarith
          have hv : padicValRat ℓ (q + ∑ j ∈ s, f j) = padicValRat ℓ (f i) := by
            rw [heq, padicValRat.neg]
          rw [hrest] at hv
          exact (ne_of_lt (hlt i (by simp))) hv
        refine ⟨by simpa [add_assoc, add_left_comm, add_comm] using hsum0, ?_⟩
        rw [show q + (f i + ∑ x ∈ s, f x) =
            (q + ∑ x ∈ s, f x) + f i by ring]
        rw [padicValRat.add_eq_of_lt hsum0 hrest0 hfi]
        · exact hrest
        · simpa [hrest] using hlt i (by simp)

/-- A finite sum whose terms all have nonnegative `ℓ`-adic valuation also has nonnegative
valuation (with the convention `padicValRat ℓ 0 = 0`). -/
lemma padicValRat_sum_nonneg {a : Type*} [DecidableEq a]
    {ℓ : ℕ} [Fact ℓ.Prime] (s : Finset a) (f : a → ℚ)
    (hf : ∀ i, i ∈ s → 0 ≤ padicValRat ℓ (f i)) :
    0 ≤ padicValRat ℓ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [sum_insert hi]
      by_cases hz : f i + ∑ j ∈ s, f j = 0
      · simp [hz]
      · exact le_trans (le_min (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj]))))
          (padicValRat.min_le_padicValRat_add hz)

/-- A natural-number specialization of the product-divisibility lemma for pairwise coprime
factors. -/
lemma nat_prod_dvd_of_pairwise_coprime {a : Type*} [DecidableEq a]
    (s : Finset a) (f : a → ℕ) (z : ℕ)
    (hcop : (s : Set a).Pairwise (Function.onFun Nat.Coprime f))
    (hdiv : ∀ i ∈ s, f i ∣ z) : (∏ i ∈ s, f i) ∣ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [prod_insert hi]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro j hj
        exact hcop (by simp) (by simp [hj]) (by aesop)
      · exact hdiv i (by simp)
      · exact ih (hcop.mono (by simp)) (fun j hj => hdiv j (by simp [hj]))

/-- The `ℓ`-adic valuation of one Stoneham orbit term.  Coprimality of `ℓ` and the base makes
the numerator a unit, so only the denominator contributes. -/
lemma padicValRat_stonehamTerm (b c m n k ℓ : ℕ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hℓ : ℓ.Prime) (hℓb : ¬ ℓ ∣ b) :
    padicValRat ℓ (((b : ℚ) ^ (n - m * c ^ k)) / (c : ℚ) ^ k) =
      -(k : ℤ) * padicValNat ℓ c := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  rw [padicValRat.div (pow_ne_zero _ (by exact_mod_cast hb))
      (pow_ne_zero _ (by exact_mod_cast hc)), padicValRat.pow, padicValRat.pow,
    padicValRat.of_nat, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hℓb]
  simp

/-- In one Stoneham family, the newest entered term is the unique strict `ℓ`-adic minimum for
every prime `ℓ ∣ c`. -/
lemma padicValRat_stonehamFamily (b c m n K ℓ : ℕ) (p : ℤ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hp : p ≠ 0) (hK : 1 ≤ K)
    (hℓ : ℓ.Prime) (hℓc : ℓ ∣ c) (hℓb : ¬ ℓ ∣ b) :
    padicValRat ℓ ((p : ℚ) *
        ∑ k ∈ Icc 1 K, ((b : ℚ) ^ (n - m * c ^ k)) / (c : ℚ) ^ k) =
      padicValInt ℓ p - (K : ℤ) * padicValNat ℓ c := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  let f : ℕ → ℚ := fun k =>
    (p : ℚ) * (((b : ℚ) ^ (n - m * c ^ k)) / (c : ℚ) ^ k)
  have hterm0 : ∀ k, ((b : ℚ) ^ (n - m * c ^ k)) / (c : ℚ) ^ k ≠ 0 := by
    intro k
    exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast hb))
      (pow_ne_zero _ (by exact_mod_cast hc))
  have hf0 : ∀ k, f k ≠ 0 := by
    intro k
    exact mul_ne_zero (by exact_mod_cast hp) (hterm0 k)
  have hfval : ∀ k, padicValRat ℓ (f k) =
      padicValInt ℓ p - (k : ℤ) * padicValNat ℓ c := by
    intro k
    rw [padicValRat.mul (by exact_mod_cast hp) (hterm0 k), padicValRat.of_int,
      padicValRat_stonehamTerm b c m n k ℓ hb hc hℓ hℓb]
    ring
  have hepos : 1 ≤ padicValNat ℓ c := one_le_padicValNat_of_dvd hc hℓc
  have hKmem : K ∈ Icc 1 K := by simp [hK]
  have hlt : ∀ j, j ∈ (Icc 1 K).erase K →
      padicValRat ℓ (f K) < padicValRat ℓ (f j) := by
    intro j hj
    rw [mem_erase] at hj
    rw [hfval, hfval]
    have hjlt : j < K := by
      have := (mem_Icc.mp hj.2).2
      omega
    have heposZ : (0 : ℤ) < padicValNat ℓ c := by exact_mod_cast hepos
    have hjltZ : (j : ℤ) < K := by exact_mod_cast hjlt
    have hmul : (j : ℤ) * padicValNat ℓ c <
        (K : ℤ) * padicValNat ℓ c := mul_lt_mul_of_pos_right hjltZ heposZ
    linarith
  obtain ⟨-, hv⟩ := padicValRat_add_sum_eq_of_lt (f K) (hf0 K)
    ((Icc 1 K).erase K) f hlt
  have hsum := sum_erase_add (Icc 1 K) f hKmem
  rw [Finset.mul_sum]
  change padicValRat ℓ (∑ k ∈ Icc 1 K, f k) = _
  rw [← hsum]
  simpa [add_comm, hfval] using hv

/-- The valuation estimate in paper Lemma 3: if the newest `i`-term has negative valuation,
then it survives both the older terms and every pairwise-coprime family.  The outside factor
`1/L` can only decrease its valuation. -/
lemma padicValRat_stonehamState_le (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) (i : Fin r) (ℓ : ℕ)
    (hb : b ≠ 0) (hL : L ≠ 0) (hc0 : ∀ j, c j ≠ 0)
    (hcb : ∀ j, Nat.Coprime (c j) b)
    (hcop : Pairwise fun j k => Nat.Coprime (c j) (c k))
    (hpi : p i ≠ 0) (hK : 1 ≤ stonehamK c m i n)
    (hℓ : ℓ.Prime) (hℓc : ℓ ∣ c i)
    (hneg : padicValInt ℓ (p i) <
      stonehamK c m i n * padicValNat ℓ (c i)) :
    padicValRat ℓ (stonehamState b L c m p n) ≤
      padicValInt ℓ (p i) -
        (stonehamK c m i n : ℤ) * padicValNat ℓ (c i) := by
  classical
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  let family : Fin r → ℚ := fun j =>
    (p j : ℚ) * ∑ k ∈ Icc 1 (stonehamK c m j n),
      ((b : ℚ) ^ (n - m j * c j ^ k)) / (c j : ℚ) ^ k
  have hℓb : ¬ ℓ ∣ b :=
    (hℓ.coprime_iff_not_dvd).mp (Nat.Coprime.of_dvd_left hℓc (hcb i))
  have hfamily_i : padicValRat ℓ (family i) =
      padicValInt ℓ (p i) -
        (stonehamK c m i n : ℤ) * padicValNat ℓ (c i) := by
    exact padicValRat_stonehamFamily b (c i) (m i) n (stonehamK c m i n) ℓ (p i)
      hb (hc0 i) hpi hK hℓ hℓc hℓb
  have hfamily_neg : padicValRat ℓ (family i) < 0 := by
    rw [hfamily_i]
    have hnegZ : (padicValInt ℓ (p i) : ℤ) <
        (stonehamK c m i n * padicValNat ℓ (c i) : ℕ) := by
      exact_mod_cast hneg
    push_cast at hnegZ
    omega
  have hfamily_i0 : family i ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hfamily_neg
    omega
  have hother : ∀ j, j ≠ i → 0 ≤ padicValRat ℓ (family j) := by
    intro j hji
    have hcij : Nat.Coprime (c i) (c j) := hcop hji.symm
    have hℓcj : ¬ ℓ ∣ c j :=
      (hℓ.coprime_iff_not_dvd).mp (Nat.Coprime.of_dvd_left hℓc hcij)
    dsimp [family]
    rw [Finset.mul_sum]
    apply padicValRat_sum_nonneg
    intro k hk
    by_cases hpj : p j = 0
    · simp [hpj]
    · rw [padicValRat.mul (by exact_mod_cast hpj)
          (div_ne_zero (pow_ne_zero _ (by exact_mod_cast hb))
            (pow_ne_zero _ (by exact_mod_cast hc0 j))),
        padicValRat.of_int,
        padicValRat_stonehamTerm b (c j) (m j) n k ℓ hb (hc0 j) hℓ hℓb,
        padicValNat.eq_zero_of_not_dvd hℓcj]
      simp
  obtain ⟨htotal0, htotal⟩ := padicValRat_add_sum_eq_of_lt (family i) hfamily_i0
    (univ.erase i) family (by
      intro j hj
      rw [mem_erase] at hj
      exact hfamily_neg.trans_le (hother j hj.1))
  have hsum := sum_erase_add univ family (mem_univ i)
  have htotal0' : (∑ j, family j) ≠ 0 := by
    rw [← hsum, add_comm]
    exact htotal0
  have htotal' : padicValRat ℓ (∑ j, family j) = padicValRat ℓ (family i) := by
    rw [← hsum, add_comm]
    exact htotal
  rw [stonehamState]
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL
  have honeL : (1 / (L : ℚ)) ≠ 0 := one_div_ne_zero hLq
  change padicValRat ℓ ((1 / (L : ℚ)) * ∑ j, family j) ≤ _
  rw [padicValRat.mul honeL htotal0', htotal', hfamily_i,
    padicValRat.div one_ne_zero hLq, padicValRat.one, padicValRat.of_nat]
  simp

/-- Each individual Stoneham-family denominator power divides the reduced denominator times its
coefficient. -/
lemma stonehamFamily_pow_dvd_den_mul_natAbs (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) (i : Fin r)
    (hb : b ≠ 0) (hL : L ≠ 0) (hc0 : ∀ j, c j ≠ 0)
    (hcb : ∀ j, Nat.Coprime (c j) b)
    (hcop : Pairwise fun j k => Nat.Coprime (c j) (c k))
    (hpi : p i ≠ 0) :
    c i ^ stonehamK c m i n ∣
      (stonehamState b L c m p n).den * (p i).natAbs := by
  apply (Nat.factorization_prime_le_iff_dvd
    (pow_ne_zero _ (hc0 i))
    (mul_ne_zero (Rat.den_nz _) (Int.natAbs_ne_zero.mpr hpi))).mp
  intro ℓ hℓ
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  rw [Nat.factorization_pow, Nat.factorization_mul (Rat.den_nz _)
      (Int.natAbs_ne_zero.mpr hpi)]
  simp only [Finsupp.smul_apply, Finsupp.add_apply, nsmul_eq_mul]
  rw [Nat.factorization_def _ hℓ, Nat.factorization_def _ hℓ,
    Nat.factorization_def _ hℓ]
  change stonehamK c m i n * padicValNat ℓ (c i) ≤
    padicValNat ℓ (stonehamState b L c m p n).den + padicValInt ℓ (p i)
  by_cases hℓc : ℓ ∣ c i
  · by_cases hle : stonehamK c m i n * padicValNat ℓ (c i) ≤
        padicValInt ℓ (p i)
    · omega
    · have hneg : padicValInt ℓ (p i) <
          stonehamK c m i n * padicValNat ℓ (c i) := by omega
      have hK : 1 ≤ stonehamK c m i n := by
        by_contra hk
        have : stonehamK c m i n = 0 := by omega
        simp [this] at hneg
      have hv := padicValRat_stonehamState_le b L c m p n i ℓ hb hL hc0 hcb hcop hpi hK
        hℓ hℓc hneg
      rw [padicValRat_def] at hv
      have hnum : (0 : ℤ) ≤ padicValInt ℓ (stonehamState b L c m p n).num := by
        positivity
      exact_mod_cast (show
        (stonehamK c m i n * padicValNat ℓ (c i) : ℕ) ≤
          padicValNat ℓ (stonehamState b L c m p n).den + padicValInt ℓ (p i) by
            omega)
  · simp [padicValNat.eq_zero_of_not_dvd hℓc]

/-- Paper Lemma 3(2), divisibility form: pairwise coprimality lets the individual family bounds
multiply without counting the reduced denominator more than once. -/
lemma stonehamProduct_dvd_den_mul_natAbs (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ)
    (hb : b ≠ 0) (hL : L ≠ 0) (hc0 : ∀ j, c j ≠ 0)
    (hcb : ∀ j, Nat.Coprime (c j) b)
    (hcop : Pairwise fun j k => Nat.Coprime (c j) (c k))
    (hp : ∀ i, p i ≠ 0) :
    (∏ i, c i ^ stonehamK c m i n) ∣
      (stonehamState b L c m p n).den * ∏ i, (p i).natAbs := by
  refine nat_prod_dvd_of_pairwise_coprime univ
    (fun i => c i ^ stonehamK c m i n)
    ((stonehamState b L c m p n).den * ∏ i, (p i).natAbs) ?_ ?_
  · intro i hi j hj hij
    exact (((hcop hij).pow_left (stonehamK c m i n)).pow_right
      (stonehamK c m j n))
  · intro i hi
    exact (stonehamFamily_pow_dvd_den_mul_natAbs b L c m p n i hb hL hc0 hcb hcop
      (hp i)).trans
      (Nat.mul_dvd_mul_left (stonehamState b L c m p n).den
        (Finset.dvd_prod_of_mem (fun j : Fin r => (p j).natAbs) (mem_univ i)))

/-- The next not-yet-entered Stoneham kick is beyond time `n`. -/
lemma lt_mul_stonehamK_succ {r : ℕ} (c m : Fin r → ℕ)
    (i : Fin r) (n : ℕ) (hc : 2 ≤ c i) (hm : 1 ≤ m i) :
    n < m i * c i ^ (stonehamK c m i n + 1) := by
  have hlog := Nat.lt_pow_succ_log_self (by omega : 1 < c i) (n / m i)
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < m i)] at hlog
  simpa [stonehamK, mul_comm] using hlog

/-! ### Approximation by the rational state -/

/-- The defining series of a Stoneham constant is summable under the hypotheses used below. -/
lemma summable_stonehamAlpha_term (B c : ℕ) (hB : 1 ≤ B) (hc : 2 ≤ c) :
    Summable (fun j : ℕ =>
      1 / ((c : ℝ) ^ (j + 1) * (B : ℝ) ^ (c ^ (j + 1)))) := by
  have hr0 : (0 : ℝ) ≤ 1 / c := by positivity
  have hr1 : (1 : ℝ) / c < 1 := by
    rw [div_lt_one]
    · exact_mod_cast (by omega : 1 < c)
    · positivity
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left (1 / (c : ℝ)))
  rw [show (1 / (c : ℝ)) * (1 / c) ^ j = 1 / (c : ℝ) ^ (j + 1) by
    rw [pow_succ]; ring]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have hBpow : (1 : ℝ) ≤ (B : ℝ) ^ (c ^ (j + 1)) :=
    one_le_pow₀ (by exact_mod_cast hB)
  nlinarith [show (0 : ℝ) < (c : ℝ) ^ (j + 1) by positivity]

/-- The first `K` terms of the scaled Stoneham series are exactly the rational orbit terms. -/
lemma stonehamAlpha_head (b c m n K : ℕ) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hkick : ∀ k ∈ Icc 1 K, m * c ^ k ≤ n) :
    (∑ j ∈ range K,
        (b : ℝ) ^ n /
          ((c : ℝ) ^ (j + 1) * ((b ^ m : ℕ) : ℝ) ^ (c ^ (j + 1)))) =
      ∑ k ∈ Icc 1 K,
        (b : ℝ) ^ (n - m * c ^ k) / (c : ℝ) ^ k := by
  rw [show Icc 1 K = Ico 1 (K + 1) from by
    ext u
    simp only [mem_Icc, mem_Ico]
    omega,
    sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply sum_congr rfl
  intro j hj
  have hjK : j < K := mem_range.mp hj
  have hle : m * c ^ (j + 1) ≤ n := hkick (j + 1) (by simp [hjK])
  push_cast
  rw [show ((b : ℝ) ^ m) ^ (c ^ (j + 1)) =
      (b : ℝ) ^ (m * c ^ (j + 1)) by rw [pow_mul]]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  rw [show 1 + j = j + 1 by omega]
  conv_lhs =>
    rw [show n = (n - m * c ^ (j + 1)) + m * c ^ (j + 1) by omega,
      pow_add]
  ring

/-- The scaled tail after the last entered kick is nonnegative and at most `c⁻ᴷ`. -/
lemma stonehamAlpha_tail_le (b c m n K : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hentered : ∀ k ∈ Icc 1 K, m * c ^ k ≤ n)
    (hnext : n < m * c ^ (K + 1)) :
    0 ≤ (b : ℝ) ^ n * stonehamAlpha (b ^ m) c -
        ∑ k ∈ Icc 1 K,
          (b : ℝ) ^ (n - m * c ^ k) / (c : ℝ) ^ k ∧
      (b : ℝ) ^ n * stonehamAlpha (b ^ m) c -
          ∑ k ∈ Icc 1 K,
            (b : ℝ) ^ (n - m * c ^ k) / (c : ℝ) ^ k ≤
        1 / (c : ℝ) ^ K := by
  set t : ℕ → ℝ := fun j =>
    1 / ((c : ℝ) ^ (j + 1) * ((b ^ m : ℕ) : ℝ) ^ (c ^ (j + 1))) with ht
  set g : ℕ → ℝ := fun j => (b : ℝ) ^ n * t j with hg
  have ht_sum : Summable t := by
    simpa only [ht] using summable_stonehamAlpha_term (b ^ m) c
      (one_le_pow₀ (by omega)) hc
  have hg_sum : Summable g := ht_sum.mul_left _
  have hmul : (b : ℝ) ^ n * stonehamAlpha (b ^ m) c = ∑' j, g j := by
    rw [stonehamAlpha, tsum_mul_left]
  have hhead : (∑ j ∈ range K, g j) =
      ∑ k ∈ Icc 1 K,
        (b : ℝ) ^ (n - m * c ^ k) / (c : ℝ) ^ k := by
    simp only [hg, ht, mul_one_div]
    exact stonehamAlpha_head b c m n K (by omega) (by omega) hentered
  have hsplit : ∑' j, g j = (∑ j ∈ range K, g j) + ∑' j, g (j + K) :=
    (hg_sum.sum_add_tsum_nat_add K).symm
  have hshift : Summable fun j => g (j + K) := (summable_nat_add_iff K).2 hg_sum
  have htail_nonneg : 0 ≤ ∑' j, g (j + K) := by
    exact tsum_nonneg fun j => by simp only [hg, ht]; positivity
  have hr0 : (0 : ℝ) ≤ 1 / c := by positivity
  have hr1 : (1 : ℝ) / c < 1 := by
    rw [div_lt_one]
    · exact_mod_cast (by omega : 1 < c)
    · positivity
  have hgeom : Summable fun j : ℕ => (1 / (c : ℝ)) ^ (j + K + 1) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left
      ((1 / (c : ℝ)) ^ (K + 1))
    refine h.congr fun j => ?_
    rw [← pow_add]
    congr 1
    omega
  have hterm : ∀ j, g (j + K) ≤ (1 / (c : ℝ)) ^ (j + K + 1) := by
    intro j
    have hexp : n ≤ m * c ^ (j + K + 1) := by
      have hp : c ^ (K + 1) ≤ c ^ (j + K + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact hnext.le.trans (Nat.mul_le_mul_left m hp)
    have hbpow : (b : ℝ) ^ n ≤ (b : ℝ) ^ (m * c ^ (j + K + 1)) :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) hexp
    simp only [hg, ht]
    push_cast
    rw [show (((b : ℝ) ^ m) ^ (c ^ (j + K + 1))) =
      (b : ℝ) ^ (m * c ^ (j + K + 1)) by rw [pow_mul]]
    calc
      (b : ℝ) ^ n *
            (1 / ((c : ℝ) ^ (j + K + 1) *
              (b : ℝ) ^ (m * c ^ (j + K + 1))))
          = (b : ℝ) ^ n /
              ((c : ℝ) ^ (j + K + 1) *
                (b : ℝ) ^ (m * c ^ (j + K + 1))) := by ring
      _ ≤ (b : ℝ) ^ (m * c ^ (j + K + 1)) /
              ((c : ℝ) ^ (j + K + 1) *
                (b : ℝ) ^ (m * c ^ (j + K + 1))) :=
        div_le_div_of_nonneg_right hbpow (by positivity)
      _ = 1 / (c : ℝ) ^ (j + K + 1) := by field_simp
      _ = (1 / (c : ℝ)) ^ (j + K + 1) := by rw [div_pow]; simp
  have htail_le : ∑' j, g (j + K) ≤ 1 / (c : ℝ) ^ K := by
    refine (hshift.tsum_le_tsum hterm hgeom).trans ?_
    have heval : (∑' j : ℕ, (1 / (c : ℝ)) ^ (j + K + 1)) =
        (1 / (c : ℝ)) ^ (K + 1) * (1 - 1 / (c : ℝ))⁻¹ := by
      rw [show (fun j : ℕ => (1 / (c : ℝ)) ^ (j + K + 1)) =
        fun j => (1 / (c : ℝ)) ^ (K + 1) * (1 / (c : ℝ)) ^ j by
          funext j
          rw [← pow_add]
          congr 1
          omega,
        tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    rw [heval, pow_succ]
    have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
    have hc0 : (0 : ℝ) < c := by positivity
    have hcm1 : (0 : ℝ) < (c : ℝ) - 1 := by linarith
    calc
      (1 / (c : ℝ)) ^ K * (1 / (c : ℝ)) *
          (1 - 1 / (c : ℝ))⁻¹ =
          (1 / (c : ℝ)) ^ K / ((c : ℝ) - 1) := by
        field_simp [hc0.ne', hcm1.ne']
      _ ≤ (1 / (c : ℝ)) ^ K := div_le_self (by positivity) (by linarith)
      _ = 1 / (c : ℝ) ^ K := by rw [div_pow]; simp
  rw [hmul, hsplit, hhead]
  constructor <;> linarith

/-- Paper Lemma 1 for one Stoneham family.  The deliberately loose constant `m*c` is fixed
with the parameters and is sufficient for the harmonic-average transfer. -/
lemma stonehamAlpha_family_approx {r : ℕ} (b : ℕ) (c m : Fin r → ℕ)
    (i : Fin r) (n : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c i) (hm : 1 ≤ m i)
    (hn : 1 ≤ n) :
    |(b : ℝ) ^ n * stonehamAlpha (b ^ m i) (c i) -
        ∑ k ∈ Icc 1 (stonehamK c m i n),
          (b : ℝ) ^ (n - m i * c i ^ k) / (c i : ℝ) ^ k| ≤
      ((m i * c i : ℕ) : ℝ) / n := by
  obtain ⟨htail0, htail⟩ := stonehamAlpha_tail_le b (c i) (m i) n
    (stonehamK c m i n) hb hc
    (fun k hk => (le_stonehamK_iff c m i n k hc hm (mem_Icc.mp hk).1).mp
      (mem_Icc.mp hk).2)
    (lt_mul_stonehamK_succ c m i n hc hm)
  rw [abs_of_nonneg htail0]
  refine htail.trans ?_
  have hnext := lt_mul_stonehamK_succ c m i n hc hm
  rw [pow_succ] at hnext
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcKR : (0 : ℝ) < (c i : ℝ) ^ stonehamK c m i n := by positivity
  have hcast : (n : ℝ) < (m i : ℝ) * (c i : ℝ) ^ stonehamK c m i n * c i := by
    exact_mod_cast (show n < m i * c i ^ stonehamK c m i n * c i by
      simpa [mul_assoc] using hnext)
  rw [show ((m i * c i : ℕ) : ℝ) = (m i : ℝ) * c i by norm_num]
  apply (div_le_div_iff₀ hcKR hnR).2
  nlinarith

/-- Paper Lemma 1 for the full rational combination: the real orbit differs from the rational
state by `O(1/n)`, with a constant depending only on the fixed coefficients and parameters. -/
lemma stonehamCombination_approx (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i) (hn : 1 ≤ n) :
    |(b : ℝ) ^ n * ((1 / (L : ℝ)) *
          ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) -
        (stonehamState b L c m p n : ℝ)| ≤
      (∑ i, |(p i : ℝ)| * ((m i * c i : ℕ) : ℝ)) / n := by
  let d : Fin r → ℝ := fun i =>
    (b : ℝ) ^ n * stonehamAlpha (b ^ m i) (c i) -
      ∑ k ∈ Icc 1 (stonehamK c m i n),
        (b : ℝ) ^ (n - m i * c i ^ k) / (c i : ℝ) ^ k
  have hd : ∀ i, |d i| ≤ ((m i * c i : ℕ) : ℝ) / n := fun i =>
    stonehamAlpha_family_approx b c m i n hb (hc i) (hm i) hn
  have hfirst : (∑ i, (p i : ℝ) *
        ((b : ℝ) ^ n * stonehamAlpha (b ^ m i) (c i))) =
      (b : ℝ) ^ n *
        ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have heq : (b : ℝ) ^ n * ((1 / (L : ℝ)) *
          ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) -
        (stonehamState b L c m p n : ℝ) =
      (1 / (L : ℝ)) * ∑ i, (p i : ℝ) * d i := by
    rw [stonehamState]
    push_cast
    simp only [d]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hfirst]
    ring
  rw [heq, abs_mul]
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLabs : |1 / (L : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < L)).2
    simpa using hLR
  calc
    |1 / (L : ℝ)| * |∑ i, (p i : ℝ) * d i|
        ≤ |∑ i, (p i : ℝ) * d i| := by
          simpa using mul_le_of_le_one_left (abs_nonneg _) hLabs
    _ ≤ ∑ i, |(p i : ℝ) * d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(p i : ℝ)| * (((m i * c i : ℕ) : ℝ) / n) := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hd i) (abs_nonneg _)
    _ = (∑ i, |(p i : ℝ)| * ((m i * c i : ℕ) : ℝ)) / n := by
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro i hi
      ring

/-- Paper Lemma 3(2–3), cross-multiplied form.  This is the polynomial lower bound on the
reduced denominator, with the explicit constant kept integral:
`n^r ≤ den(S_n) · (∏ |p_i|) · (∏ m_i c_i)`. -/
lemma stonehamState_den_lower_cross (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ)
    (hb : b ≠ 0) (hL : L ≠ 0) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ j, Nat.Coprime (c j) b)
    (hcop : Pairwise fun j k => Nat.Coprime (c j) (c k))
    (hp : ∀ i, p i ≠ 0) :
    n ^ r ≤ (stonehamState b L c m p n).den *
      ((∏ i, (p i).natAbs) * ∏ i, m i * c i) := by
  have hc0 : ∀ i, c i ≠ 0 := fun i =>
    ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two (hc i))
  have hdvd := stonehamProduct_dvd_den_mul_natAbs b L c m p n hb hL hc0 hcb hcop hp
  have hpabs : ∀ i, 0 < (p i).natAbs := fun i => Int.natAbs_pos.mpr (hp i)
  have hprodabs : 0 < ∏ i, (p i).natAbs := prod_pos fun i _ => hpabs i
  have hpow_le : (∏ i, c i ^ stonehamK c m i n) ≤
      (stonehamState b L c m p n).den * ∏ i, (p i).natAbs :=
    Nat.le_of_dvd (mul_pos (Rat.den_pos _) hprodabs) hdvd
  calc
    n ^ r = ∏ _i : Fin r, n := by simp
    _ ≤ ∏ i, (m i * c i) * c i ^ stonehamK c m i n := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      have h := lt_mul_stonehamK_succ c m i n (hc i) (hm i)
      rw [pow_succ] at h
      nlinarith
    _ = (∏ i, m i * c i) * ∏ i, c i ^ stonehamK c m i n := by
      rw [Finset.prod_mul_distrib]
    _ ≤ (∏ i, m i * c i) *
        ((stonehamState b L c m p n).den * ∏ i, (p i).natAbs) := by
      gcongr
    _ = (stonehamState b L c m p n).den *
        ((∏ i, (p i).natAbs) * ∏ i, m i * c i) := by
      ac_rfl

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

lemma sum_range_mul_blocks (f : ℕ → ℂ) (G H : ℕ) :
    ∑ n ∈ range (G * H), f n = ∑ j ∈ range G, ∑ t ∈ range H, f (j * H + t) := by
  induction G with
  | zero => simp
  | succ G ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma sum_Icc_mul_blocks (f : ℕ → ℂ) (G H : ℕ) :
    ∑ n ∈ Icc 1 (G * H), f n =
      ∑ j ∈ range G, ∑ t ∈ Icc 1 H, f (j * H + t) := by
  rw [show Icc 1 (G * H) = Ico 1 (G * H + 1) from by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [sum_range_mul_blocks (fun k => f (1 + k)) G H]
  apply sum_congr rfl
  intro j hj
  rw [show Icc 1 H = Ico 1 (H + 1) from by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega,
    Finset.sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro t ht
  congr 1
  omega

lemma sum_range_shift_eq_sum_Icc (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, f (n + 1) = ∑ n ∈ Icc 1 N, f n := by
  rw [show Icc 1 N = Ico 1 (N + 1) from by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega,
    Finset.sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro n hn
  congr 1
  omega

lemma tendsto_mean_of_shift {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, f (n + 1)) / (N : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f n) / (N : ℂ)) atTop (𝓝 0) := by
  have herr : Tendsto (fun N : ℕ => (f 0 - f N) / (N : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have htwo : Tendsto (fun N : ℕ => (2 : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 2
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) htwo
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (by linarith [hf 0, hf N]))
        (by positivity)
  have hsum : ∀ N : ℕ, ∑ n ∈ range N, f n =
      (∑ n ∈ range N, f (n + 1)) + f 0 - f N := by
    intro N
    have h1 := Finset.sum_range_succ f N
    have h2 := Finset.sum_range_succ' f N
    calc
      ∑ n ∈ range N, f n = ((∑ n ∈ range N, f n) + f N) - f N := by ring
      _ = (∑ n ∈ range (N + 1), f n) - f N := by rw [h1]
      _ = (∑ n ∈ range N, f (n + 1)) + f 0 - f N := by rw [h2]
  simpa only [← add_div, hsum, add_sub, add_zero] using h.add herr

def stonehamKickBlocks {r : ℕ} (c m : Fin r → ℕ) (J : ℕ) : Finset ℕ :=
  insert 0 (univ.biUnion fun i =>
    (Icc 1 (Nat.log 2 (J ^ 2))).image fun k => (m i * c i ^ k - 1) / J)

lemma stonehamKickBlocks_card {r : ℕ} (c m : Fin r → ℕ) (J : ℕ) :
    (stonehamKickBlocks c m J).card ≤ 1 + r * Nat.log 2 (J ^ 2) := by
  unfold stonehamKickBlocks
  calc
    (insert 0 (univ.biUnion fun i =>
        (Icc 1 (Nat.log 2 (J ^ 2))).image fun k => (m i * c i ^ k - 1) / J)).card
        ≤ 1 + (univ.biUnion fun i =>
          (Icc 1 (Nat.log 2 (J ^ 2))).image fun k => (m i * c i ^ k - 1) / J).card :=
      by
        simpa [Nat.add_comm] using
          (card_insert_le (0 : ℕ) (univ.biUnion fun i : Fin r =>
            (Icc 1 (Nat.log 2 (J ^ 2))).image fun k => (m i * c i ^ k - 1) / J))
    _ ≤ 1 + ∑ i ∈ (univ : Finset (Fin r)),
        ((Icc 1 (Nat.log 2 (J ^ 2))).image fun k =>
          (m i * c i ^ k - 1) / J).card := by
      gcongr
      exact card_biUnion_le
    _ ≤ 1 + ∑ _i ∈ (univ : Finset (Fin r)), (Icc 1 (Nat.log 2 (J ^ 2))).card := by
      apply Nat.add_le_add_left
      exact Finset.sum_le_sum fun i hi =>
        @Finset.card_image_le ℕ ℕ (Icc 1 (Nat.log 2 (J ^ 2)))
          (fun k : ℕ => (m i * c i ^ k - 1) / J) inferInstance
    _ = 1 + r * Nat.log 2 (J ^ 2) := by
      simp [Nat.card_Icc]

lemma stonehamK_block_eq {r : ℕ} (c m : Fin r → ℕ) (i : Fin r)
    (J j t : ℕ) (hJ : 1 ≤ J) (hj : j < J)
    (hgood : j ∉ stonehamKickBlocks c m J) (ht : t ∈ Icc 1 J)
    (hc : 2 ≤ c i) (hm : 1 ≤ m i) :
    stonehamK c m i (j * J + t) = stonehamK c m i (j * J) := by
  have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
  have htJ : t ≤ J := (mem_Icc.mp ht).2
  have hend : j * J + t ≤ J ^ 2 := by
    have hj1 : j + 1 ≤ J := by omega
    nlinarith
  have hmono : stonehamK c m i (j * J) ≤ stonehamK c m i (j * J + t) := by
    by_cases hK0 : stonehamK c m i (j * J) = 0
    · simp [hK0]
    · have hK1 : 1 ≤ stonehamK c m i (j * J) := by omega
      apply (le_stonehamK_iff c m i (j * J + t) (stonehamK c m i (j * J)) hc hm hK1).2
      exact ((le_stonehamK_iff c m i (j * J) (stonehamK c m i (j * J)) hc hm hK1).1
        le_rfl).trans (by omega)
  apply le_antisymm
  · by_contra hnot
    have hlt : stonehamK c m i (j * J) < stonehamK c m i (j * J + t) := by omega
    let k := stonehamK c m i (j * J + t)
    have hk1 : 1 ≤ k := by dsimp [k]; omega
    have hkick_end : m i * c i ^ k ≤ j * J + t :=
      (le_stonehamK_iff c m i (j * J + t) k hc hm hk1).1 le_rfl
    have hkick_start : j * J < m i * c i ^ k := by
      by_contra hle
      push_neg at hle
      have hkold := (le_stonehamK_iff c m i (j * J) k hc hm hk1).2 hle
      dsimp [k] at hkold
      omega
    have hpow : 2 ^ k ≤ J ^ 2 := by
      have hc_pow : 2 ^ k ≤ c i ^ k := Nat.pow_le_pow_left hc k
      have hm_mul : c i ^ k ≤ m i * c i ^ k := by
        simpa using Nat.mul_le_mul_right (c i ^ k) hm
      exact hc_pow.trans (hm_mul.trans (hkick_end.trans hend))
    have hklog : k ≤ Nat.log 2 (J ^ 2) :=
      Nat.le_log_of_pow_le (by norm_num) hpow
    have hdiv : (m i * c i ^ k - 1) / J = j := by
      have hupper : m i * c i ^ k ≤ (j + 1) * J := by
        calc
          m i * c i ^ k ≤ j * J + t := hkick_end
          _ ≤ j * J + J := by omega
          _ = (j + 1) * J := by ring
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    apply hgood
    simp only [stonehamKickBlocks, mem_insert, mem_biUnion, mem_univ, true_and,
      mem_image]
    exact Or.inr ⟨i, k, mem_Icc.mpr ⟨hk1, hklog⟩, hdiv⟩
  · exact hmono

def stonehamPrimes (L : ℕ) {r : ℕ} (c : Fin r → ℕ) : Finset ℕ :=
  (L * ∏ i, c i).primeFactors

lemma stonehamPrimes_valid (b L : ℕ) {r : ℕ} (c : Fin r → ℕ)
    (hLb : Nat.Coprime L b) (hcb : ∀ i, Nat.Coprime (c i) b) :
    ∀ q ∈ stonehamPrimes L c, q.Prime ∧ Nat.Coprime q b := by
  intro q hq
  have hcop : Nat.Coprime (L * ∏ i, c i) b :=
    Nat.Coprime.mul_left hLb (Nat.Coprime.prod_left fun i _ => hcb i)
  exact ⟨Nat.prime_of_mem_primeFactors hq,
    Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hq) hcop⟩

lemma stonehamState_den_primes (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (n : ℕ) (hL : L ≠ 0) (hc0 : ∀ i, c i ≠ 0) :
    ∀ q, q.Prime → q ∣ (stonehamState b L c m p n).den →
      q ∈ stonehamPrimes L c := by
  intro q hq hqd
  have hbig0 : L * ∏ i, c i ≠ 0 := by
    exact mul_ne_zero hL (prod_ne_zero_iff.mpr fun i _ => hc0 i)
  apply Nat.mem_primeFactors.mpr
  refine ⟨hq, ?_, hbig0⟩
  rcases prime_dvd_stonehamState_den b L c m p n q hL hc0 hq hqd with hqL | ⟨i, hqc⟩
  · exact Dvd.dvd.mul_right hqL _
  · exact dvd_trans hqc (dvd_trans
      (Finset.dvd_prod_of_mem c (mem_univ i)) (dvd_mul_left _ _))

lemma stonehamState_good_block_bound
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    {ε δ C : ℝ} (hcor : ∀ (M : ℕ), 2 ≤ M →
      (∀ q, q.Prime → q ∣ M → q ∈ stonehamPrimes L c) →
      ∀ (a : ℤ), IsCoprime a (M : ℤ) → ∀ N : ℕ, (M : ℝ) ^ ε ≤ N →
        ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / M)‖ ≤
          C * (M : ℝ) ^ (-δ) * N * (1 + Real.log M))
    (J j : ℕ) (hJ : 1 ≤ J) (hj : j < J)
    (hgood : j ∉ stonehamKickBlocks c m J)
    (hden2 : 2 ≤ (stonehamState b L c m p (j * J)).den)
    (hlen : ((stonehamState b L c m p (j * J)).den : ℝ) ^ ε ≤ J) :
    ‖∑ t ∈ Icc 1 J, ePhase ((stonehamState b L c m p (j * J + t) : ℚ) : ℝ)‖ ≤
      C * ((stonehamState b L c m p (j * J)).den : ℝ) ^ (-δ) * J *
        (1 + Real.log (stonehamState b L c m p (j * J)).den) := by
  let x : ℚ := stonehamState b L c m p (j * J)
  let D : ℕ := x.den
  let A : ℤ := x.num
  have hL0 : L ≠ 0 := by omega
  have hc0 : ∀ i, c i ≠ 0 := fun i => by have := hc i; omega
  have hDP : ∀ q, q.Prime → q ∣ D → q ∈ stonehamPrimes L c := by
    simpa only [D, x] using stonehamState_den_primes b L c m p (j * J) hL0 hc0
  have hAD : IsCoprime A (D : ℤ) := by
    exact Int.isCoprime_iff_gcd_eq_one.2 x.reduced
  have hmain := hcor D (by simpa only [D, x] using hden2) hDP A hAD J
    (by simpa only [D, x] using hlen)
  have hx : (x : ℝ) = (A : ℝ) / D := by
    rw [← Rat.num_div_den x]
    push_cast
    rfl
  refine (le_of_eq ?_).trans hmain
  congr 1
  apply sum_congr rfl
  intro t ht
  have hstate := stonehamState_add_of_K_eq b L c m p (j * J) t hc hm
    (fun i => stonehamK_block_eq c m i J j t hJ hj hgood ht (hc i) (hm i))
  rw [hstate]
  congr 1
  simp only [x, D, A] at hx ⊢
  push_cast
  rw [hx]
  ring

def stonehamCoeffBound {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ) : ℕ :=
  (∏ i, (p i).natAbs) * ∏ i, m i * c i

/-- The only arithmetic input needed by the analytic block argument: the reduced
denominator of the rational orbit state grows at least linearly, up to the fixed
coefficient bound.  Unlike the original proof of this fact, the interface itself does not
require the Stoneham parameters to be pairwise coprime. -/
def StonehamStateDenLinearLower (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) : Prop :=
  ∀ n, n ≤ (stonehamState b L c m p n).den * stonehamCoeffBound c m p

lemma stonehamState_block_den_bounds_of_linearLower
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (J j : ℕ) (hJ : 1 ≤ J) (hj1 : 1 ≤ j) (hj : j < J)
    (hL : L ≠ 0) (hc : ∀ i, 2 ≤ c i)
    (hlower : StonehamStateDenLinearLower b L c m p) :
    let A := stonehamCoeffBound c m p
    J ≤ (stonehamState b L c m p (j * J)).den * A ∧
      (stonehamState b L c m p (j * J)).den ≤ L * (J ^ 2) ^ r := by
  dsimp only
  have hs0 : j * J ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hsN : j * J ≤ J ^ 2 := by nlinarith
  constructor
  · exact (by nlinarith : J ≤ j * J).trans (hlower (j * J))
  · have hc0 : ∀ i, c i ≠ 0 := fun i => by have := hc i; omega
    have hdenDvd := stonehamState_den_dvd b L c m p (j * J) hL hc0
    have hstateDen0 : stonehamStateDen L c m (j * J) ≠ 0 := by
      unfold stonehamStateDen
      exact mul_ne_zero hL (prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hc0 i))
    have hdenle : (stonehamState b L c m p (j * J)).den ≤
        stonehamStateDen L c m (j * J) := Nat.le_of_dvd (Nat.pos_of_ne_zero hstateDen0) hdenDvd
    exact hdenle.trans ((stonehamStateDen_le L c m (j * J) hs0).trans (by
      gcongr))

lemma stonehamState_den_linearLower (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (hb : b ≠ 0) (hL : L ≠ 0)
    (hr : 1 ≤ r)
    (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hcop : Pairwise fun i k => Nat.Coprime (c i) (c k))
    (hp : ∀ i, p i ≠ 0) : StonehamStateDenLinearLower b L c m p := by
  intro n
  have hcross := stonehamState_den_lower_cross b L c m p n hb hL hc hm hcb hcop hp
  by_cases hn : n = 0
  · simp [hn]
  · simpa only [stonehamCoeffBound] using
      (Nat.le_self_pow (by omega : r ≠ 0) n |>.trans hcross)

lemma stonehamState_block_den_bounds (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (J j : ℕ) (hJ : 1 ≤ J) (hj1 : 1 ≤ j) (hj : j < J)
    (hr : 1 ≤ r) (hb : b ≠ 0) (hL : L ≠ 0)
    (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hcop : Pairwise fun i k => Nat.Coprime (c i) (c k))
    (hp : ∀ i, p i ≠ 0) :
    let A := stonehamCoeffBound c m p
    J ≤ (stonehamState b L c m p (j * J)).den * A ∧
      (stonehamState b L c m p (j * J)).den ≤ L * (J ^ 2) ^ r := by
  exact stonehamState_block_den_bounds_of_linearLower b L c m p J j hJ hj1 hj hL hc
    (stonehamState_den_linearLower b L c m p hb hL hr hc hm hcb hcop hp)

lemma stonehamState_block_length (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (J j : ℕ) (hJ : 1 ≤ J) (hLJ : L ≤ J)
    (hupper : (stonehamState b L c m p (j * J)).den ≤ L * (J ^ 2) ^ r) :
    ((stonehamState b L c m p (j * J)).den : ℝ) ^ (1 / (2 * r + 1 : ℝ)) ≤ J := by
  let D := (stonehamState b L c m p (j * J)).den
  let d := 2 * r + 1
  have hDJ : D ≤ J ^ d := by
    dsimp only [D, d]
    calc
      (stonehamState b L c m p (j * J)).den ≤ L * (J ^ 2) ^ r := hupper
      _ ≤ J * (J ^ 2) ^ r := Nat.mul_le_mul_right _ hLJ
      _ = J ^ (2 * r + 1) := by ring
  have hDJR : (D : ℝ) ≤ (J : ℝ) ^ d := by exact_mod_cast hDJ
  have heps : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  calc
    (D : ℝ) ^ (1 / (2 * r + 1 : ℝ)) = (D : ℝ) ^ (1 / (d : ℝ)) := by
      congr 2
      dsimp [d]
      push_cast
      ring
    _ ≤ ((J : ℝ) ^ d) ^ (1 / (d : ℝ)) := Real.rpow_le_rpow (by positivity) hDJR heps
    _ = J := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      have hd0 : (d : ℝ) ≠ 0 := by dsimp [d]; positivity
      rw [show (d : ℝ) * (1 / (d : ℝ)) = 1 by field_simp, Real.rpow_one]

lemma stonehamState_square_bound_of_linearLower
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hp : ∀ i, p i ≠ 0)
    (hlower : StonehamStateDenLinearLower b L c m p)
    {δ C : ℝ} (hδ : 0 < δ)
    (hcor : ∀ (M : ℕ), 2 ≤ M →
      (∀ q, q.Prime → q ∣ M → q ∈ stonehamPrimes L c) →
      ∀ (a : ℤ), IsCoprime a (M : ℤ) → ∀ N : ℕ,
        (M : ℝ) ^ (1 / (2 * r + 1 : ℝ)) ≤ N →
        ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / M)‖ ≤
          C * (M : ℝ) ^ (-δ) * N * (1 + Real.log M))
    (J : ℕ) (hJ : 1 ≤ J) (hAJ : stonehamCoeffBound c m p < J)
    (hLJ : L ≤ J) :
    ‖∑ n ∈ Icc 1 (J ^ 2),
        ePhase ((stonehamState b L c m p n : ℚ) : ℝ)‖ ≤
      (1 + r * Nat.log 2 (J ^ 2)) * J +
        |C| * ((J : ℝ) / stonehamCoeffBound c m p) ^ (-δ) * J ^ 2 *
          (1 + Real.log (L * (J ^ 2) ^ r)) := by
  let A := stonehamCoeffBound c m p
  let U := L * (J ^ 2) ^ r
  let B : ℝ := |C| * ((J : ℝ) / A) ^ (-δ) * J * (1 + Real.log U)
  have hApos : 0 < A := by
    dsimp [A, stonehamCoeffBound]
    apply mul_pos
    · exact prod_pos fun i _ => Int.natAbs_pos.mpr (hp i)
    · exact prod_pos fun i _ => mul_pos (hm i) (by have := hc i; omega)
  have hU1 : 1 ≤ U := by
    dsimp [U]
    have hJpow : 1 ≤ (J ^ 2) ^ r := one_le_pow₀ (one_le_pow₀ hJ)
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Nat.one_le_iff_ne_zero.mp hL) (Nat.one_le_iff_ne_zero.mp hJpow))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  let f : ℕ → ℂ := fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)
  have hf1 : ∀ n, ‖f n‖ = 1 := fun n => norm_ePhase _
  have hblock : ∀ j ∈ range J,
      ‖∑ t ∈ Icc 1 J, f (j * J + t)‖ ≤
        (if j ∈ stonehamKickBlocks c m J then (J : ℝ) else 0) + B := by
    intro j hj
    rw [mem_range] at hj
    by_cases hbad : j ∈ stonehamKickBlocks c m J
    · rw [if_pos hbad]
      have htriv : ‖∑ t ∈ Icc 1 J, f (j * J + t)‖ ≤ J := by
        refine (norm_sum_le _ _).trans ?_
        simp [hf1, Nat.card_Icc]
      linarith
    · rw [if_neg hbad, zero_add]
      have hj1 : 1 ≤ j := by
        by_contra hj0
        have : j = 0 := by omega
        subst j
        exact hbad (by simp [stonehamKickBlocks])
      obtain ⟨hlower, hupper⟩ := stonehamState_block_den_bounds_of_linearLower
        b L c m p J j hJ hj1 hj (by omega) hc hlower
      let D := (stonehamState b L c m p (j * J)).den
      have hden2 : 2 ≤ D := by
        by_contra hd
        have hDone : D = 1 := by have := Rat.den_pos (stonehamState b L c m p (j * J)); omega
        change J ≤ D * A at hlower
        rw [hDone, one_mul] at hlower
        exact (not_lt_of_ge hlower) (by simpa only [A] using hAJ)
      have hlen := stonehamState_block_length b L c m p J j hJ hLJ hupper
      have hraw := stonehamState_good_block_bound b L c m p hb hL hLb hc hm hcb hcor
        J j hJ hj hbad (by simpa only [D] using hden2) hlen
      have hJA : (J : ℝ) / A ≤ D := by
        have hAR : (0 : ℝ) < A := by exact_mod_cast hApos
        apply (div_le_iff₀ hAR).2
        exact_mod_cast hlower
      have hpow : (D : ℝ) ^ (-δ) ≤ ((J : ℝ) / A) ^ (-δ) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hJA (by linarith)
      have hDU : D ≤ U := by simpa only [D, U] using hupper
      have hlog : Real.log D ≤ Real.log U := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hDU)
      have hlogD0 : 0 ≤ 1 + Real.log D := by
        have : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
        linarith [Real.log_nonneg this]
      have hlogU0 : 0 ≤ 1 + Real.log U := by
        have : (1 : ℝ) ≤ U := by exact_mod_cast hU1
        linarith [Real.log_nonneg this]
      have hC0 : 0 ≤ C := by
        have hpos : 0 < (D : ℝ) ^ (-δ) * J * (1 + Real.log D) := by positivity
        nlinarith [norm_nonneg (∑ t ∈ Icc 1 J, f (j * J + t))]
      calc
        ‖∑ t ∈ Icc 1 J, f (j * J + t)‖
            ≤ C * (D : ℝ) ^ (-δ) * J * (1 + Real.log D) := by
              simpa only [f, D] using hraw
        _ ≤ |C| * ((J : ℝ) / A) ^ (-δ) * J * (1 + Real.log U) := by
          gcongr
          exact le_abs_self C
        _ = B := by rfl
  rw [show J ^ 2 = J * J by ring, sum_Icc_mul_blocks]
  refine (norm_sum_le _ _).trans ((sum_le_sum hblock).trans ?_)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hbadcard : ((range J).filter fun j => j ∈ stonehamKickBlocks c m J).card ≤
      1 + r * Nat.log 2 (J ^ 2) := by
    have hsub : ((range J).filter fun j => j ∈ stonehamKickBlocks c m J) ⊆
        stonehamKickBlocks c m J := by
      intro j hj
      exact (mem_filter.mp hj).2
    exact (card_le_card hsub).trans (stonehamKickBlocks_card c m J)
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  have hbadR : (((range J).filter fun j => j ∈ stonehamKickBlocks c m J).card : ℝ) ≤
      1 + r * Nat.log 2 (J ^ 2) := by exact_mod_cast hbadcard
  have hJR : (0 : ℝ) ≤ J := by positivity
  have hfin :
      (((range J).filter fun j => j ∈ stonehamKickBlocks c m J).card : ℝ) * J +
          (J : ℝ) * B ≤
        (1 + r * Nat.log 2 (J ^ 2)) * J +
          |C| * ((J : ℝ) / stonehamCoeffBound c m p) ^ (-δ) * J ^ 2 *
            (1 + Real.log (L * (J ^ 2) ^ r)) := by
    calc
      (((range J).filter fun j => j ∈ stonehamKickBlocks c m J).card : ℝ) * J +
            (J : ℝ) * B
          ≤ (1 + r * Nat.log 2 (J ^ 2) : ℕ) * J + (J : ℝ) * B := by
            gcongr
      _ = (1 + r * Nat.log 2 (J ^ 2)) * J +
          |C| * ((J : ℝ) / stonehamCoeffBound c m p) ^ (-δ) * J ^ 2 *
            (1 + Real.log (L * (J ^ 2) ^ r)) := by
        dsimp only [B, U, A]
        push_cast
        ring
  simpa [pow_two] using hfin

/-- The original pairwise-coprime square bound is recovered by supplying the standard
denominator-growth proof to the arithmetic-independent analytic engine. -/
lemma stonehamState_square_bound
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hcop : Pairwise fun i k => Nat.Coprime (c i) (c k))
    (hp : ∀ i, p i ≠ 0) {δ C : ℝ} (hδ : 0 < δ)
    (hcor : ∀ (M : ℕ), 2 ≤ M →
      (∀ q, q.Prime → q ∣ M → q ∈ stonehamPrimes L c) →
      ∀ (a : ℤ), IsCoprime a (M : ℤ) → ∀ N : ℕ,
        (M : ℝ) ^ (1 / (2 * r + 1 : ℝ)) ≤ N →
        ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / M)‖ ≤
          C * (M : ℝ) ^ (-δ) * N * (1 + Real.log M))
    (J : ℕ) (hJ : 1 ≤ J) (hAJ : stonehamCoeffBound c m p < J)
    (hLJ : L ≤ J) :
    ‖∑ n ∈ Icc 1 (J ^ 2),
        ePhase ((stonehamState b L c m p n : ℚ) : ℝ)‖ ≤
      (1 + r * Nat.log 2 (J ^ 2)) * J +
        |C| * ((J : ℝ) / stonehamCoeffBound c m p) ^ (-δ) * J ^ 2 *
          (1 + Real.log (L * (J ^ 2) ^ r)) := by
  exact stonehamState_square_bound_of_linearLower b L c m p hb hL hLb hr hc hm hcb hp
    (stonehamState_den_linearLower b L c m p (by omega) (by omega) hr hc hm hcb hcop hp)
    hδ hcor J hJ hAJ hLJ

lemma natLog_le_real (n : ℕ) : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have h3 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h4 : (0 : ℝ) ≤ (Nat.log 2 n : ℕ) := by positivity
  nlinarith

lemma tendsto_natLog_square_div (r : ℕ) :
    Tendsto (fun J : ℕ => ((1 + r * Nat.log 2 (J ^ 2) : ℕ) : ℝ) / J)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun J : ℕ => (1 : ℝ) / J) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlog : Tendsto (fun J : ℕ => Real.log J / (J : ℝ)) atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun J : ℕ =>
      (1 : ℝ) / J + (4 * r : ℝ) * (Real.log J / J)) atTop (𝓝 0) := by
    simpa using hinv.add (hlog.const_mul (4 * (r : ℝ)))
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 1] with J hJ
    positivity
  · filter_upwards [eventually_ge_atTop 1] with J hJ
    have hJR : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
    have hnat := natLog_le_real (J ^ 2)
    have hlogpow : Real.log ((J ^ 2 : ℕ) : ℝ) = 2 * Real.log J := by
      push_cast
      rw [Real.log_pow]
      norm_num
    rw [hlogpow] at hnat
    have heq : (1 : ℝ) / J + (4 * r : ℝ) * (Real.log J / J) =
        (1 + 4 * (r : ℝ) * Real.log J) / J := by ring
    rw [heq]
    apply (div_le_div_iff₀ hJR hJR).2
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hnat (show (0 : ℝ) ≤ r by positivity)]

lemma tendsto_stoneham_analytic_rate (r L A : ℕ) (C δ : ℝ)
    (hL : 1 ≤ L) (hA : 1 ≤ A) (hδ : 0 < δ) :
    Tendsto (fun J : ℕ =>
      |C| * ((J : ℝ) / A) ^ (-δ) * (1 + Real.log (L * (J ^ 2) ^ r)))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun J : ℕ => (J : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hlogpow : Tendsto (fun J : ℕ => Real.log J / (J : ℝ) ^ δ) atTop (𝓝 0) :=
    isLittleO_log_rpow_atTop hδ |>.tendsto_div_nhds_zero |>.comp
      tendsto_natCast_atTop_atTop
  let K : ℝ := |C| / (A : ℝ) ^ (-δ)
  have hmodel : Tendsto (fun J : ℕ => K *
      ((1 + Real.log L) * (J : ℝ) ^ (-δ) +
        (2 * r : ℝ) * (Real.log J / (J : ℝ) ^ δ))) atTop (𝓝 0) := by
    have h1 := hpow.const_mul (1 + Real.log L)
    have h2 := hlogpow.const_mul (2 * r : ℝ)
    simpa using (h1.add h2).const_mul K
  apply hmodel.congr'
  filter_upwards [eventually_ge_atTop 1] with J hJ
  have hJR : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hAR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hLR : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hlogeq : Real.log ((L : ℝ) * ((J : ℝ) ^ 2) ^ r) =
      Real.log L + 2 * r * Real.log J := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  rw [hlogeq, Real.div_rpow hJR.le hAR.le]
  dsimp only [K]
  rw [Real.rpow_neg hJR.le]
  have hJpow0 : (J : ℝ) ^ δ ≠ 0 := (Real.rpow_pos_of_pos hJR δ).ne'
  have hAneg0 : (A : ℝ) ^ (-δ) ≠ 0 := (Real.rpow_pos_of_pos hAR (-δ)).ne'
  field_simp [hJpow0, hAneg0]
  ring

lemma stonehamState_square_mean_tendsto_of_linearLower
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hp : ∀ i, p i ≠ 0)
    (hlower : StonehamStateDenLinearLower b L c m p) :
    Tendsto (fun J : ℕ =>
      (∑ n ∈ Icc 1 (J ^ 2), ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) /
        ((J ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
  let P := stonehamPrimes L c
  let ε : ℝ := 1 / (2 * r + 1 : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hP : ∀ q ∈ P, q.Prime ∧ Nat.Coprime q b := by
    simpa only [P] using stonehamPrimes_valid b L c hLb hcb
  obtain ⟨δ, C, hδ, hcor⟩ := hV b hb P hP ε hε
  let A := stonehamCoeffBound c m p
  have hA : 1 ≤ A := by
    dsimp [A, stonehamCoeffBound]
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero
      (prod_ne_zero_iff.mpr fun i _ => Int.natAbs_ne_zero.mpr (hp i))
      (prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (by have := hm i; omega)
        (by have := hc i; omega))
  have hrate : Tendsto (fun J : ℕ =>
      ((1 + r * Nat.log 2 (J ^ 2) : ℕ) : ℝ) / J +
        |C| * ((J : ℝ) / A) ^ (-δ) * (1 + Real.log (L * (J ^ 2) ^ r)))
      atTop (𝓝 0) := by
    simpa only [zero_add] using (tendsto_natLog_square_div r).add
      (tendsto_stoneham_analytic_rate r L A C δ hL hA hδ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hrate
  filter_upwards [eventually_ge_atTop (max 1 (max L (A + 1)))] with J hJlarge
  have hJ : 1 ≤ J := le_trans (le_max_left _ _) hJlarge
  have hLJ : L ≤ J := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hJlarge
  have hAJ : A < J := by
    have : A + 1 ≤ J := le_trans (le_max_right L (A + 1))
      (le_trans (le_max_right 1 (max L (A + 1))) hJlarge)
    omega
  have hs := stonehamState_square_bound_of_linearLower
    b L c m p hb hL hLb hr hc hm hcb hp hlower hδ
    (by simpa only [P, ε] using hcor) J hJ (by simpa only [A] using hAJ) hLJ
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  rw [norm_div, Complex.norm_natCast]
  push_cast
  calc
    ‖∑ n ∈ Icc 1 (J ^ 2), ePhase ((stonehamState b L c m p n : ℚ) : ℝ)‖ /
          (J : ℝ) ^ 2
        ≤ ((1 + (r : ℝ) * (Nat.log 2 (J ^ 2) : ℝ)) * J +
            |C| * ((J : ℝ) / A) ^ (-δ) * J ^ 2 *
              (1 + Real.log (L * (J ^ 2) ^ r))) / (J : ℝ) ^ 2 := by
          gcongr
    _ = (1 + (r : ℝ) * (Nat.log 2 (J ^ 2) : ℝ)) / J +
        |C| * ((J : ℝ) / A) ^ (-δ) * (1 + Real.log (L * (J ^ 2) ^ r)) := by
      push_cast
      field_simp

lemma stonehamState_square_mean_tendsto
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hcop : Pairwise fun i k => Nat.Coprime (c i) (c k))
    (hp : ∀ i, p i ≠ 0) :
    Tendsto (fun J : ℕ =>
      (∑ n ∈ Icc 1 (J ^ 2), ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) /
        ((J ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
  exact stonehamState_square_mean_tendsto_of_linearLower hV b L c m p hb hL hLb hr hc hm hcb hp
    (stonehamState_den_linearLower b L c m p (by omega) (by omega) hr hc hm hcb hcop hp)

lemma stonehamState_mean_tendsto_of_linearLower
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hp : ∀ i, p i ≠ 0)
    (hlower : StonehamStateDenLinearLower b L c m p) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) /
        (N : ℂ)) atTop (𝓝 0) := by
  let f : ℕ → ℂ := fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)
  let z : ℕ → ℂ := fun n => f (n + 1)
  have hsq : Tendsto (fun J : ℕ =>
      (∑ n ∈ range (J ^ 2), z n) / ((J ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
    convert stonehamState_square_mean_tendsto_of_linearLower
      hV b L c m p hb hL hLb hr hc hm hcb hp hlower using 1
    funext J
    simp only [z, f]
    rw [sum_range_shift_eq_sum_Icc
      (fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) (J ^ 2)]
  have hz : ∀ n, ‖z n‖ ≤ 1 := fun n => by simp only [z, f, norm_ePhase, le_refl]
  have hall := DecayAeNormal.tendsto_of_tendsto_sq z hz hsq
  exact tendsto_mean_of_shift (fun n => by simp only [f, norm_ePhase, le_refl]) hall

lemma stonehamState_mean_tendsto
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hcop : Pairwise fun i k => Nat.Coprime (c i) (c k))
    (hp : ∀ i, p i ≠ 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) /
        (N : ℂ)) atTop (𝓝 0) := by
  exact stonehamState_mean_tendsto_of_linearLower hV b L c m p hb hL hLb hr hc hm hcb hp
    (stonehamState_den_linearLower b L c m p (by omega) (by omega) hr hc hm hcb hcop hp)

lemma stonehamCombination_phase_error_tendsto
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i) :
    Tendsto (fun n : ℕ =>
      ePhase ((b : ℝ) ^ n * ((1 / (L : ℝ)) *
        ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i))) -
      ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := 4 * Real.pi * ∑ i, |(p i : ℝ)| * ((m i * c i : ℕ) : ℝ)
  have hrate : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hrate
  filter_upwards [eventually_ge_atTop 1] with n hn
  calc
    ‖ePhase ((b : ℝ) ^ n * ((1 / (L : ℝ)) *
          ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i))) -
        ePhase ((stonehamState b L c m p n : ℚ) : ℝ)‖
        ≤ 4 * Real.pi *
          |(b : ℝ) ^ n * ((1 / (L : ℝ)) *
              ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) -
            (stonehamState b L c m p n : ℝ)| := norm_ePhase_sub _ _
    _ ≤ 4 * Real.pi *
        ((∑ i, |(p i : ℝ)| * ((m i * c i : ℕ) : ℝ)) / n) := by
      gcongr
      exact stonehamCombination_approx b L c m p n hb hL hc hm hn
    _ = C / n := by simp only [C]; ring

lemma stonehamCombination_mean_tendsto_of_linearLower
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hp : ∀ i, p i ≠ 0)
    (hlower : StonehamStateDenLinearLower b L c m p) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((b : ℝ) ^ n * ((1 / (L : ℝ)) *
        ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)))) / (N : ℂ))
      atTop (𝓝 0) := by
  let a : ℕ → ℂ := fun n => ePhase ((b : ℝ) ^ n * ((1 / (L : ℝ)) *
    ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)))
  let s : ℕ → ℂ := fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)
  have hs : Tendsto (fun N : ℕ => (∑ n ∈ range N, s n) / (N : ℂ))
      atTop (𝓝 0) := by
    simpa only [s] using
      stonehamState_mean_tendsto_of_linearLower
        hV b L c m p hb hL hLb hr hc hm hcb hp hlower
  have he : Tendsto (fun n : ℕ => a n - s n) atTop (𝓝 0) := by
    simpa only [a, s] using
      stonehamCombination_phase_error_tendsto b L c m p hb hL hc hm
  have hemean : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (a n - s n)) / (N : ℂ)) atTop (𝓝 0) := by
    convert he.cesaro_smul using 1
    · funext N
      simp only [Complex.real_smul, div_eq_mul_inv]
      rw [show (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by
        simpa using (Complex.ofReal_inv (N : ℝ)).symm]
      ring
  convert hs.add hemean using 1
  · funext N
    simp only [a, s, Finset.sum_sub_distrib]
    ring
  · simp

lemma stonehamCombination_mean_tendsto
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hcop : Pairwise fun i k => Nat.Coprime (c i) (c k))
    (hp : ∀ i, p i ≠ 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((b : ℝ) ^ n * ((1 / (L : ℝ)) *
        ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)))) / (N : ℂ))
      atTop (𝓝 0) := by
  exact stonehamCombination_mean_tendsto_of_linearLower
    hV b L c m p hb hL hLb hr hc hm hcb hp
      (stonehamState_den_linearLower b L c m p (by omega) (by omega) hr hc hm hcb hcop hp)

lemma ePhase_orbit (b : ℕ) (x : ℝ) (h : ℤ) (n : ℕ) :
    ePhase ((h : ℝ) * orbit b x n) =
      ePhase ((h : ℝ) * ((b : ℝ) ^ n * x)) := by
  have e : (h : ℝ) * orbit b x n = (h : ℝ) * ((b : ℝ) ^ n * x) +
      ((-(h * ⌊x * (b : ℝ) ^ n⌋) : ℤ) : ℝ) := by
    rw [orbit, Int.fract]
    push_cast
    ring
  rw [e, ePhase_add_int]

lemma isNormal_stonehamCombination_int_nonzero
    (hV : VandeheyThm51) (b : ℕ) (hb : 2 ≤ b) {r : ℕ}
    (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i)
    (hr : 1 ≤ r) (hp : ∀ i, p i ≠ 0) :
    IsNormal b (∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) := by
  let x : ℝ := ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (orbit_mem_Ico b _) ?_
  intro h hh
  have hp' : ∀ i, h * p i ≠ 0 := fun i => mul_ne_zero hh (hp i)
  have hmean := stonehamCombination_mean_tendsto
    (vandeheyCor12_of_thm51 hV) b 1 c m (fun i => h * p i) hb (by omega)
      (by simp) hr hc hm hcb hcop hp'
  have heq : fourierMean (orbit b x) h = fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((h : ℝ) * orbit b x n)) / (N : ℂ) := by
    funext N
    rw [fourierMean]
    congr 1
    apply sum_congr rfl
    intro n hn
    rw [ePhase]
    congr 1
    push_cast
    ring
  rw [heq]
  convert hmean using 1
  funext N
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [ePhase_orbit]
  congr 1
  dsimp only [x]
  push_cast
  norm_num
  calc
    (h : ℝ) * ((b : ℝ) ^ n * ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) =
        (b : ℝ) ^ n * ((h : ℝ) *
          ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) := by ring
    _ = (b : ℝ) ^ n *
        ∑ i, (h : ℝ) * (p i : ℝ) * stonehamAlpha (b ^ m i) (c i) := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]

lemma isNormal_stonehamCombination_int
    (hV : VandeheyThm51) (b : ℕ) (hb : 2 ≤ b) {r : ℕ}
    (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i)
    (hp : p ≠ 0) :
    IsNormal b (∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) := by
  classical
  let S : Finset (Fin r) := univ.filter fun i => p i ≠ 0
  let R : ℕ := Fintype.card S
  let e : Fin R ≃ S := (Fintype.equivFin S).symm
  let c' : Fin R → ℕ := fun j => c (e j).1
  let m' : Fin R → ℕ := fun j => m (e j).1
  let p' : Fin R → ℤ := fun j => p (e j).1
  have hSnonempty : Nonempty S := by
    by_contra hempty
    apply hp
    funext i
    by_contra hi
    have hip : p i ≠ 0 := by simpa using hi
    have his : i ∈ S := by
      dsimp only [S]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hip⟩
    exact hempty ⟨i, his⟩
  have hRpos : 1 ≤ R := by
    dsimp only [R]
    exact Fintype.card_pos_iff.mpr hSnonempty
  have hc' : ∀ j, 2 ≤ c' j := fun j => hc (e j).1
  have hm' : ∀ j, 1 ≤ m' j := fun j => hm (e j).1
  have hcb' : ∀ j, Nat.Coprime (c' j) b := fun j => hcb (e j).1
  have hp' : ∀ j, p' j ≠ 0 := fun j => by
    have hj := (e j).property
    simpa only [S, mem_filter, mem_univ, true_and, p'] using hj
  have hcop' : Pairwise fun i j => Nat.Coprime (c' i) (c' j) := by
    intro i j hij
    apply hcop
    intro heq
    apply hij
    apply e.injective
    exact Subtype.ext heq
  have hsum : (∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) =
      ∑ j, (p' j : ℝ) * stonehamAlpha (b ^ m' j) (c' j) := by
    let f : Fin r → ℝ := fun i => (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)
    calc
      ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i) = ∑ i ∈ S, f i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i hi hiS
        have hpi : p i = 0 := by
          simpa only [S, mem_filter, mem_univ, true_and, not_ne_iff] using hiS
        simp only [f, hpi, Int.cast_zero, zero_mul]
      _ = ∑ s : S, f s.1 := by
        exact (Finset.sum_coe_sort S f).symm
      _ = ∑ j : Fin R, f (e j).1 :=
        (Equiv.sum_comp e (fun s : S => f s.1)).symm
      _ = ∑ j, (p' j : ℝ) * stonehamAlpha (b ^ m' j) (c' j) := by rfl
  rw [hsum]
  exact isNormal_stonehamCombination_int_nonzero
    hV b hb c' m' p' hc' hcop' hcb' hm' hRpos hp'

lemma isNormal_stonehamCombination_rat
    (hV : VandeheyThm51) (b : ℕ) (hb : 2 ≤ b) {r : ℕ}
    (c m : Fin r → ℕ) (q : Fin r → ℚ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i)
    (hq : q ≠ 0) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (c i)) := by
  classical
  let D : ℕ := ∏ i, (q i).den
  let p : Fin r → ℤ := fun i => (D / (q i).den : ℕ) * (q i).num
  have hDpos : 0 < D := by
    dsimp only [D]
    exact Finset.prod_pos fun i _ => (q i).pos
  have hden : ∀ i, (q i).den ∣ D := fun i => by
    dsimp only [D]
    exact Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
  have hpq : ∀ i, (p i : ℝ) = (D : ℝ) * (q i : ℝ) := by
    intro i
    have hmul := Nat.div_mul_cancel (hden i)
    have hmulR : ((D / (q i).den : ℕ) : ℝ) * (q i).den = D := by
      exact_mod_cast hmul
    dsimp only [p]
    rw [Rat.cast_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hdenR : ((q i).den : ℝ) ≠ 0 := by positivity
    field_simp [hdenR]
    linear_combination ((q i).num : ℝ) * hmulR
  have hp : p ≠ 0 := by
    intro hp0
    apply hq
    funext i
    have hpi : p i = 0 := congrFun hp0 i
    have hqiR : (q i : ℝ) = 0 := by
      have hi := hpq i
      rw [hpi, Int.cast_zero] at hi
      exact (mul_eq_zero.mp hi.symm).resolve_left (by positivity)
    exact_mod_cast hqiR
  let x : ℝ := ∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (c i)
  have hscaled : (∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)) =
      (D : ℝ) * x := by
    dsimp only [x]
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [hpq i]
    ring
  have hn : IsNormal b ((D : ℝ) * x) := by
    rw [← hscaled]
    exact isNormal_stonehamCombination_int hV b hb c m p hc hcop hcb hm hp
  let a : ℚ := 1 / (D : ℚ)
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact one_div_ne_zero (by exact_mod_cast hDpos.ne')
  have hout := isNormal_rat_mul_add b hb ((D : ℝ) * x) a 0 ha hn
  have hDR : (D : ℝ) ≠ 0 := by positivity
  convert hout using 1
  dsimp only [a, x]
  push_cast
  field_simp
  ring


/-- **Theorem A.**  Pairwise-coprime Stoneham families: every nonzero rational combination is
normal. -/
theorem isNormal_stonehamCombination (hV : VandeheyThm51)
    (b : ℕ) (hb : 2 ≤ b) {r : ℕ} (c m : Fin r → ℕ) (q : Fin r → ℚ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i) (hq : q ≠ 0) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (c i)) := by
  exact isNormal_stonehamCombination_rat hV b hb c m q hc hcop hcb hm hq

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
