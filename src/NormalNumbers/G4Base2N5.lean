/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2TTHyp
import NormalNumbers.G4Base2Rough
import NormalNumbers.G4Base2Mertens

/-!
# N5 proved: TT's hypothesis (3.1) for a bin indicator

* `binIndR_eq`: inclusion–exclusion over the `I`-products `≤ 2N` (`prodLe`).
* `abs_card_Ioc_mod_dvd_sub_le`: CRT count of `n ≡ a (q)`, `d ∣ n` in `(A, B]`.
* `abs_apSum_sub_le_small` (`q` below every prime of `I`): error `≤ 2·#prodLe I (2N)`, then the
  rough count `card_prodLe_le'` gives `≪ N / log X`.
* `abs_apSum_sub_le_large` (`q > Y ≥ X^{1/101}`): trivial bound `≪ N/q`, with `|δ| ≤ e⁵`.
* `binInd_ap_mean` with `C₅ = 10⁶`, `X₀ = exp 2828000`.
-/
open Finset
namespace NormalNumbers.G4.Base2

/-- Residue-class count in `(A, B]`: within `1` of `(B − A)/m`. -/
lemma abs_card_Ioc_modEq_sub_le {A B m : ℕ} (hAB : A ≤ B) (hm : 0 < m) (s : ℕ) :
    |(((Ioc A B).filter (fun n => n ≡ s [MOD m])).card : ℝ) - ((B : ℝ) - A) / m| ≤ 1 := by
  have h := Nat.Ioc_filter_modEq_card A B hm s
  set u : ℚ := ((B : ℚ) - s) / m
  set w : ℚ := ((A : ℚ) - s) / m
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have huw : w ≤ u := by
    simp only [u, w]; gcongr
  have hfl : ⌊w⌋ ≤ ⌊u⌋ := Int.floor_le_floor huw
  rw [max_eq_left (by omega)] at h
  have hc : (((Ioc A B).filter (fun n => n ≡ s [MOD m])).card : ℝ) = ((⌊u⌋ : ℚ) : ℝ) - ((⌊w⌋ : ℚ) : ℝ) := by
    have : ((((Ioc A B).filter (fun n => n ≡ s [MOD m])).card : ℤ) : ℝ) = ((⌊u⌋ - ⌊w⌋ : ℤ) : ℝ) := by
      rw [h]
    push_cast at this ⊢; exact this
  have cast : ∀ r : ℚ, ∀ k : ℤ, ((k : ℚ) ≤ r → ((k : ℚ) : ℝ) ≤ (r : ℝ)) ∧ (r < k + 1 → (r : ℝ) < ((k : ℚ) : ℝ) + 1) :=
    fun r k => ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  have h1 := (cast u ⌊u⌋).1 (Int.floor_le u); have h2 := (cast u ⌊u⌋).2 (Int.lt_floor_add_one u)
  have h3 := (cast w ⌊w⌋).1 (Int.floor_le w); have h4 := (cast w ⌊w⌋).2 (Int.lt_floor_add_one w)
  have e : (u : ℝ) - (w : ℝ) = ((B : ℝ) - A) / m := by simp only [u, w]; push_cast; ring
  rw [hc, abs_le]; constructor <;> linarith

/-- CRT count: `n ≡ a (q)` and `d ∣ n` in `(A, B]`, for coprime `q, d`. -/
lemma abs_card_Ioc_mod_dvd_sub_le {A B q d : ℕ} (hAB : A ≤ B) (hq : 0 < q) (hd : 0 < d)
    (hcop : q.Coprime d) (a : ℕ) :
    |(((Ioc A B).filter (fun n => n % q = a % q ∧ d ∣ n)).card : ℝ) - ((B : ℝ) - A) / (q * d)|
      ≤ 1 := by
  obtain ⟨s, hs1, hs2⟩ := Nat.chineseRemainder hcop a 0
  have hf : (Ioc A B).filter (fun n => n % q = a % q ∧ d ∣ n)
      = (Ioc A B).filter (fun n => n ≡ s [MOD q * d]) := by
    refine filter_congr fun n _ => ?_
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop, ← Nat.modEq_zero_iff_dvd]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(show n ≡ a [MOD q] from h1).trans hs1.symm, h2.trans hs2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨show n ≡ a [MOD q] from h1.trans hs1, h2.trans hs2⟩
  rw [hf]
  have := abs_card_Ioc_modEq_sub_le hAB (Nat.mul_pos hq hd) s
  push_cast at this; exact this

lemma prod_dvd_iff {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (n : ℕ) :
    (∏ p ∈ T, p) ∣ n ↔ ∀ p ∈ T, p ∣ n :=
  ⟨fun h p hp => (dvd_prod_of_mem _ hp).trans h,
   fun h => prod_primes_dvd n (fun p hp => (hT p hp).prime) h⟩

/-- **Inclusion–exclusion** for the bin indicator, truncated at `x ≥ n`. -/
lemma binIndR_eq {I : Finset ℕ} (hI : ∀ p ∈ I, p.Prime) {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hnx : (n : ℝ) ≤ x) :
    (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1)
      = ∑ T ∈ prodLe I x, (-1 : ℝ) ^ T.card * (if (∏ p ∈ T, p) ∣ n then 1 else 0) := by
  have h1 : (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1)
      = ∏ p ∈ I, (1 + (-(if p ∣ n then (1 : ℝ) else 0))) := by
    split_ifs with h
    · obtain ⟨p, hp, hpn⟩ := h
      exact (prod_eq_zero hp (by simp [hpn])).symm
    · push Not at h
      exact (prod_eq_one fun p hp => by simp [h p hp]).symm
  rw [h1, prod_one_add]
  unfold prodLe
  rw [sum_filter]
  refine sum_congr rfl fun T hT => ?_
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hI p (mem_powerset.1 hT hp)
  have e : ∏ p ∈ T, (-(if p ∣ n then (1 : ℝ) else 0))
      = (-1 : ℝ) ^ T.card * (if (∏ p ∈ T, p) ∣ n then 1 else 0) := by
    rw [prod_neg, prod_boole]; simp only [prod_dvd_iff hTp]
  rw [e]
  by_cases hx : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ x
  · rw [if_pos hx]
  · rw [if_neg hx, if_neg, mul_zero]
    intro hd
    have := Nat.le_of_dvd hn hd
    have : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    exact hx (by linarith)

lemma floor_window {N : ℝ} (hN : 1 ≤ N) :
    ⌊N⌋₊ ≤ ⌊2 * N⌋₊ ∧ |((⌊2 * N⌋₊ : ℝ) - ⌊N⌋₊) - N| ≤ 1 := by
  refine ⟨Nat.floor_le_floor (by linarith), ?_⟩
  have h1 := Nat.floor_le (by linarith : (0 : ℝ) ≤ N)
  have h2 := Nat.lt_floor_add_one N
  have h3 := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * N)
  have h4 := Nat.lt_floor_add_one (2 * N)
  rw [abs_le]; constructor <;> linarith

/-- **N5, small modulus.**  For `q` below every prime of `I`, the AP sum of the bin indicator
is within `2·#prodLe I (2N)` of `(N/q)·δ_I(N)`. -/
lemma abs_apSum_sub_le_small {I : Finset ℕ} (hI : ∀ p ∈ I, p.Prime) {q : ℕ} (hq : 0 < q)
    (hqI : ∀ p ∈ I, q < p) {N : ℝ} (hN : 1 ≤ N) (a : ℕ) :
    |∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q),
        (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1) - N / q * binDelta I N|
      ≤ 2 * (prodLe I (2 * N)).card := by
  obtain ⟨hAB, hBA⟩ := floor_window hN
  set A := ⌊N⌋₊; set B := ⌊2 * N⌋₊
  set P := (Ioc A B).filter (fun n => n % q = a % q)
  have hB : (B : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
  set F := prodLe I (2 * N)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  -- expand the indicator
  have hexp : ∑ n ∈ P, (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1)
      = ∑ T ∈ F, (-1 : ℝ) ^ T.card * ((Ioc A B).filter (fun n => n % q = a % q ∧ (∏ p ∈ T, p) ∣ n)).card := by
    rw [sum_congr rfl fun n hn => binIndR_eq hI (n := n) (x := 2 * N) ?_ ?_]
    · rw [sum_comm]
      refine sum_congr rfl fun T _ => ?_
      rw [← mul_sum, sum_boole, filter_filter]
    · have := (mem_Ioc.1 (mem_filter.1 hn).1).1; omega
    · have := (mem_Ioc.1 (mem_filter.1 hn).1).2
      have : (n : ℝ) ≤ B := by exact_mod_cast this
      linarith
  have hδ : N / q * binDelta I N = ∑ T ∈ F, (-1 : ℝ) ^ T.card * (N / (q * ((∏ p ∈ T, p : ℕ) : ℝ))) := by
    unfold binDelta; rw [mul_sum]
    refine sum_congr rfl fun T _ => ?_
    field_simp
  rw [hexp, hδ, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [show (2 : ℝ) * (F.card : ℝ) = ∑ _T ∈ F, (2 : ℝ) by simp [mul_comm]]
  refine sum_le_sum fun T hT => ?_
  simp only [F, prodLe, mem_filter, mem_powerset] at hT
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hI p (hT.1 hp)
  have hd : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hTp p hp).pos
  have hdr : (1 : ℝ) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast hd
  have hcop : q.Coprime (∏ p ∈ T, p) := Nat.Coprime.prod_right fun p hp =>
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hTp p hp)).2
      fun h => absurd (Nat.le_of_dvd hq h) (not_le.2 (hqI p (hT.1 hp)))))
  have hc := abs_card_Ioc_mod_dvd_sub_le hAB hq hd hcop a
  rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hqd : (1 : ℝ) ≤ q * ((∏ p ∈ T, p : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hdiff : |((B : ℝ) - A) / (q * ((∏ p ∈ T, p : ℕ) : ℝ)) - N / (q * ((∏ p ∈ T, p : ℕ) : ℝ))| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < q * ((∏ p ∈ T, p : ℕ) : ℝ)), div_le_one (by linarith)]
    exact hBA.trans hqd
  calc _ ≤ |(((Ioc A B).filter (fun n => n % q = a % q ∧ (∏ p ∈ T, p) ∣ n)).card : ℝ)
          - ((B : ℝ) - A) / (q * ((∏ p ∈ T, p : ℕ) : ℝ))|
        + |((B : ℝ) - A) / (q * ((∏ p ∈ T, p : ℕ) : ℝ)) - N / (q * ((∏ p ∈ T, p : ℕ) : ℝ))| :=
          abs_sub_le _ _ _
    _ ≤ 2 := by linarith

lemma abs_binDelta_le_sum (I : Finset ℕ) (N : ℝ) :
    |binDelta I N| ≤ ∑ T ∈ prodLe I (2 * N), ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹ := by
  unfold binDelta
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  unfold prodLe
  refine sum_congr rfl fun T _ => ?_
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, one_div, Nat.abs_cast]

/-- **N5, large modulus.**  Trivial bound. -/
lemma abs_apSum_sub_le_large (I : Finset ℕ) {q : ℕ} (hq : 0 < q) {N : ℝ} (hN : 1 ≤ N) (a : ℕ) :
    |∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q),
        (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1) - N / q * binDelta I N|
      ≤ (N + 1) / q + 1 + N / q * ∑ T ∈ prodLe I (2 * N), ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹ := by
  obtain ⟨hAB, hBA⟩ := floor_window hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hc := abs_card_Ioc_modEq_sub_le hAB hq a
  have hP : ((Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q))
      = (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n ≡ a [MOD q]) := rfl
  have h1 : |∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q),
      (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1)|
      ≤ (((Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q)).card : ℝ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_le_sum fun n _ => ?_
    split_ifs <;> simp
  rw [hP] at h1
  have h2 : (((Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n ≡ a [MOD q])).card : ℝ) ≤ (N + 1) / q + 1 := by
    rw [abs_le] at hc hBA
    have : ((⌊2 * N⌋₊ : ℝ) - ⌊N⌋₊) / q ≤ (N + 1) / q := by gcongr; linarith
    linarith
  have h3 : |N / q * binDelta I N| ≤ N / q * ∑ T ∈ prodLe I (2 * N), ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_binDelta_le_sum I N) (by positivity)
  rw [hP]
  have := abs_sub (∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n ≡ a [MOD q]),
    (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1)) (N / q * binDelta I N)
  linarith

lemma exp_five_lt : Real.exp 5 < 149 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := by gcongr
    _ < 149 := by norm_num

lemma log_four_lt : Real.log 4 < 1.4 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

lemma binInd_eq_ofReal (I : Finset ℕ) (n : ℕ) :
    binInd I n = (((if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1) : ℝ) : ℂ) := by
  unfold binInd; split_ifs <;> simp

/-- **N5.**  TT's hypothesis (3.1) for bin indicators, with `L = log X / C₅`. -/
theorem binInd_ap_mean : ∃ C₅ X₀ : ℝ, 0 < C₅ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ Y : ℝ,
    X ^ ((1 : ℝ) / 101) ≤ Y → ∀ I : Finset ℕ, (∀ p ∈ I, p.Prime ∧ Y < p) →
    ∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
      ‖(∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), binInd I n)
          - (((N / q) * binDelta I N : ℝ) : ℂ)‖ ≤ N / (Real.log X / C₅) := by
  refine ⟨10 ^ 6, Real.exp 2828000, by norm_num, fun X hX Y hY I hI N hN1 hN2 a q hq => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  set LX := Real.log X with hLX
  have hLX0 : 2828000 ≤ LX := by
    have := Real.log_le_log (Real.exp_pos _) hX; rwa [Real.log_exp] at this
  have hLXpos : 0 < LX := by linarith
  -- `log X ≤ 101 X^{1/101}` and `log X ≤ 2.5 X^{0.4}`
  have hl1 : LX ≤ X ^ ((1 : ℝ) / 101) / (1 / 101) := Real.log_le_rpow_div hX0.le (by norm_num)
  have hl2 : LX ≤ X ^ (0.4 : ℝ) / 0.4 := Real.log_le_rpow_div hX0.le (by norm_num)
  have hXr0 : 0 < X ^ ((1 : ℝ) / 101) := Real.rpow_pos_of_pos hX0 _
  have hY0 : 0 < Y := lt_of_lt_of_le hXr0 hY
  have hLY : LX / 101 ≤ Real.log Y := by
    have := Real.log_le_log hXr0 hY
    rw [Real.log_rpow hX0] at this; linarith
  have hNLX : LX ≤ 2.5 * N := by
    have : X ^ (0.4 : ℝ) / 0.4 = 2.5 * X ^ (0.4 : ℝ) := by ring
    linarith
  have hN : 1 ≤ N := by linarith
  have hYbig : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Real.log Y := by linarith
    by_contra h; push Not at h
    have := Real.log_nonpos hY0.le h.le; linarith
  -- the natural cut `Y' = ⌊Y⌋`
  set Y' := ⌊Y⌋₊ with hY'
  have hY'le : (Y' : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hY'pos : (0 : ℝ) < Y' := by have := half_le_floor hYbig; linarith
  have hLY' : Real.log Y - Real.log 2 ≤ Real.log Y' := by
    have := Real.log_le_log (by linarith) (half_le_floor hYbig)
    rwa [Real.log_div hY0.ne' (by norm_num)] at this
  have hl2u := Real.log_two_lt_d9
  have hLY'1 : LX / 202 ≤ Real.log Y' := by linarith
  have hLY'2 : 13860 ≤ Real.log Y' := by linarith
  have hI' : ∀ p ∈ I, p.Prime ∧ Y' < p := fun p hp => ⟨(hI p hp).1, by
    have : (Y' : ℝ) < p := lt_of_le_of_lt hY'le (hI p hp).2
    exact_mod_cast this⟩
  have hIp : ∀ p ∈ I, p.Prime := fun p hp => (hI p hp).1
  have h2N : 2 * N ≤ (Y' : ℝ) ^ 102 := by
    have e1 : (Y' : ℝ) ^ 102 = Real.exp (102 * Real.log Y') := by
      rw [show (102 : ℝ) = ((102 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hY'pos]
    have e2 : 2 * N ≤ Real.exp (Real.log 2 + LX) := by
      rw [Real.exp_add, Real.exp_log (by norm_num), hLX, Real.exp_log hX0]; linarith
    rw [e1]; refine e2.trans (Real.exp_le_exp.2 ?_)
    linarith
  -- convert to a real sum
  have hconv : (∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), binInd I n)
      - (((N / q) * binDelta I N : ℝ) : ℂ)
      = (((∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q),
          (if ∃ p ∈ I, p ∣ n then (0 : ℝ) else 1)) - N / q * binDelta I N : ℝ) : ℂ) := by
    simp only [binInd_eq_ofReal]; push_cast; ring
  rw [hconv, Complex.norm_real, Real.norm_eq_abs, div_div_eq_mul_div, mul_comm N, mul_div_assoc]
  have hq0 : 0 < q := hq
  have he5 := exp_five_lt
  have hl4 := log_four_lt
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hNLX' : 0 ≤ N / LX := by positivity
  by_cases hqY : (q : ℝ) ≤ Y
  · -- small modulus
    have hs := abs_apSum_sub_le_small hIp hq0
      (fun p hp => by have := (hI p hp).2; exact_mod_cast (show (q : ℝ) < p by linarith)) hN a
    have hc := card_prodLe_le' hLY'2 hI' (by linarith) h2N
    have hk : Real.exp 5 * Real.log 4 * (2 * N) / Real.log Y'
        ≤ 404 * (Real.exp 5 * Real.log 4) * (N / LX) := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ Real.exp 5 * Real.log 4 * N := by positivity
      calc Real.exp 5 * Real.log 4 * (2 * N) = (Real.exp 5 * Real.log 4 * N) * 2 := by ring
        _ ≤ (Real.exp 5 * Real.log 4 * N) * (404 * Real.log Y' / LX) := by
            gcongr; rw [le_div_iff₀ hLXpos]; linarith
        _ = _ := by field_simp
    have h1 : 1 ≤ 2.5 * (N / LX) := by rw [mul_div_assoc', le_div_iff₀ hLXpos]; linarith
    have hK : Real.exp 5 * Real.log 4 ≤ 149 * 1.4 := by
      have := Real.exp_pos 5; nlinarith
    nlinarith
  · -- large modulus
    push Not at hqY
    have hl := abs_apSum_sub_le_large I hq0 hN a
    have hs := sum_prodLe_inv_le hLY'2 hI' h2N
    have hqLX : LX / 101 < q := by
      have : X ^ ((1 : ℝ) / 101) / (1 / 101) = 101 * X ^ ((1 : ℝ) / 101) := by ring
      linarith
    have hqr : (0 : ℝ) < q := by linarith
    have hinv : 1 / (q : ℝ) ≤ 101 / LX := by
      rw [div_le_div_iff₀ hqr hLXpos]; linarith
    have h1 : 1 ≤ 2.5 * (N / LX) := by rw [mul_div_assoc', le_div_iff₀ hLXpos]; linarith
    have hA : (N + 1) / q ≤ 202 * (N / LX) := by
      calc (N + 1) / q = (N + 1) * (1 / q) := by ring
        _ ≤ (2 * N) * (101 / LX) := by gcongr; linarith
        _ = 202 * (N / LX) := by ring
    have hB : N / q * ∑ T ∈ prodLe I (2 * N), ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹
        ≤ 149 * 101 * (N / LX) := by
      have hS0 : 0 ≤ ∑ T ∈ prodLe I (2 * N), ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹ :=
        sum_nonneg fun _ _ => by positivity
      calc N / q * ∑ T ∈ prodLe I (2 * N), ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹
          ≤ (N * (101 / LX)) * 149 := by
            rw [div_eq_mul_one_div N]
            gcongr; linarith
        _ = 149 * 101 * (N / LX) := by ring
    linarith

end NormalNumbers.G4.Base2
