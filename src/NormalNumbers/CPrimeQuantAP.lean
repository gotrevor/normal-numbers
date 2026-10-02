/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4MertensAP
import NormalNumbers.G4WiringSparse
import NormalNumbers.CPrimeQuantStatement

/-!
# Quantitative C′: Mertens in progressions, upper bound (build gap 6)

The fresh mass `∑_{√N<p≤N, p≡a (q)} 1/p` of a residue class is eventually `≤ 2e/φ(q) + ε`.
Route (no sieve, no Tauberian theorem):
1. `LSeries_residueClass_upper`: mathlib's auxiliary function is continuous on `[1,2]`, so
   `∑ Λ_a(n)/n^x ≤ φ(q)⁻¹/(x−1) + C` (the mirror of `LSeries_residueClass_lower_bound`).
2. `sumLogAP_le`: at `x = 1 + 1/log N`, `p^x ≤ e·p` for `p ≤ N`, so
   `∑_{p≤N, p≡a} log p/p ≤ e(log N/φ(q) + C)`.
3. `recipAP_le`: Abel summation against the weights `1/log t − 1/log(t+1) ≥ 0`.
-/

open Finset Real Filter

namespace NormalNumbers.PrimeModel.Quant

section ResidueClass

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Upper bound mirror** of mathlib's `LSeries_residueClass_lower_bound`. -/
lemma LSeries_residueClass_upper (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      ∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ x
        ≤ (q.totient : ℝ)⁻¹ / (x - 1) + C := by
  open ArithmeticFunction.vonMangoldt Complex in
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : ℝ) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
      eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  open ArithmeticFunction.vonMangoldt Complex in
  have : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux a)
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := bddAbove_def.mp <| IsCompact.bddAbove_image isCompact_Icc this
  refine ⟨max C 0, le_max_right _ _, fun {x} hx ↦ ?_⟩
  rw [H hx.1, add_comm]
  have := hC _ (Set.mem_image_of_mem _ (Set.mem_Icc_of_Ioc hx))
  linarith [le_max_left C 0]

/-- The prime part below `N`: `∑_{p≤N, p≡a} log p/p ≤ e(log N/φ(q) + C)`. -/
theorem sumLogAP_le (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      ∑ p ∈ (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), Real.log p / p
        ≤ Real.exp 1 * (Real.log N / q.totient + C) := by
  obtain ⟨C, hC0, hC⟩ := LSeries_residueClass_upper ha
  refine ⟨C, hC0, fun N hN => ?_⟩
  set rc := ArithmeticFunction.vonMangoldt.residueClass a with hrc
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  set x : ℝ := 1 + 1 / Real.log N with hx
  have hx1 : 1 < x := by
    rw [hx]; have : 0 < 1 / Real.log N := by positivity
    linarith
  have hx2 : x ≤ 2 := by
    rw [hx]; have : 1 / Real.log N ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hsum : Summable (fun n : ℕ => rc n / (n : ℝ) ^ x) := by
    refine LSeries.summable_real_of_abscissaOfAbsConv_lt ?_
    refine lt_of_le_of_lt
      (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) ?_
    exact_mod_cast hx1
  have hrc0 : ∀ n, 0 ≤ rc n / (n : ℝ) ^ x := fun n => by
    have := ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
    have : (0 : ℝ) ≤ (n : ℝ) ^ x := Real.rpow_nonneg (by positivity) _
    positivity
  have hterm : ∀ p ∈ (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
      Real.log p / p ≤ Real.exp 1 * (rc p / (p : ℝ) ^ x) := by
    intro p hp
    obtain ⟨hpN, hpp, hpa⟩ := by simpa using hp
    have hrcp : rc p = Real.log p := by
      simp [hrc, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, hpa,
        ArithmeticFunction.vonMangoldt_apply_prime hpp]
    rw [hrcp]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
    have hpx : (p : ℝ) ^ x ≤ Real.exp 1 * p := by
      rw [hx, Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
      gcongr
      rw [Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.mpr
      rw [mul_one_div, div_le_one (by linarith)]
      exact Real.log_le_log (by linarith) hpN'
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have hpx0 : 0 < (p : ℝ) ^ x := Real.rpow_pos_of_pos (by linarith) _
    rw [mul_div_assoc', le_div_iff₀ hpx0, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [Real.exp_pos 1]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
  refine (hsum.sum_le_tsum _ (fun n _ => hrc0 n)).trans ?_
  refine (hC ⟨hx1, hx2⟩).trans (le_of_eq ?_)
  rw [hx]; field_simp; ring

end ResidueClass

/-! ### Abel summation against `1/log` -/

/-- The Abel weights `w_t = 1/log t − 1/log(t+1)`. -/
noncomputable def abelW (t : ℕ) : ℝ := 1 / Real.log t - 1 / Real.log (t + 1)

lemma abelW_nonneg {t : ℕ} (ht : 2 ≤ t) : 0 ≤ abelW t := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : 0 < Real.log t := Real.log_pos (by linarith)
  have h1 : Real.log t ≤ Real.log ((t : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  unfold abelW
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le h0 h1

/-- Abel summation identity: `∑_{M<n≤N} f n/log n = T(N)/log N + ∑_{M<t<N} w_t T(t)`. -/
lemma abel_identity (f : ℕ → ℝ) (M : ℕ) (hM : 2 ≤ M) :
    ∀ N, M ≤ N → ∑ n ∈ Ioc M N, f n / Real.log n
      = (∑ n ∈ Ioc M N, f n) / Real.log N
        + ∑ t ∈ Ico (M + 1) N, abelW t * ∑ n ∈ Ioc M t, f n := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hM.trans hMN
    have hl0 : Real.log N ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hl1 : Real.log ((N : ℝ) + 1) ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), ih]
    rcases Nat.eq_or_lt_of_le hMN with hEq | hlt
    · subst hEq; simp
    · rw [Finset.sum_Ico_succ_top (by omega)]
      unfold abelW
      push_cast
      field_simp
      ring

/-- **Abel bound.**  If the partial sums of `f ≥ 0` over `(M, t]` are `≤ A log t + B`, then
`∑_{M<n≤N} f n/log n ≤ A log N/log M + B/log M`. -/
lemma abel_log_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : ∀ t, M < t → t ≤ N → ∑ n ∈ Ioc M t, f n ≤ A * Real.log t + B) :
    ∑ n ∈ Ioc M N, f n / Real.log n ≤ A * Real.log N / Real.log M + B / Real.log M := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlM : 0 < Real.log M := Real.log_pos (by linarith)
  rw [abel_identity f M hM N hMN]
  rcases Nat.eq_or_lt_of_le hMN with hEq | hlt
  · subst hEq; simp; positivity
  -- the weighted tail
  have hQ : ∀ K, M + 1 ≤ K → K ≤ N →
      ∑ t ∈ Ico (M + 1) K, abelW t * ∑ n ∈ Ioc M t, f n
        ≤ A * (Real.log K - Real.log (M + 1)) / Real.log M
          + B * (1 / Real.log (M + 1) - 1 / Real.log K) := by
    intro K hK hKN
    induction K, hK using Nat.le_induction with
    | base => push_cast; simp
    | succ K hMK ih =>
      have hKR : (2 : ℝ) ≤ K := by exact_mod_cast (hM.trans (by omega : M ≤ K))
      have hlK : 0 < Real.log K := Real.log_pos (by linarith)
      have hlK1 : Real.log K ≤ Real.log ((K : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
      have hlMK : Real.log M ≤ Real.log K := Real.log_le_log (by linarith)
        (by exact_mod_cast (by omega : M ≤ K))
      rw [Finset.sum_Ico_succ_top hMK]
      have ih' := ih (by omega)
      have hw := abelW_nonneg (t := K) (by omega)
      have hTK := hT K (by omega) (by omega)
      have step1 : abelW K * ∑ n ∈ Ioc M K, f n ≤ abelW K * (A * Real.log K + B) :=
        mul_le_mul_of_nonneg_left hTK hw
      have step2 : abelW K * (A * Real.log K) ≤ A * (Real.log (K + 1) - Real.log K) / Real.log M := by
        unfold abelW
        have e : (1 / Real.log K - 1 / Real.log ((K : ℝ) + 1)) * (A * Real.log K)
            = A * ((Real.log ((K : ℝ) + 1) - Real.log K) / Real.log ((K : ℝ) + 1)) := by
          have : Real.log ((K : ℝ) + 1) ≠ 0 := by linarith
          field_simp
        rw [e, mul_div_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hA
        exact div_le_div_of_nonneg_left (by linarith) hlM (hlMK.trans hlK1)
      have e3 : abelW K * B = B * (1 / Real.log K - 1 / Real.log ((K : ℝ) + 1)) := by
        unfold abelW; ring
      push_cast
      have : abelW K * (A * Real.log K + B) = abelW K * (A * Real.log K) + abelW K * B := by ring
      rw [this, e3] at step1
      have e4 : A * (Real.log ((K : ℝ) + 1) - Real.log (M + 1)) / Real.log M
          = A * (Real.log K - Real.log (M + 1)) / Real.log M
            + A * (Real.log ((K : ℝ) + 1) - Real.log K) / Real.log M := by ring
      rw [e4]
      push_cast at ih' step2
      linarith
  have hQN := hQ N (by omega) le_rfl
  have hNR : (2 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt hM hlt)
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hTN := hT N hlt le_rfl
  have hM1 : Real.log M ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have h1 : (∑ n ∈ Ioc M N, f n) / Real.log N ≤ A + B / Real.log N := by
    rw [div_le_iff₀ hlN, add_mul, div_mul_cancel₀ _ hlN.ne']; linarith
  have h2 : A * (Real.log N - Real.log (M + 1)) / Real.log M
      ≤ A * Real.log N / Real.log M - A := by
    have hA' : A ≤ A * Real.log (M + 1) / Real.log M := by
      rw [le_div_iff₀ hlM]; push_cast; nlinarith
    have : A * (Real.log N - Real.log (M + 1)) / Real.log M
        = A * Real.log N / Real.log M - A * Real.log (M + 1) / Real.log M := by ring
    linarith
  have h3 : B * (1 / Real.log (M + 1) - 1 / Real.log N) + B / Real.log N ≤ B / Real.log M := by
    have h4 : 1 / Real.log ((M : ℝ) + 1) ≤ 1 / Real.log M := one_div_le_one_div_of_le hlM hM1
    have h5 := mul_le_mul_of_nonneg_left h4 hB
    rw [div_eq_mul_one_div B (Real.log N), div_eq_mul_one_div B (Real.log M)]
    push_cast
    nlinarith
  linarith

/-! ### The residue-class fresh mass -/

/-- **Mertens in progressions, upper bound for the fresh mass.**  The square-root fresh mass of
the primes `≡ a (mod q)` is eventually `≤ 9/φ(q) + ε` (`3e/φ(q)` from `sumLogAP_le` and
`abel_log_le`, with `log N ≤ 3 log √N`). -/
theorem sqrtFreshMassLe_residue {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    SqrtFreshMassLe (fun p => p % q = a % q) (9 / q.totient) := by
  haveI : NeZero q := ⟨by omega⟩
  have haZ : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  obtain ⟨C, hC0, hC⟩ := sumLogAP_le haZ
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  intro ε hε
  set K : ℝ := Real.exp 1 * C / ε + 1 with hK
  set m : ℕ := max 3 ⌈Real.exp K⌉₊ with hm
  filter_upwards [eventually_ge_atTop (m * m)] with N hN
  set M := Nat.sqrt N with hMdef
  have hmM : m ≤ M := Nat.le_sqrt.mpr hN
  have hM3 : 3 ≤ M := (le_max_left _ _).trans hmM
  have hMN : M ≤ N := Nat.sqrt_le_self N
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hlM : 0 < Real.log M := Real.log_pos (by linarith)
  set f : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) = a then Real.log n / n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf]; split_ifs with h
    · have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast h.1.one_lt.le); positivity
    · exact le_rfl
  -- the fresh mass is the Abel sum
  have hrecip : G4Sparse.recipSumIoc (fun p => p % q = a % q) M N
      = ∑ n ∈ Ioc M N, f n / Real.log n := by
    rw [G4Sparse.recipSumIoc, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hiff : (n.Prime ∧ n % q = a % q) ↔ (n.Prime ∧ (n : ZMod q) = a) := by
      rw [← ZMod.natCast_eq_natCast_iff']
    simp only [hf]
    by_cases h : n.Prime ∧ (n : ZMod q) = a
    · rw [if_pos (hiff.mpr h), if_pos h]
      have : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.1.one_lt)
      field_simp
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, zero_div]
  have hT : ∀ t, M < t → t ≤ N → ∑ n ∈ Ioc M t, f n
      ≤ Real.exp 1 / q.totient * Real.log t + Real.exp 1 * C := by
    intro t hMt _
    have hsub : ∑ n ∈ Ioc M t, f n ≤ ∑ n ∈ range (t + 1), f n :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => by simp at hn ⊢; omega) (fun n _ _ => hf0 n)
    have heq : ∑ n ∈ range (t + 1), f n
        = ∑ p ∈ (range (t + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
            Real.log p / p := by
      rw [Finset.sum_filter]
    have := hC t (by omega)
    rw [heq] at hsub
    have e : Real.exp 1 * (Real.log t / q.totient + C)
        = Real.exp 1 / q.totient * Real.log t + Real.exp 1 * C := by ring
    linarith
  have hab := abel_log_le hf0 (by omega) hMN (by positivity) (by positivity) hT
  rw [hrecip]
  refine hab.trans ?_
  -- log N ≤ 3 log M
  have hN3 : Real.log N ≤ 3 * Real.log M := by
    have h1 : N < (M + 1) * (M + 1) := Nat.lt_succ_sqrt N
    have h2 : (M + 1) * (M + 1) ≤ M ^ 3 := by nlinarith
    have hNpos : (0 : ℝ) < N := by
      have : 0 < N := lt_of_lt_of_le (by omega) hMN
      exact_mod_cast this
    have : 3 * Real.log M = Real.log ((M : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
    rw [this]
    exact Real.log_le_log hNpos (by exact_mod_cast (h1.trans_le h2).le)
  have hA : Real.exp 1 / q.totient * Real.log N / Real.log M ≤ 9 / q.totient := by
    rw [div_le_iff₀ hlM]
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have : Real.exp 1 / q.totient * Real.log N ≤ 3 / q.totient * (3 * Real.log M) := by
      have hlN : 0 ≤ Real.log N := Real.log_nonneg (by
        have : 1 ≤ N := by omega
        exact_mod_cast this)
      apply mul_le_mul (div_le_div_of_nonneg_right he hφ.le) hN3 hlN (by positivity)
    have e : 3 / (q.totient : ℝ) * (3 * Real.log M) = 9 / q.totient * Real.log M := by ring
    linarith
  have hB : Real.exp 1 * C / Real.log M ≤ ε := by
    have hKM : K ≤ Real.log M := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hmM)
    rw [div_le_iff₀ hlM]
    have : Real.exp 1 * C / ε < K := by rw [hK]; linarith
    rw [div_lt_iff₀ hε] at this
    nlinarith
  linarith

/-! ### `φ(q) → ∞` and divergence -/

/-- `φ(n) ≥ K` once `n > ((K+1)!)^K`: otherwise every prime `p ∣ n` has `p ≤ K` and every
exponent is `< K`, so `n ∣ ((K+1)!)^K`. -/
theorem le_totient_of_large (K : ℕ) {n : ℕ} (hn : ((K + 1).factorial) ^ K < n) :
    K ≤ n.totient := by
  by_contra hlt
  push_neg at hlt
  have hn0 : n ≠ 0 := by omega
  have hM0 : ((K + 1).factorial) ^ K ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  have hdvd : n ∣ ((K + 1).factorial) ^ K := by
    rw [← Nat.factorization_le_iff_dvd hn0 hM0]
    intro p
    by_cases he : n.factorization p = 0
    · rw [he]; exact Nat.zero_le _
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr he)
    have hpn : p ∣ n := Nat.dvd_of_factorization_pos he
    have hφp : p.totient ≤ n.totient := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
      (Nat.totient_dvd_of_dvd hpn)
    rw [Nat.totient_prime hp] at hφp
    have hpK : p ≤ K + 1 := by omega
    have hpfac : p ∣ (K + 1).factorial := (Nat.Prime.dvd_factorial hp).mpr hpK
    have hfac1 : 1 ≤ (K + 1).factorial.factorization p := by
      have := (hp.dvd_iff_one_le_factorization (Nat.factorial_ne_zero _)).mp hpfac
      exact this
    have hpe : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have hφpe : (p ^ n.factorization p).totient ≤ n.totient :=
      Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (Nat.totient_dvd_of_dvd hpe)
    obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
    rw [hk] at hφpe ⊢
    rw [Nat.totient_prime_pow_succ hp] at hφpe
    have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
    have h3 : k < 2 ^ k := Nat.lt_two_pow_self
    have h4 : 1 ≤ p - 1 := by have := hp.two_le; omega
    have h5 : p ^ k ≤ p ^ k * (p - 1) := Nat.le_mul_of_pos_right _ h4
    rw [Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    have : k + 1 ≤ K := by omega
    nlinarith
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hdvd) (by omega)

/-- Primes `≡ a (mod q)` have divergent reciprocal sum (from `mertensRate_residueClass`). -/
theorem divergentRecip_residue {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    G4Sparse.DivergentRecip (fun p => p % q = a % q) := by
  haveI : NeZero q := ⟨by omega⟩
  have haZ : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  obtain ⟨c, C, hc, hM⟩ := G4.MertensAP.mertensRate_residueClass haZ
  intro hsum
  set g : ℕ → ℝ := fun p => if p.Prime ∧ p % q = a % q then (1 : ℝ) / p else 0 with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity
  have hbound : ∀ N : ℕ, 2 ≤ N → c * Real.log (Real.log N) - C ≤ ∑' p, g p := by
    intro N hN
    refine (hM N hN).trans ?_
    have : G4.MertensAP.sumInvPrimesIn (fun p => (p : ZMod q) = a) N
        ≤ ∑ p ∈ range N, g p := by
      rw [G4.MertensAP.sumInvPrimesIn, Finset.sum_filter, Nat.primesBelow, Finset.sum_filter]
      refine Finset.sum_le_sum fun p _ => ?_
      simp only [hg]
      by_cases hp : p.Prime
      · by_cases hpa : (p : ZMod q) = a
        · rw [if_pos hp, if_pos hpa, if_pos ⟨hp, (ZMod.natCast_eq_natCast_iff' p a q).mp hpa⟩,
            one_div]
        · rw [if_pos hp, if_neg hpa]; split_ifs <;> positivity
      · rw [if_neg hp]; split_ifs <;> positivity
    exact this.trans (hsum.sum_le_tsum _ (fun p _ => hg0 p))
  -- `log log N → ∞`
  have ht : Tendsto (fun N : ℕ => c * Real.log (Real.log N) - C) atTop atTop := by
    refine tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop hc ?_)
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := ((ht.eventually_gt_atTop (∑' p, g p)).and (eventually_ge_atTop 2)).exists
  linarith [hbound N hN.2]

end NormalNumbers.PrimeModel.Quant
