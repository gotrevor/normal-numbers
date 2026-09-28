import NormalNumbers.TwoPointDelangeWire

/-!
# Past the `‖z − 1‖ < 1` wall: the parity case `t = 1/2`, from Möbius

`delangeMean_of_norm_lt_one` (`TwoPointDelangeScale.lean`) proves `DelangeMean t` for
`‖phase t − 1‖ < 1`, i.e. `‖t‖_{ℝ/ℤ} < 1/6`.  `TwoPointDelangeWire.lean` records why the
remaining regime is not a technical gap: at `t = 1/2` the Dirichlet series of `(−1)^{ω(n)}` is
`ζ(s)·∏_p(1 − 2p^{-s}) ≈ 1/ζ(s)`, so `DelangeMean (1/2)` is of Möbius/PNT strength.

## The structural observation this file runs on

For `z` on the unit circle, `z^ω` and the *completely* multiplicative `z^Ω` differ by a Dirichlet
convolution supported on powerful numbers:

    z^ω = z^Ω * k_z ,   k_z(p) = 0 ,  k_z(p^j) = −z(z−1) for j ≥ 2

(compare local factors `(1 + (z−1)X)/(1−X)` and `(1 − zX)^{-1}`).  And `z^Ω` reduces to Möbius by a
*finite* convolution exactly when `z = −1`:

    λ = 1_{squares} * μ        (`ζ(2s)/ζ(s)`),

because the exponent `w` in `(1 − zX)^{-1}(1 − X)^{w}` is an integer only for `z = −1`.  **That is
the precise reason `t = 1/2` (and only `t = 1/2`) is reachable from PNT by elementary means, while
`b ≥ 3` needs `ζ(s)^z` — Selberg–Delange or Halász.**  Recording that dichotomy is half the point of
this file.

## Contents

* `kernelSum_tendsto_zero` — **the transfer engine**: if `‖A n‖ ≤ n` and `A n / n → 0`, and
  `∑_d ‖k d‖/d < ∞`, then `(∑_{d ≤ N} k d · A(N/d))/N → 0`.  Used once per convolution stage.
* `sum_conv_eq` — the general hyperbola identity `∑_{n ≤ N} (k * T)(n) = ∑_{d ≤ N} k d · (∑_{e ≤ N/d} T e)`.
* `MoebiusMeanZero` — the cited classical input `∑_{n ≤ N} μ(n) = o(N)` (Landau 1911; equivalent to
  the prime number theorem, which is itself in this tree as `PNTPort.MediumPNT` — see the handoff
  for the remaining Axer-type deduction).
* `liouvilleMean_of_moebius` — stage A: `MoebiusMeanZero → (1/N)∑_{n≤N} λ(n) → 0`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### The general hyperbola identity -/

/-- **Hyperbola summation for a Dirichlet convolution.**  `∑_{n ≤ N} ∑_{d | n} k d · T (n/d)`
regrouped by `d`. -/
theorem sum_conv_eq {R : Type*} [NonUnitalNonAssocSemiring R] (k T : ℕ → R) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, k d * T (n / d)
      = ∑ d ∈ Finset.Ioc 0 N, k d * ∑ e ∈ Finset.Ioc 0 (N / d), T e := by
  classical
  have hstep : ∀ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, k d * T (n / d)
      = ∑ d ∈ Finset.Ioc 0 N, if d ∣ n then k d * T (n / d) else 0 := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn.1, le_trans (Nat.le_of_dvd hn.1 hdvd) hn.2⟩, hdvd⟩
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_Ioc] at hd
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_nbij' (fun n => n / d) (fun e => d * e) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hn0, hnN⟩, hdvd⟩ := hn
    refine ⟨Nat.div_pos (Nat.le_of_dvd hn0 hdvd) hd.1, ?_⟩
    exact Nat.div_le_div_right hnN
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_Ioc] at he ⊢
    refine ⟨⟨Nat.mul_pos hd.1 he.1, ?_⟩, Dvd.intro e rfl⟩
    calc d * e ≤ d * (N / d) := Nat.mul_le_mul_left d he.2
      _ = (N / d) * d := by ring
      _ ≤ N := Nat.div_mul_le_self N d
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro e he
    exact Nat.mul_div_cancel_left e hd.1
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    rfl


/-! ### The transfer engine -/

/-- **Transfer across a summable convolution kernel.**  If `A` has `‖A n‖ ≤ n` and `A n = o(n)`,
and the kernel `k` has `∑_d ‖k d‖/d < ∞`, then `∑_{d ≤ N} k d · A(N/d) = o(N)`.

This is the only analytic step in the chain: each convolution stage (`λ = 1_{sq} * μ`, then
`z^ω = z^Ω * k_z`) is discharged by one application. -/
theorem kernelSum_tendsto_zero (k A : ℕ → ℂ)
    (hk : Summable fun d : ℕ => ‖k d‖ / (d : ℝ))
    (hAle : ∀ n : ℕ, ‖A n‖ ≤ (n : ℝ))
    (hA : Tendsto (fun n : ℕ => ‖A n‖ / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ‖∑ d ∈ Finset.Ioc 0 N, k d * A (N / d)‖ / (N : ℝ)) atTop (𝓝 0) := by
  classical
  set f : ℕ → ℝ := fun d => ‖k d‖ / (d : ℝ) with hf
  have hf0 : ∀ d, 0 ≤ f d := fun d => by positivity
  set K : ℝ := ∑' d, f d with hK
  have hK0 : 0 ≤ K := tsum_nonneg hf0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the tail of the kernel
  have htail : Tendsto (fun i : ℕ => ∑' d : ℕ, f (d + i)) atTop (𝓝 0) :=
    tendsto_sum_nat_add f
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨D₀, hD₀⟩ := htail (ε / 2) (by linarith)
  set D : ℕ := D₀ + 1 with hD
  have hDpos : 0 < D := by omega
  have htailD : ∑' i : ℕ, f (i + D) < ε / 2 := by
    have h := hD₀ D (by omega)
    rw [Real.dist_eq, sub_zero] at h
    calc ∑' i : ℕ, f (i + D) ≤ |∑' i : ℕ, f (i + D)| := le_abs_self _
      _ < ε / 2 := h
  -- the smallness of `A`
  set ε' : ℝ := ε / (2 * (K + 1)) with hε'
  have hε'pos : 0 < ε' := by
    rw [hε']; apply div_pos hε; linarith
  have hAsmall : ∀ᶠ n : ℕ in atTop, ‖A n‖ ≤ ε' * (n : ℝ) := by
    rw [Metric.tendsto_atTop] at hA
    obtain ⟨M, hM⟩ := hA ε' hε'pos
    filter_upwards [Filter.eventually_ge_atTop (max M 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right M 1) hn
    have hnM : M ≤ n := le_trans (le_max_left M 1) hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h := hM n hnM
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
    have := (div_lt_iff₀ hnR).mp h
    linarith
  obtain ⟨M, hM⟩ := (Filter.eventually_atTop.mp hAsmall)
  refine ⟨max (D * (M + 1)) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNbig : D * (M + 1) ≤ N := le_trans (le_max_left _ _) hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  -- split the sum at `D`
  have hsplit : ∑ d ∈ Finset.Ioc 0 N, k d * A (N / d)
      = (∑ d ∈ Finset.Ioc 0 (min D N), k d * A (N / d))
        + ∑ d ∈ Finset.Ioc (min D N) N, k d * A (N / d) := by
    rw [← Finset.sum_union]
    · congr 1
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (min_le_right D N)]
    · refine Finset.disjoint_left.mpr fun a ha hb => ?_
      simp only [Finset.mem_Ioc] at ha hb
      omega
  -- the head: `‖A (N/d)‖ ≤ ε' · N/d`
  have hhead : ‖∑ d ∈ Finset.Ioc 0 (min D N), k d * A (N / d)‖ ≤ ε' * K * (N : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ d ∈ Finset.Ioc 0 (min D N),
        ‖k d * A (N / d)‖ ≤ ε' * (N : ℝ) * f d := by
      intro d hd
      simp only [Finset.mem_Ioc, le_min_iff] at hd
      have hd0 : 0 < d := hd.1
      have hdD : d ≤ D := hd.2.1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      have hMle : M ≤ N / d := by
        have h1 : (M + 1) * d ≤ N := by
          calc (M + 1) * d ≤ (M + 1) * D := Nat.mul_le_mul_left _ hdD
            _ = D * (M + 1) := by ring
            _ ≤ N := hNbig
        have h2 : M + 1 ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr h1
        omega
      have hA1 : ‖A (N / d)‖ ≤ ε' * ((N / d : ℕ) : ℝ) := hM _ hMle
      have hA2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      have hA3 : ‖A (N / d)‖ ≤ ε' * ((N : ℝ) / d) := by
        refine le_trans hA1 ?_
        exact mul_le_mul_of_nonneg_left hA2 hε'pos.le
      rw [norm_mul, hf]
      have : ‖k d‖ * ‖A (N / d)‖ ≤ ‖k d‖ * (ε' * ((N : ℝ) / d)) :=
        mul_le_mul_of_nonneg_left hA3 (norm_nonneg _)
      calc ‖k d‖ * ‖A (N / d)‖ ≤ ‖k d‖ * (ε' * ((N : ℝ) / d)) := this
        _ = ε' * (N : ℝ) * (‖k d‖ / (d : ℝ)) := by field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ d ∈ Finset.Ioc 0 (min D N), f d ≤ K :=
      hk.sum_le_tsum _ (fun d _ => hf0 d)
    have : ε' * (N : ℝ) * (∑ d ∈ Finset.Ioc 0 (min D N), f d) ≤ ε' * (N : ℝ) * K :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    calc ε' * (N : ℝ) * (∑ d ∈ Finset.Ioc 0 (min D N), f d) ≤ ε' * (N : ℝ) * K := this
      _ = ε' * K * (N : ℝ) := by ring
  -- the tail: `‖A (N/d)‖ ≤ N/d`
  have htail2 : ‖∑ d ∈ Finset.Ioc (min D N) N, k d * A (N / d)‖ ≤ (ε / 2) * (N : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ d ∈ Finset.Ioc (min D N) N,
        ‖k d * A (N / d)‖ ≤ (N : ℝ) * f d := by
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hd0 : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      have hA2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      have hA3 : ‖A (N / d)‖ ≤ (N : ℝ) / d := le_trans (hAle _) hA2
      rw [norm_mul, hf]
      calc ‖k d‖ * ‖A (N / d)‖ ≤ ‖k d‖ * ((N : ℝ) / d) :=
            mul_le_mul_of_nonneg_left hA3 (norm_nonneg _)
        _ = (N : ℝ) * (‖k d‖ / (d : ℝ)) := by field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ d ∈ Finset.Ioc (min D N) N, f d ≤ ∑' i : ℕ, f (i + D) := by
      have hshift : Summable (fun i : ℕ => f (i + D)) := (summable_nat_add_iff D).mpr hk
      have hsub : Finset.Ioc (min D N) N ⊆ (Finset.range N).image (fun i => i + D) := by
        intro d hd
        simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range] at hd ⊢
        exact ⟨d - D, by omega, by omega⟩
      calc ∑ d ∈ Finset.Ioc (min D N) N, f d
          ≤ ∑ d ∈ (Finset.range N).image (fun i => i + D), f d :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hf0 d)
        _ = ∑ i ∈ Finset.range N, f (i + D) :=
            Finset.sum_image (by intro x _ y _ h; exact Nat.add_right_cancel h)
        _ ≤ ∑' i : ℕ, f (i + D) := hshift.sum_le_tsum _ (fun i _ => hf0 _)
    have := mul_le_mul_of_nonneg_left hsum hNR.le
    calc (N : ℝ) * (∑ d ∈ Finset.Ioc (min D N) N, f d) ≤ (N : ℝ) * (∑' i : ℕ, f (i + D)) := this
      _ ≤ (N : ℝ) * (ε / 2) := mul_le_mul_of_nonneg_left htailD.le hNR.le
      _ = (ε / 2) * (N : ℝ) := by ring
  have hεK : ε' * K < ε / 2 := by
    rw [hε']
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hK0]
  calc ‖∑ d ∈ Finset.Ioc 0 N, k d * A (N / d)‖ / (N : ℝ)
      ≤ (ε' * K * (N : ℝ) + (ε / 2) * (N : ℝ)) / (N : ℝ) := by
        have hle : ‖∑ d ∈ Finset.Ioc 0 N, k d * A (N / d)‖
            ≤ ε' * K * (N : ℝ) + (ε / 2) * (N : ℝ) := by
          rw [hsplit]
          exact le_trans (norm_add_le _ _) (add_le_add hhead htail2)
        gcongr
    _ = ε' * K + ε / 2 := by field_simp
    _ < ε := by linarith


/-! ### Stage A: `λ = 1_{squares} * μ`, so the Liouville mean is Möbius-controlled -/

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- The indicator of the squares, as an arithmetic function. -/
noncomputable def sqIndA : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else if IsSquare n then 1 else 0, by simp⟩

lemma sqIndA_apply (n : ℕ) :
    sqIndA n = if n = 0 then 0 else if IsSquare n then 1 else 0 := rfl

lemma norm_sqIndA_le (n : ℕ) : ‖sqIndA n‖ ≤ 1 := by
  rw [sqIndA_apply]
  split
  · simp
  · split <;> simp

/-- `p^k` is a square iff `k` is even. -/
lemma isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact pow_ne_zero k hp.ne_zero (by simpa using hc)
    have h := congrArg (fun m : ℕ => m.factorization p) hc
    simp only [Nat.factorization_mul hc0 hc0, Nat.Prime.factorization_pow hp,
      Finsupp.single_eq_same, Finsupp.add_apply] at h
    exact ⟨c.factorization p, h⟩
  · rintro ⟨m, hm⟩
    exact ⟨p ^ m, by rw [← pow_add, hm]⟩

/-- Coprime factors of a square are squares. -/
lemma isSquare_of_coprime_mul {m n : ℕ} (hmn : m.Coprime n) (h : IsSquare (m * n)) :
    IsSquare m := by
  obtain ⟨c, hc⟩ := h
  have hgcd : IsUnit (gcd m n) := by
    rw [Nat.isUnit_iff]
    exact hmn
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (k := 2) hgcd (by rw [hc]; ring)
  exact ⟨d, by rw [hd]; ring⟩

lemma isMultiplicative_sqIndA : sqIndA.IsMultiplicative := by
  constructor
  · simp [sqIndA_apply]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [sqIndA_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [sqIndA_apply]
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
    simp only [sqIndA_apply, hm, hn, hmn0, if_false]
    by_cases hsq : IsSquare (m * n)
    · have h1 : IsSquare m := isSquare_of_coprime_mul hmn hsq
      have h2 : IsSquare n :=
        isSquare_of_coprime_mul hmn.symm (by rwa [mul_comm] at hsq)
      simp [hsq, h1, h2]
    · have hno : ¬ (IsSquare m ∧ IsSquare n) := by
        rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        exact hsq ⟨a * b, by rw [ha, hb]; ring⟩
      rcases Classical.em (IsSquare m) with h1 | h1
      · have h2 : ¬ IsSquare n := fun h => hno ⟨h1, h⟩
        simp [hsq, h1, h2]
      · simp [hsq, h1]

lemma sum_neg_one_pow_range (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd n with he | ho
    · have h1 : Odd (n + 1) := Even.add_one he
      have h2 : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr h1
      rw [if_pos he, if_neg h2, h1.neg_one_pow]
      ring
    · have h1 : Even (n + 1) := Odd.add_one ho
      have h2 : ¬ Even n := Nat.not_even_iff_odd.mpr ho
      rw [if_neg h2, if_pos h1, h1.neg_one_pow]
      ring

/-- **`∑_{d | n} λ(d) = 1_{squares}(n)`** — the divisor sum of Liouville's function. -/
theorem liouville_mul_zeta : (↑liouville : ArithmeticFunction ℂ) * ζ = sqIndA := by
  have hmulL : (↑liouville : ArithmeticFunction ℂ).IsMultiplicative :=
    isMultiplicative_liouville.intCast
  have hmul : ((↑liouville : ArithmeticFunction ℂ) * ζ).IsMultiplicative :=
    hmulL.mul isMultiplicative_zeta.natCast
  rw [(ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _ isMultiplicative_sqIndA)]
  intro p k hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (↑liouville : ArithmeticFunction ℂ) (p ^ j) = (-1 : ℂ) ^ j := by
    intro j _
    rw [intCoe_apply, liouville_apply (pow_ne_zero _ hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [sum_neg_one_pow_range k, sqIndA_apply]
  have hp0 : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [hp0, if_false, isSquare_prime_pow_iff hp]

/-- **`λ = 1_{squares} * μ`.** -/
theorem sqIndA_mul_moebius : sqIndA * (↑μ : ArithmeticFunction ℂ) = ↑liouville := by
  rw [← liouville_mul_zeta, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]

/-- The pointwise form the hyperbola identity needs. -/
theorem liouville_eq_sum_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, sqIndA d * ((μ (n / d) : ℤ) : ℂ) = ((liouville n : ℤ) : ℂ) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) sqIndA_mul_moebius
  simp only [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (f := fun d e => sqIndA d * (↑μ : ArithmeticFunction ℂ) e)] at h
  simpa [intCoe_apply] using h


/-! ### The cited classical input, and stage A -/

/-- Mertens' function `M(N) = ∑_{n ≤ N} μ(n)`. -/
def moebiusSum (N : ℕ) : ℤ := ∑ n ∈ Finset.Ioc 0 N, μ n

/-- **The cited classical input**: `M(N) = o(N)` (Landau 1911).  This is *equivalent* to the prime
number theorem, which is itself in this tree (`PNTPort.MediumPNT`); the deduction
`ψ(x) ∼ x ⟹ M(x) = o(x)` is Axer's theorem and is the remaining debt of this route.  It is a
hypothesis, never an axiom (house style). -/
def MoebiusMeanZero : Prop :=
  Tendsto (fun N : ℕ => (moebiusSum N : ℝ) / (N : ℝ)) atTop (𝓝 0)

/-- `M` in `ℂ`, the `A` of the transfer engine. -/
noncomputable def moebiusSumC (N : ℕ) : ℂ := ∑ e ∈ Finset.Ioc 0 N, ((μ e : ℤ) : ℂ)

lemma moebiusSumC_eq (N : ℕ) : moebiusSumC N = ((moebiusSum N : ℤ) : ℂ) := by
  rw [moebiusSumC, moebiusSum]
  push_cast
  rfl

lemma norm_moebiusSumC_le (N : ℕ) : ‖moebiusSumC N‖ ≤ (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ e ∈ Finset.Ioc 0 N, ‖((μ e : ℤ) : ℂ)‖ ≤ 1 := by
    intro e _
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp

/-- The kernel `1_{squares}` is summable against `1/d`: `∑_{d square} 1/d = ∑_m 1/m²`. -/
lemma summable_sqIndA : Summable fun d : ℕ => ‖sqIndA d‖ / (d : ℝ) := by
  have hinj : Function.Injective fun m : ℕ => m ^ 2 := fun a b h => by
    simpa using Nat.pow_left_injective (by norm_num) h
  have hzero : ∀ d ∉ Set.range (fun m : ℕ => m ^ 2), ‖sqIndA d‖ / (d : ℝ) = 0 := by
    intro d hd
    have : ¬ IsSquare d := by
      rintro ⟨c, hc⟩
      exact hd ⟨c, by rw [hc]; ring⟩
    simp [sqIndA_apply, this]
  rw [← hinj.summable_iff hzero]
  have heq : (fun m : ℕ => ‖sqIndA (m ^ 2)‖ / ((m ^ 2 : ℕ) : ℝ))
      = fun m : ℕ => 1 / ((m : ℝ) ^ 2) := by
    funext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have h1 : (m ^ 2 : ℕ) ≠ 0 := pow_ne_zero _ hm
      have h2 : IsSquare (m ^ 2 : ℕ) := ⟨m, by ring⟩
      rw [sqIndA_apply, if_neg h1, if_pos h2]
      push_cast
      simp
  rw [Function.comp_def, heq]
  exact Real.summable_one_div_nat_pow.mpr one_lt_two

/-- **The hyperbola identity for `λ`.** -/
theorem sum_liouville_eq (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((liouville n : ℤ) : ℂ)
      = ∑ d ∈ Finset.Ioc 0 N, sqIndA d * moebiusSumC (N / d) := by
  have hpt : ∀ n ∈ Finset.Ioc 0 N, ((liouville n : ℤ) : ℂ)
      = ∑ d ∈ n.divisors, sqIndA d * ((μ (n / d) : ℤ) : ℂ) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    exact (liouville_eq_sum_divisors n).symm
  rw [Finset.sum_congr rfl hpt]
  exact sum_conv_eq sqIndA (fun e => ((μ e : ℤ) : ℂ)) N

/-- **Stage A.**  `M(N) = o(N)` forces the Liouville mean to vanish:
`(1/N) ∑_{n ≤ N} λ(n) → 0`. -/
theorem liouvilleMean_of_moebius (hM : MoebiusMeanZero) :
    Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.Ioc 0 N, ((liouville n : ℤ) : ℂ)‖ / (N : ℝ))
      atTop (𝓝 0) := by
  have hA : Tendsto (fun n : ℕ => ‖moebiusSumC n‖ / (n : ℝ)) atTop (𝓝 0) := by
    have h := hM.abs
    simp only [abs_zero] at h
    refine h.congr fun n => ?_
    rw [moebiusSumC_eq, Complex.norm_intCast, abs_div, Nat.abs_cast]
  have := kernelSum_tendsto_zero sqIndA moebiusSumC summable_sqIndA norm_moebiusSumC_le hA
  refine this.congr fun N => ?_
  rw [sum_liouville_eq N]


/-! ### Stage B: `(−1)^ω = λ * k`, with `k` supported on powerful numbers

`λ^{-1} = 1_{squarefree}` (local factors `(1+X)^{-1}·(1+X) = 1`), so the kernel is simply
`k = (−1)^ω * 1_{squarefree}`, whose prime-power values are `k(1) = 1`, `k(p) = 0`,
`k(p^j) = −2` for `j ≥ 2`. -/

/-- `(−1)^{ω(n)}`, as an arithmetic function. -/
noncomputable def omegaSignA : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (-1 : ℂ) ^ omegaNat n, by simp⟩

lemma omegaSignA_apply (n : ℕ) :
    omegaSignA n = if n = 0 then 0 else (-1 : ℂ) ^ omegaNat n := rfl

/-- The indicator of the squarefree numbers. -/
noncomputable def sqfreeIndA : ArithmeticFunction ℂ :=
  ⟨fun n => if Squarefree n then 1 else 0, by simp⟩

lemma sqfreeIndA_apply (n : ℕ) : sqfreeIndA n = if Squarefree n then 1 else 0 := rfl

lemma isMultiplicative_omegaSignA : omegaSignA.IsMultiplicative := by
  constructor
  · simp [omegaSignA_apply, omegaNat]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [omegaSignA_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [omegaSignA_apply]
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
    have hom : omegaNat (m * n) = omegaNat m + omegaNat n := by
      rw [omegaNat, omegaNat, omegaNat, Nat.primeFactors_mul hm hn,
        Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hmn)]
    simp only [omegaSignA_apply, hm, hn, hmn0, if_false, hom, pow_add]

lemma isMultiplicative_sqfreeIndA : sqfreeIndA.IsMultiplicative := by
  constructor
  · simp [sqfreeIndA_apply]
  · intro m n hmn
    simp only [sqfreeIndA_apply]
    by_cases h : Squarefree (m * n)
    · have h1 : Squarefree m := (Nat.squarefree_mul_iff.mp h).2.1
      have h2 : Squarefree n := (Nat.squarefree_mul_iff.mp h).2.2
      simp [h, h1, h2]
    · have hno : ¬ (Squarefree m ∧ Squarefree n) := fun ⟨h1, h2⟩ =>
        h (Nat.squarefree_mul hmn |>.mpr ⟨h1, h2⟩)
      rcases Classical.em (Squarefree m) with h1 | h1
      · have h2 : ¬ Squarefree n := fun hh => hno ⟨h1, hh⟩
        simp [h, h1, h2]
      · simp [h, h1]

/-- Evaluation of a convolution at a prime power. -/
lemma mul_apply_prime_pow (f g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (f * g) (p ^ i) = ∑ j ∈ Finset.range (i + 1), f (p ^ j) * g (p ^ (i - j)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun d e => f d * g e),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [Nat.pow_div (by omega) hp.pos]

/-- **`λ * 1_{squarefree} = 1`** — the Dirichlet inverse of Liouville's function is the
squarefree indicator. -/
theorem liouville_mul_sqfreeInd : (↑liouville : ArithmeticFunction ℂ) * sqfreeIndA = 1 := by
  have hmulL : (↑liouville : ArithmeticFunction ℂ).IsMultiplicative :=
    isMultiplicative_liouville.intCast
  have hmul : ((↑liouville : ArithmeticFunction ℂ) * sqfreeIndA).IsMultiplicative :=
    hmulL.mul isMultiplicative_sqfreeIndA
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    ArithmeticFunction.isMultiplicative_one]
  intro p i hp
  rw [mul_apply_prime_pow _ _ hp]
  have hL : ∀ j : ℕ, (↑liouville : ArithmeticFunction ℂ) (p ^ j) = (-1 : ℂ) ^ j := by
    intro j
    rw [intCoe_apply, liouville_apply (pow_ne_zero _ hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp]
    push_cast; ring
  have hS : ∀ j : ℕ, sqfreeIndA (p ^ j) = if j ≤ 1 then (if j = 0 then 1 else 1) else 0 := by
    intro j
    rw [sqfreeIndA_apply]
    by_cases hj : j ≤ 1
    · interval_cases j
      · simp
      · simp [hp.squarefree]
    · have : ¬ Squarefree (p ^ j) := by
        intro hsq
        have := Nat.squarefree_pow_iff hp.ne_one (by omega) |>.mp hsq
        omega
      simp [this, hj]
  simp only [hL, hS]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have hone : (1 : ArithmeticFunction ℂ) (p ^ i) = 0 := by
      rw [ArithmeticFunction.one_apply]
      have hne : p ^ i ≠ 1 := (Nat.one_lt_pow (by omega) hp.one_lt).ne'
      exact if_neg hne
    rw [hone]
    -- only `i - j ≤ 1`, i.e. `j = i` or `j = i - 1`, contributes
    rw [Finset.sum_eq_add_of_mem (a := i - 1) (b := i)
      (by simp only [Finset.mem_range]; omega) (by simp only [Finset.mem_range]; omega)
      (by omega) (fun j hj hjne => ?_)]
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have h1 : m + 1 - (m + 1 - 1) = 1 := by omega
      have h2 : m + 1 - (m + 1) = 0 := by omega
      have h3 : m + 1 - 1 = m := by omega
      rw [h1, h2, h3, pow_succ]
      norm_num
    · simp only [Finset.mem_range] at hj
      have hj1 : ¬ (i - j ≤ 1) := by
        obtain ⟨h1, h2⟩ := hjne
        omega
      simp [hj1]


/-! ### The arithmetic toolbox for stage B's kernel -/

/-- `2^{ω(m)} ≤ m`: the radical divides `m` and is a product of `ω(m)` primes, each `≥ 2`. -/
lemma two_pow_omega_le_self {m : ℕ} (hm : m ≠ 0) : 2 ^ omegaNat m ≤ m := by
  calc 2 ^ omegaNat m = ∏ _p ∈ m.primeFactors, 2 := by
        rw [Finset.prod_const, omegaNat]
    _ ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/-- `2^{ω(m)} ≤ d(m)`: each prime contributes a factor `k_p + 1 ≥ 2` to the divisor count. -/
lemma two_pow_omega_le_card_divisors {m : ℕ} (hm : m ≠ 0) :
    2 ^ omegaNat m ≤ #m.divisors := by
  rw [Nat.card_divisors hm]
  calc 2 ^ omegaNat m = ∏ _p ∈ m.primeFactors, 2 := by
        rw [Finset.prod_const, omegaNat]
    _ ≤ ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
        refine Finset.prod_le_prod' fun p hp => ?_
        have := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hm
          (Nat.dvd_of_mem_primeFactors hp)
        omega
    _ = m.primeFactors.prod (m.factorization · + 1) := rfl

/-- `∑_{u ≤ N} 1/u²` is bounded by its total. -/
lemma sum_inv_sq_le (N : ℕ) :
    ∑ u ∈ Finset.Ioc 0 N, 1 / ((u : ℝ)) ^ 2 ≤ ∑' u : ℕ, 1 / ((u : ℝ)) ^ 2 := by
  refine (Real.summable_one_div_nat_pow.mpr one_lt_two).sum_le_tsum _ (fun u _ => by positivity)

lemma summable_inv_sq : Summable fun u : ℕ => 1 / ((u : ℝ)) ^ 2 :=
  Real.summable_one_div_nat_pow.mpr one_lt_two

/-- **`∑_c d(c)/c² < ∞`**, by the hyperbola identity: the sum is `(∑_u 1/u²)²`. -/
lemma summable_divisorCard : Summable fun c : ℕ => (#c.divisors : ℝ) / ((c : ℝ)) ^ 2 := by
  set K : ℝ := ∑' u : ℕ, 1 / ((u : ℝ)) ^ 2 with hKdef
  have hK0 : 0 ≤ K := tsum_nonneg fun u => by positivity
  refine summable_of_sum_range_le (c := K * K) (fun c => by positivity) fun N => ?_
  have hsub : Finset.range N ⊆ insert 0 (Finset.Ioc 0 N) := by
    intro c hc
    simp only [Finset.mem_range] at hc
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hrange : ∑ c ∈ Finset.range N, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2
      ≤ ∑ c ∈ Finset.Ioc 0 N, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2 := by
    calc ∑ c ∈ Finset.range N, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2
        ≤ ∑ c ∈ insert 0 (Finset.Ioc 0 N), (#c.divisors : ℝ) / ((c : ℝ)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => by positivity)
      _ = ∑ c ∈ Finset.Ioc 0 N, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2 := by
          rw [Finset.sum_insert (by simp)]
          simp
  refine le_trans hrange ?_
  have hpt : ∀ c ∈ Finset.Ioc 0 N, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2
      = ∑ d ∈ c.divisors, (1 / ((d : ℝ)) ^ 2) * (1 / ((c / d : ℕ) : ℝ) ^ 2) := by
    intro c hc
    simp only [Finset.mem_Ioc] at hc
    have hterm : ∀ d ∈ c.divisors,
        (1 / ((d : ℝ)) ^ 2) * (1 / ((c / d : ℕ) : ℝ) ^ 2) = 1 / ((c : ℝ)) ^ 2 := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hd.2 (zero_dvd_iff.mp hd.1)
      have hcd : ((d : ℝ)) * ((c / d : ℕ) : ℝ) = (c : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hd.1]
      rw [div_mul_div_comm, one_mul, ← mul_pow, hcd]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hpt,
    sum_conv_eq (fun d => 1 / ((d : ℝ)) ^ 2) (fun e => 1 / ((e : ℝ)) ^ 2) N]
  calc ∑ d ∈ Finset.Ioc 0 N, (1 / ((d : ℝ)) ^ 2) * ∑ e ∈ Finset.Ioc 0 (N / d), 1 / ((e : ℝ)) ^ 2
      ≤ ∑ d ∈ Finset.Ioc 0 N, (1 / ((d : ℝ)) ^ 2) * K := by
        refine Finset.sum_le_sum fun d _ => ?_
        exact mul_le_mul_of_nonneg_left (sum_inv_sq_le _) (by positivity)
    _ = (∑ d ∈ Finset.Ioc 0 N, 1 / ((d : ℝ)) ^ 2) * K := by rw [Finset.sum_mul]
    _ ≤ K * K := mul_le_mul_of_nonneg_right (sum_inv_sq_le N) hK0


/-! ### The powerful-number parametrisation `n = a³c²` -/

/-- `n` is powerful: every prime dividing it divides it twice. -/
def IsPowerfulN (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- **Every powerful number is `a³c²`.**  Take the maximal square divisor `b²` of `n`, so
`n = b²a` with `a` squarefree; powerfulness forces every prime of `a` to divide `b`, hence
`a ∣ b` and `b = ac`. -/
theorem exists_cube_sq_of_powerful {n : ℕ} (hn : n ≠ 0) (hpow : IsPowerfulN n) :
    ∃ a c : ℕ, 0 < a ∧ 0 < c ∧ n = a ^ 3 * c ^ 2 := by
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree n
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; omega
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; omega
  -- every prime of `a` divides `b`
  have hdvd : a ∣ b := by
    rw [← Nat.factorization_le_iff_dvd ha0 hb0]
    intro p
    rcases Nat.eq_zero_or_pos (a.factorization p) with h | h
    · simp [h]
    · have hp : p.Prime := by
        by_contra hcon
        rw [Nat.factorization_eq_zero_of_not_prime a hcon] at h
        omega
      have hpa : p ∣ a := Nat.dvd_of_factorization_pos (by omega)
      have hpn : p ∣ n := hab ▸ Dvd.dvd.mul_left hpa _
      have hp2 : p ^ 2 ∣ n := hpow p hp hpn
      have ha1 : a.factorization p = 1 := by
        have := (Nat.squarefree_iff_factorization_le_one ha0).mp hsq p
        omega
      have hnf : n.factorization p = 2 * b.factorization p + a.factorization p := by
        rw [← hab, Nat.factorization_mul (pow_ne_zero _ hb0) ha0]
        simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      have h2 : 2 ≤ n.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp hp2
      have hbpos : 1 ≤ b.factorization p := by omega
      simp only [ha1]
      omega
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · simp [hc] at hb0
    · exact h
  refine ⟨a, c, Nat.pos_of_ne_zero ha0, hc0, ?_⟩
  rw [← hab, hc]
  ring

/-- Primes of `a³c²` are primes of `a` or of `c`, so `ω` is subadditive along the
parametrisation. -/
lemma omega_cube_sq_le {a c : ℕ} (ha : 0 < a) (hc : 0 < c) :
    omegaNat (a ^ 3 * c ^ 2) ≤ omegaNat a + omegaNat c := by
  have h : (a ^ 3 * c ^ 2).primeFactors = a.primeFactors ∪ c.primeFactors := by
    rw [Nat.primeFactors_mul (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)),
      Nat.primeFactors_pow _ (by omega), Nat.primeFactors_pow _ (by omega)]
  rw [omegaNat, omegaNat, omegaNat, h]
  exact Finset.card_union_le _ _


/-! ### The stage-B kernel `k = (−1)^ω * 1_{squarefree}` -/

/-- The stage-B kernel.  `k(1) = 1`, `k(p) = 0`, `k(p^j) = −2` for `j ≥ 2`. -/
noncomputable def kA : ArithmeticFunction ℂ := omegaSignA * sqfreeIndA

lemma isMultiplicative_kA : kA.IsMultiplicative :=
  isMultiplicative_omegaSignA.mul isMultiplicative_sqfreeIndA

/-- **`(−1)^ω = λ * k`.** -/
theorem liouville_mul_kA : (↑liouville : ArithmeticFunction ℂ) * kA = omegaSignA := by
  rw [kA, mul_left_comm, liouville_mul_sqfreeInd, mul_one]

lemma omegaSignA_prime_pow {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : 1 ≤ j) :
    omegaSignA (p ^ j) = -1 := by
  have h0 : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hom : omegaNat (p ^ j) = 1 := by
    rw [omegaNat, Nat.primeFactors_pow _ (by omega), Nat.Prime.primeFactors hp,
      Finset.card_singleton]
  rw [omegaSignA_apply, if_neg h0, hom, pow_one]

/-- The kernel's prime-power values. -/
lemma kA_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    kA (p ^ i) = if i = 0 then 1 else if i = 1 then 0 else -2 := by
  rw [kA, mul_apply_prime_pow _ _ hp]
  have hS : ∀ j : ℕ, sqfreeIndA (p ^ j) = if j ≤ 1 then 1 else 0 := by
    intro j
    rw [sqfreeIndA_apply]
    by_cases hj : j ≤ 1
    · interval_cases j
      · simp
      · simp [hp.squarefree]
    · have hns : ¬ Squarefree (p ^ j) := by
        intro hsq
        have := Nat.squarefree_pow_iff hp.ne_one (by omega) |>.mp hsq
        omega
      simp [hns, hj]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [omegaSignA_apply, sqfreeIndA_apply, omegaNat]
  rcases eq_or_ne i 1 with rfl | hi1
  · rw [if_neg (by omega), if_pos rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [hS, pow_zero, omegaSignA_prime_pow hp le_rfl]
    norm_num
    rw [omegaSignA_apply]
    norm_num [omegaNat]
  · rw [if_neg (by omega), if_neg hi1]
    have hi2 : 2 ≤ i := by omega
    rw [Finset.sum_eq_add_of_mem (a := i - 1) (b := i)
      (by simp only [Finset.mem_range]; omega) (by simp only [Finset.mem_range]; omega)
      (by omega) (fun j hj hjne => ?_)]
    · have h1 : i - (i - 1) = 1 := by omega
      have h2 : i - i = 0 := by omega
      rw [h1, h2, omegaSignA_prime_pow hp (by omega), omegaSignA_prime_pow hp (by omega)]
      simp only [hS]
      norm_num
    · obtain ⟨hja, hjb⟩ := hjne
      have hj1 : ¬ (i - j ≤ 1) := by
        simp only [Finset.mem_range] at hj
        omega
      simp [hS, hj1]

lemma norm_kA_prime_pow_le {p : ℕ} (hp : p.Prime) (i : ℕ) : ‖kA (p ^ i)‖ ≤ 2 := by
  rw [kA_prime_pow hp]
  split
  · norm_num
  · split <;> norm_num

/-- `‖k(n)‖ ≤ 2^{ω(n)}`. -/
lemma norm_kA_le {n : ℕ} (hn : n ≠ 0) : ‖kA n‖ ≤ 2 ^ omegaNat n := by
  rw [isMultiplicative_kA.multiplicative_factorization _ hn, Finsupp.prod,
    Nat.support_factorization]
  calc ‖∏ p ∈ n.primeFactors, kA (p ^ n.factorization p)‖
      = ∏ p ∈ n.primeFactors, ‖kA (p ^ n.factorization p)‖ := by
        rw [norm_prod]
    _ ≤ ∏ _p ∈ n.primeFactors, (2 : ℝ) :=
        Finset.prod_le_prod (fun p _ => norm_nonneg _)
          (fun p hp => norm_kA_prime_pow_le (Nat.prime_of_mem_primeFactors hp) _)
    _ = 2 ^ omegaNat n := by rw [Finset.prod_const, omegaNat]

/-- The kernel vanishes off the powerful numbers. -/
lemma kA_eq_zero_of_not_powerful {n : ℕ} (hn : ¬ IsPowerfulN n) : kA n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rw [IsPowerfulN] at hn
  simp only [not_forall] at hn
  obtain ⟨p, hp, hpn, hp2⟩ := hn
  have hfac : n.factorization p = 1 := by
    have h1 : 1 ≤ n.factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).mp (by simpa using hpn)
    have h2 : ¬ (2 ≤ n.factorization p) := fun h =>
      hp2 ((Nat.Prime.pow_dvd_iff_le_factorization hp hn0).mpr h)
    omega
  rw [isMultiplicative_kA.multiplicative_factorization _ hn0, Finsupp.prod,
    Nat.support_factorization]
  refine Finset.prod_eq_zero (i := p) ?_ ?_
  · rw [Nat.mem_primeFactors]
    exact ⟨hp, hpn, hn0⟩
  · rw [hfac, kA_prime_pow hp]
    norm_num


/-! ### The kernel is summable against `1/n` -/

/-- The parametrisation, phrased so that it always exists (trivially when `n` is not powerful). -/
lemma exists_cubeSqRep (n : ℕ) :
    ∃ q : ℕ × ℕ, 0 < q.1 ∧ 0 < q.2 ∧ (n ≠ 0 → IsPowerfulN n → n = q.1 ^ 3 * q.2 ^ 2) := by
  by_cases h : n ≠ 0 ∧ IsPowerfulN n
  · obtain ⟨a, c, ha, hc, heq⟩ := exists_cube_sq_of_powerful h.1 h.2
    exact ⟨(a, c), ha, hc, fun _ _ => heq⟩
  · refine ⟨(1, 1), one_pos, one_pos, fun h1 h2 => ?_⟩
    exact absurd ⟨h1, h2⟩ h

/-- A choice of parametrisation `n = a³c²` for powerful `n`. -/
noncomputable def cubeSqParam (n : ℕ) : ℕ × ℕ := (exists_cubeSqRep n).choose

lemma cubeSqParam_pos (n : ℕ) : 0 < (cubeSqParam n).1 ∧ 0 < (cubeSqParam n).2 :=
  ⟨(exists_cubeSqRep n).choose_spec.1, (exists_cubeSqRep n).choose_spec.2.1⟩

lemma cubeSqParam_eq {n : ℕ} (hn : n ≠ 0) (hpow : IsPowerfulN n) :
    n = (cubeSqParam n).1 ^ 3 * (cubeSqParam n).2 ^ 2 :=
  (exists_cubeSqRep n).choose_spec.2.2 hn hpow

/-- The single-term bound along a parametrisation `n = a³c²`. -/
lemma kA_term_bound {n a c : ℕ} (hn0 : n ≠ 0) (ha : 0 < a) (hc : 0 < c)
    (heq : n = a ^ 3 * c ^ 2) :
    ‖kA n‖ / (n : ℝ) ≤ (1 / ((a : ℝ)) ^ 2) * ((#c.divisors : ℝ) / ((c : ℝ)) ^ 2) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have h1 : ‖kA n‖ ≤ (a : ℝ) * (#c.divisors : ℝ) := by
    refine le_trans (norm_kA_le hn0) ?_
    have h2 : omegaNat n ≤ omegaNat a + omegaNat c := by
      rw [heq]; exact omega_cube_sq_le ha hc
    have h4 : (2 : ℝ) ^ omegaNat a ≤ (a : ℝ) := by
      exact_mod_cast two_pow_omega_le_self (by omega : a ≠ 0)
    have h5 : (2 : ℝ) ^ omegaNat c ≤ (#c.divisors : ℝ) := by
      exact_mod_cast two_pow_omega_le_card_divisors (by omega : c ≠ 0)
    calc (2 : ℝ) ^ omegaNat n ≤ 2 ^ (omegaNat a + omegaNat c) :=
          pow_le_pow_right₀ (by norm_num) h2
      _ = 2 ^ omegaNat a * 2 ^ omegaNat c := by rw [pow_add]
      _ ≤ (a : ℝ) * (#c.divisors : ℝ) := mul_le_mul h4 h5 (by positivity) (by positivity)
  have hnval : (n : ℝ) = (a : ℝ) ^ 3 * (c : ℝ) ^ 2 := by rw [heq]; push_cast; ring
  rw [hnval, div_le_iff₀ (by positivity)]
  calc ‖kA n‖ ≤ (a : ℝ) * (#c.divisors : ℝ) := h1
    _ = 1 / ((a : ℝ)) ^ 2 * ((#c.divisors : ℝ) / ((c : ℝ)) ^ 2) * ((a : ℝ) ^ 3 * (c : ℝ) ^ 2) := by
        field_simp

/-- The parameters are bounded by `n`. -/
lemma cubeSq_param_le {n a c : ℕ} (ha : 0 < a) (hc : 0 < c) (heq : n = a ^ 3 * c ^ 2) :
    a ≤ n ∧ c ≤ n := by
  constructor
  · rw [heq]
    calc a ≤ a ^ 3 := Nat.le_self_pow (by omega) _
      _ ≤ a ^ 3 * c ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  · rw [heq]
    calc c ≤ c ^ 2 := Nat.le_self_pow (by omega) _
      _ ≤ a ^ 3 * c ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)

/-- **`∑_n ‖k(n)‖/n < ∞`.**  The kernel lives on the powerful numbers, and along `n = a³c²` the
bound `‖k(n)‖ ≤ 2^{ω(a)}·2^{ω(c)} ≤ a·d(c)` turns the term into `(1/a²)·(d(c)/c²)`, a product of
two convergent series. -/
theorem summable_kA : Summable fun n : ℕ => ‖kA n‖ / (n : ℝ) := by
  classical
  set K₁ : ℝ := ∑' a : ℕ, 1 / ((a : ℝ)) ^ 2 with hK₁
  set K₂ : ℝ := ∑' c : ℕ, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2 with hK₂
  have hK₁0 : 0 ≤ K₁ := tsum_nonneg fun a => by positivity
  have hK₂0 : 0 ≤ K₂ := tsum_nonneg fun c => by positivity
  have hK₂le : ∀ M : ℕ, ∑ c ∈ Finset.Ioc 0 M, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2 ≤ K₂ := fun M =>
    summable_divisorCard.sum_le_tsum _ (fun c _ => by positivity)
  set R : ℕ × ℕ → ℝ := fun q => (1 / ((q.1 : ℝ)) ^ 2) * ((#q.2.divisors : ℝ) / ((q.2 : ℝ)) ^ 2)
    with hR
  have hR0 : ∀ q : ℕ × ℕ, 0 ≤ R q := fun q => by rw [hR]; positivity
  refine summable_of_sum_range_le (c := K₁ * K₂) (fun n => by positivity) fun N => ?_
  set P : ℕ → Prop := fun n => n ≠ 0 ∧ IsPowerfulN n with hP
  set F : Finset ℕ := Finset.filter P (Finset.range N) with hF
  have hfilter : ∑ n ∈ Finset.range N, ‖kA n‖ / (n : ℝ) = ∑ n ∈ F, ‖kA n‖ / (n : ℝ) := by
    refine (Finset.sum_filter_of_ne fun n _ hne => ?_).symm
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [Nat.cast_zero, div_zero] at hne
      exact absurd rfl hne
    · by_contra hcon
      rw [kA_eq_zero_of_not_powerful hcon, norm_zero, zero_div] at hne
      exact absurd rfl hne
  have hmemF : ∀ n ∈ F, n ≠ 0 ∧ IsPowerfulN n := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hinj : ∀ m ∈ F, ∀ n ∈ F, cubeSqParam m = cubeSqParam n → m = n := by
    intro m hm n hn hmn
    obtain ⟨hm1, hm2⟩ := hmemF m hm
    obtain ⟨hn1, hn2⟩ := hmemF n hn
    rw [cubeSqParam_eq hm1 hm2, cubeSqParam_eq hn1 hn2, hmn]
  have hsub : F.image cubeSqParam ⊆ (Finset.Ioc 0 N) ×ˢ (Finset.Ioc 0 N) := by
    intro q hq
    obtain ⟨n, hnF, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hn1, hn2⟩ := hmemF n hnF
    have hnN : n < N := Finset.mem_range.mp (Finset.mem_filter.mp hnF).1
    obtain ⟨ha, hc⟩ := cubeSqParam_pos n
    obtain ⟨h1, h2⟩ := cubeSq_param_le ha hc (cubeSqParam_eq hn1 hn2)
    rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc]
    exact ⟨⟨ha, by omega⟩, ⟨hc, by omega⟩⟩
  rw [hfilter]
  calc ∑ n ∈ F, ‖kA n‖ / (n : ℝ)
      ≤ ∑ n ∈ F, R (cubeSqParam n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hn1, hn2⟩ := hmemF n hn
        obtain ⟨ha, hc⟩ := cubeSqParam_pos n
        rw [hR]
        exact kA_term_bound hn1 ha hc (cubeSqParam_eq hn1 hn2)
    _ = ∑ q ∈ F.image cubeSqParam, R q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ (Finset.Ioc 0 N) ×ˢ (Finset.Ioc 0 N), R q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hR0 q)
    _ = (∑ a ∈ Finset.Ioc 0 N, 1 / ((a : ℝ)) ^ 2)
          * (∑ c ∈ Finset.Ioc 0 N, (#c.divisors : ℝ) / ((c : ℝ)) ^ 2) := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ K₁ * K₂ :=
        mul_le_mul (sum_inv_sq_le N) (hK₂le N)
          (Finset.sum_nonneg fun c _ => by positivity) hK₁0


/-! ### Stage B and the payoff: `DelangeMean (1/2)` from Möbius -/

/-- The pointwise form of `(−1)^ω = k * λ`. -/
theorem omegaSignA_eq_sum_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, kA d * ((liouville (n / d) : ℤ) : ℂ) = omegaSignA n := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (mul_comm (↑liouville : ArithmeticFunction ℂ) kA ▸ liouville_mul_kA)
  simp only [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (f := fun d e => kA d * (↑liouville : ArithmeticFunction ℂ) e)]
    at h
  simpa [intCoe_apply] using h

/-- Partial sums of `λ`. -/
noncomputable def liouvilleSumC (N : ℕ) : ℂ := ∑ e ∈ Finset.Ioc 0 N, ((liouville e : ℤ) : ℂ)

lemma norm_liouvilleSumC_le (N : ℕ) : ‖liouvilleSumC N‖ ≤ (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ e ∈ Finset.Ioc 0 N, ‖((liouville e : ℤ) : ℂ)‖ ≤ 1 := by
    intro e he
    simp only [Finset.mem_Ioc] at he
    rw [liouville_apply (by omega : e ≠ 0)]
    push_cast
    simp [abs_pow]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp

/-- **The hyperbola identity for `(−1)^ω`.** -/
theorem sum_omegaSign_eq (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, omegaSignA n
      = ∑ d ∈ Finset.Ioc 0 N, kA d * liouvilleSumC (N / d) := by
  have hpt : ∀ n ∈ Finset.Ioc 0 N, omegaSignA n
      = ∑ d ∈ n.divisors, kA d * ((liouville (n / d) : ℤ) : ℂ) := fun n _ =>
    (omegaSignA_eq_sum_divisors n).symm
  rw [Finset.sum_congr rfl hpt]
  exact sum_conv_eq kA (fun e => ((liouville e : ℤ) : ℂ)) N

/-- **Stage B.**  `M(N) = o(N)` forces `∑_{n ≤ N} (−1)^{ω(n)} = o(N)`. -/
theorem omegaSignMean_of_moebius (hM : MoebiusMeanZero) :
    Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.Ioc 0 N, omegaSignA n‖ / (N : ℝ)) atTop (𝓝 0) := by
  have hA : Tendsto (fun n : ℕ => ‖liouvilleSumC n‖ / (n : ℝ)) atTop (𝓝 0) :=
    liouvilleMean_of_moebius hM
  have := kernelSum_tendsto_zero kA liouvilleSumC summable_kA norm_liouvilleSumC_le hA
  refine this.congr fun N => ?_
  rw [sum_omegaSign_eq N]

lemma phase_half : phase (1 / 2 : ℝ) = -1 := by
  rw [phase]
  have : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_pi_mul_I]

/-- **THE PAYOFF.**  `DelangeMean (1/2)` — the parity case, out of reach of the elementary
`‖phase t − 1‖ < 1` route (there `‖phase (1/2) − 1‖ = 2`) — follows from `M(N) = o(N)`, i.e. from
the prime number theorem.  No Selberg–Delange contour, no Halász. -/
theorem delangeMean_half_of_moebius (hM : MoebiusMeanZero) : DelangeMean (1 / 2 : ℝ) := by
  have hkey := omegaSignMean_of_moebius hM
  rw [DelangeMean, tendsto_zero_iff_norm_tendsto_zero]
  refine hkey.congr fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [fullMean]
  have hidx : ∑ n ∈ Finset.range N, phase ((1 / 2 : ℝ) * (omegaNat (n + 1) : ℝ))
      = ∑ m ∈ Finset.Ioc 0 N, omegaSignA m := by
    have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N + 1) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 1 + n = n + 1 by omega, omegaSignA_apply, if_neg (by omega : n + 1 ≠ 0),
      ← phase_half, ← phase_omegaNat_pow]
  rw [fullMean, hidx, norm_div, Complex.norm_natCast]

end NormalNumbers.CastingOut
