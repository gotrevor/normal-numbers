/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtElliottForm
import NormalNumbers.SwingC1
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The `ω → Ω` bridge: `z^ω = z^Ω ⋆ g` with `g` supported on the powerful numbers

Lap 4 found that the MRT / log-Elliott development in `lean-proofs-latest` cannot be applied to
this crux, because `Erdos67b.NonasymptoticLogElliott` requires
`IsCompletelyMultiplicativeOnPositive`, and `z^{ω}` is merely multiplicative (`ω(p²) = 1`, so
`z^{ω(p²)} = z ≠ z²`).  `z^{Ω}`, by contrast, IS completely multiplicative.

This file builds the bridge.  Solving `z^ω = z^Ω ⋆ g` for `g` at prime powers gives
`g(1) = 1`, `g(p) = 0`, and `g(p^k) = z − z²` for every `k ≥ 2`: so

    **`g` is supported exactly on the POWERFUL numbers, with `g(d) = (z−z²)^{ω(d)}`.**

Hence, for `m ≠ 0`,

    z^{ω(m)} = ∑_{d ∣ m, d powerful} (z−z²)^{ω(d)} · z^{Ω(m/d)}.

## Why this is the route back to log-Elliott

Substituting this into the `D`-point correlation
`∑_{n<N} e(jn/Q) ∏_{i<D} ζ_i^{ω(n+1+i)}` expands it as an absolutely convergent sum over
tuples `(d_0,…,d_{D−1})` of powerful numbers, of terms

    ∏_i (ζ_i − ζ_i²)^{ω(d_i)} · ∑_{n : d_i ∣ n+1+i} e(jn/Q) ∏_i ζ_i^{Ω((n+1+i)/d_i)} .

On each residue class `n ≡ a (mod lcm d_i)` the arguments `(n+1+i)/d_i` become genuine **linear
forms** `(L/d_i)k + (a+1+i)/d_i` in the progression variable `k`.  So each term is a `D`-point
correlation of the **completely multiplicative** `ζ_i^{Ω}` along `D` linear forms — exactly the
shape `NonasymptoticLogElliott` is stated for.  The tuple sum converges absolutely because

    ∑_{d powerful} |z−z²|^{ω(d)}/d ≤ ∏_p (1 + 2/(p(p−1))) < ∞,

so it truncates at `d_i ≤ Y` with a uniform `ε` tail (`tsum_powerfulWeight_div_lt_top`).

`Powerful` here is the standard notion: every prime dividing `n` divides it twice.
-/

open Finset ArithmeticFunction

namespace NormalNumbers

namespace CastingOut

/-- `n` is **powerful** (squarefull): every prime dividing `n` divides it to order `≥ 2`. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

noncomputable instance : DecidablePred Powerful := fun _ => Classical.dec _

lemma powerful_one : Powerful 1 := fun _p hp hd =>
  absurd (Nat.eq_one_of_dvd_one hd) hp.ne_one

lemma not_powerful_prime {p : ℕ} (hp : p.Prime) : ¬ Powerful p := by
  intro hP
  have := hP p hp dvd_rfl
  have h2 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos this
  have := hp.two_le
  nlinarith [h2]

lemma powerful_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : Powerful (p ^ k) := by
  intro q hq hqd
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
  subst hqp
  exact pow_dvd_pow q hk

/-- `Ω` as a complex power: completely multiplicative. -/
noncomputable def zOm (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else z ^ ArithmeticFunction.cardFactors n, by simp⟩

/-- `ω` as a complex power: multiplicative but not completely. -/
noncomputable def zom (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else z ^ omegaNat n, by simp⟩

/-- The bridging weight `g`, supported on the powerful numbers. -/
noncomputable def sqfW (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else if Powerful n then (z - z ^ 2) ^ omegaNat n else 0, by simp⟩

@[simp] lemma zOm_apply {z : ℂ} {n : ℕ} (hn : n ≠ 0) :
    zOm z n = z ^ ArithmeticFunction.cardFactors n := by rw [zOm]; simp [hn]

@[simp] lemma zom_apply {z : ℂ} {n : ℕ} (hn : n ≠ 0) :
    zom z n = z ^ omegaNat n := by rw [zom]; simp [hn]

lemma sqfW_apply {z : ℂ} {n : ℕ} (hn : n ≠ 0) :
    sqfW z n = if Powerful n then (z - z ^ 2) ^ omegaNat n else 0 := by rw [sqfW]; simp [hn]

@[simp] lemma sqfW_one {z : ℂ} : sqfW z 1 = 1 := by
  rw [sqfW_apply one_ne_zero, if_pos powerful_one]
  simp [omegaNat]

lemma sqfW_prime {z : ℂ} {p : ℕ} (hp : p.Prime) : sqfW z p = 0 := by
  rw [sqfW_apply hp.pos.ne', if_neg (not_powerful_prime hp)]

lemma sqfW_prime_pow {z : ℂ} {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    sqfW z (p ^ k) = z - z ^ 2 := by
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  rw [sqfW_apply hne, if_pos (powerful_prime_pow hp hk)]
  have hom : omegaNat (p ^ k) = 1 := by
    rw [omegaNat, Nat.primeFactors_prime_pow (by omega) hp]
    simp
  rw [hom, pow_one]

lemma omegaNat_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : omegaNat (p ^ k) = 1 := by
  rw [omegaNat, Nat.primeFactors_prime_pow (by omega) hp]
  simp

private lemma geom_tel (z : ℂ) (m : ℕ) :
    (z - z ^ 2) * ∑ j ∈ range m, z ^ j = z - z ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-! ### The prime-power identity -/

/-- **`z^ω = z^Ω ⋆ g` at prime powers.**  This is the whole computation: the geometric sum
`∑_{j=2}^{k} z^{k−j}(z − z²) = z − z^k` cancels the `z^k` from the `j = 0` term. -/
theorem zOm_mul_sqfW_prime_pow (z : ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (zOm z * sqfW z) (p ^ k) = zom z (p ^ k) := by
  have hpne : p ≠ 0 := hp.pos.ne'
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hpne
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => zOm z x * sqfW z y)]
  rw [Nat.sum_divisors_prime_pow hp]
  have hterm : ∀ j ∈ range (k + 1),
      zOm z (p ^ j) * sqfW z (p ^ k / p ^ j)
        = if j = k then z ^ j * 1 else if j = k - 1 then 0 else z ^ j * (z - z ^ 2) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hdiv : p ^ k / p ^ j = p ^ (k - j) := by
      rw [Nat.pow_div (by omega) hp.pos]
    rw [hdiv, zOm_apply (pow_ne_zero _ hpne)]
    have hOm : ArithmeticFunction.cardFactors (p ^ j) = j := by
      rw [ArithmeticFunction.cardFactors_apply_prime_pow hp]
    rw [hOm]
    by_cases hjk : j = k
    · subst hjk
      rw [Nat.sub_self, pow_zero, sqfW_one, if_pos rfl]
    · by_cases hjk1 : j = k - 1
      · have h1 : k - j = 1 := by omega
        rw [h1, pow_one, sqfW_prime hp, mul_zero, if_neg hjk, if_pos hjk1]
      · have h2 : 2 ≤ k - j := by omega
        rw [sqfW_prime_pow hp h2, if_neg hjk, if_neg hjk1]
  rw [Finset.sum_congr rfl hterm, zom_apply hpk]
  match k, hp with
  | 0, _ => simp [omegaNat]
  | 1, _ =>
      rw [Finset.sum_range_succ, Finset.sum_range_one, if_neg (by norm_num : (0 : ℕ) ≠ 1),
        if_pos (by norm_num : (0 : ℕ) = 1 - 1), if_pos rfl, omegaNat_prime_pow hp le_rfl]
      ring
  | (k + 2), _ =>
      have hk1 : k + 2 - 1 = k + 1 := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hhead : ∑ j ∈ range (k + 1),
          (if j = k + 2 then z ^ j * 1 else if j = k + 2 - 1 then 0 else z ^ j * (z - z ^ 2))
            = ∑ j ∈ range (k + 1), z ^ j * (z - z ^ 2) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hhead, if_neg (by omega : k + 1 ≠ k + 2), if_pos (by omega : k + 1 = k + 2 - 1),
        if_pos rfl, omegaNat_prime_pow hp (by omega)]
      have : ∑ j ∈ range (k + 1), z ^ j * (z - z ^ 2)
          = (z - z ^ 2) * ∑ j ∈ range (k + 1), z ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, geom_tel z (k + 1)]
      ring

/-! ### Multiplicativity, and the global identity -/

lemma omegaNat_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hco : Nat.Coprime m n) :
    omegaNat (m * n) = omegaNat m + omegaNat n := by
  rw [omegaNat, omegaNat, omegaNat, Nat.primeFactors_mul hm hn,
    Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hco)]

/-- Powerfulness is multiplicative on coprime factorisations. -/
lemma powerful_mul_iff {m n : ℕ} (hco : Nat.Coprime m n) :
    Powerful (m * n) ↔ Powerful m ∧ Powerful n := by
  constructor
  · intro hP
    refine ⟨fun p hp hpm => ?_, fun p hp hpn => ?_⟩
    · have h2 := hP p hp (hpm.mul_right n)
      have hpn : ¬ p ∣ n := fun hd => hp.one_lt.ne' (Nat.eq_one_of_dvd_one
        (hco ▸ Nat.dvd_gcd hpm hd))
      have hcop : Nat.Coprime (p ^ 2) n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn |>.pow_left 2
      exact (Nat.Coprime.dvd_of_dvd_mul_right hcop h2)
    · have h2 := hP p hp (hpn.mul_left m)
      have hpm : ¬ p ∣ m := fun hd => hp.one_lt.ne' (Nat.eq_one_of_dvd_one
        (hco ▸ Nat.dvd_gcd hd hpn))
      have hcop : Nat.Coprime (p ^ 2) m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm |>.pow_left 2
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop h2)
  · rintro ⟨hm, hn⟩ p hp hpmn
    rcases (Nat.Prime.dvd_mul hp).1 hpmn with hd | hd
    · exact (hm p hp hd).mul_right n
    · exact (hn p hp hd).mul_left m

theorem isMultiplicative_zOm (z : ℂ) : (zOm z).IsMultiplicative := by
  refine ⟨by simp [zOm], fun {m n} hco => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [zOm]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zOm]
  rw [zOm_apply (by positivity), zOm_apply hm, zOm_apply hn,
    ArithmeticFunction.cardFactors_mul hm hn, pow_add]

theorem isMultiplicative_zom (z : ℂ) : (zom z).IsMultiplicative := by
  refine ⟨by simp [zom, omegaNat], fun {m n} hco => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [zom]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zom]
  rw [zom_apply (by positivity), zom_apply hm, zom_apply hn,
    omegaNat_mul_of_coprime hm hn hco, pow_add]

theorem isMultiplicative_sqfW (z : ℂ) : (sqfW z).IsMultiplicative := by
  refine ⟨by simp, fun {m n} hco => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sqfW]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sqfW]
  rw [sqfW_apply (by positivity), sqfW_apply hm, sqfW_apply hn]
  by_cases hP : Powerful (m * n)
  · obtain ⟨hPm, hPn⟩ := (powerful_mul_iff hco).1 hP
    rw [if_pos hP, if_pos hPm, if_pos hPn, omegaNat_mul_of_coprime hm hn hco, pow_add]
  · rw [if_neg hP]
    by_cases hPm : Powerful m
    · by_cases hPn : Powerful n
      · exact absurd ((powerful_mul_iff hco).2 ⟨hPm, hPn⟩) hP
      · rw [if_neg hPn, mul_zero]
    · rw [if_neg hPm, zero_mul]

/-- **The bridge, as an identity of arithmetic functions.** -/
theorem zOm_mul_sqfW (z : ℂ) : zOm z * sqfW z = zom z :=
  (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_zOm z).mul (isMultiplicative_sqfW z)) _
    (isMultiplicative_zom z)).2 fun p i hp => zOm_mul_sqfW_prime_pow z hp i

/-- **The bridge, as a divisor sum.**  `z^{ω(m)} = ∑_{d ∣ m, d powerful} (z−z²)^{ω(d)} z^{Ω(m/d)}`.
This is what converts a correlation of the merely-multiplicative `z^ω` into an absolutely
convergent sum of correlations of the COMPLETELY multiplicative `z^Ω` along linear forms. -/
theorem pow_omegaNat_eq_sum_divisors (z : ℂ) {m : ℕ} (hm : m ≠ 0) :
    z ^ omegaNat m
      = ∑ d ∈ m.divisors, z ^ ArithmeticFunction.cardFactors d
          * (if Powerful (m / d) then (z - z ^ 2) ^ omegaNat (m / d) else 0) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f m) (zOm_mul_sqfW z)
  simp only [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (f := fun x y => zOm z x * sqfW z y)] at h
  rw [zom_apply hm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm := Nat.mem_divisors.1 hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hm (Nat.eq_zero_of_zero_dvd hdm.1)
  have hq0 : m / d ≠ 0 := Nat.div_ne_zero_iff.2 ⟨hd0, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm.1⟩
  rw [zOm_apply hd0, sqfW_apply hq0]

end CastingOut

end NormalNumbers
