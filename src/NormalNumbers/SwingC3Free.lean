/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3AddChar

/-!
# What is exactly free in `AddCharTail`, and where the content starts

`SwingC3AddChar.conjC3_of_addCharTail` reduces `ConjC3` to

`AddCharTail b : ∀ P Q j h, 0 < j < Q → (1/N) ∑_{n<N} e(jn/Q)·e(h·tailLarge P b n) → 0`.

This file pins the boundary between the free part and the content.

* **`addCharTail_h_eq_zero`** — the `h = 0` case is a geometric sum and is proved here.  So the
  whole content lives at `h ≠ 0`, i.e. in the tail factor, never in the character.
* **`card_modEq_sub_div_le`** and **`card_modEq_crt_sub_div_le`** — the *exact* finite-level
  statement: for any modulus, an arithmetic progression occupies its share of `[0,N)` up to an
  additive `1`, and for coprime moduli the two conditions combine by CRT with the same `O(1)`
  error.  Since every prime `> P` is coprime to `Q = ∏_{p ≤ P} p`, this is precisely the sense
  in which "large primes do not see small ones" is free.
* **`card_modEq_primes_sub_div_le`** — the same for a finite set of primes `> P` steering the
  residue of `n`, jointly with the class mod `Q`: density exactly `1/(Q·∏p)` with error `1`.

The gap this makes visible: the error is `O(1)` *per divisibility pattern*, and `tailLarge` is
not a function of boundedly many patterns — `E[∑_{p>K} c_p(n)] ≍ loglog N − loglog K`.  That is
the whole obstruction, and it is now a statement about how many patterns are needed, not about
whether each one decouples.
-/

open Filter Topology Finset Complex

namespace NormalNumbers

namespace CastingOut

open PrimeLambert

/-! ### The free part: `h = 0` -/

lemma ee_ne_one_of_lt {Q j : ℕ} (hQ : 0 < Q) (hj : 0 < j) (hjQ : j < Q) :
    ee ((((j : ℝ) / Q : ℝ)) : ℂ) ≠ 1 := by
  intro hcon
  obtain ⟨m, hm⟩ := ee_eq_one_iff_int.1 hcon
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have h0 : (0 : ℝ) < (j : ℝ) / Q := by
    have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    positivity
  have h1 : (j : ℝ) / Q < 1 := by
    rw [div_lt_one hQR]; exact_mod_cast hjQ
  rw [hm] at h0 h1
  have : (0 : ℤ) < m := by exact_mod_cast h0
  have : m < 1 := by exact_mod_cast h1
  omega

/-- **The `h = 0` case of `AddCharTail` is a geometric sum.**  Proved. -/
theorem addCharTail_h_eq_zero (b P Q j : ℕ) (hQ : 0 < Q) (hj : 0 < j) (hjQ : j < Q) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
        * ee (((((0 : ℤ)) : ℝ) * tailLarge P b n : ℝ) : ℂ)) / N) atTop (𝓝 0) := by
  set z : ℂ := ee ((((j : ℝ) / Q : ℝ)) : ℂ) with hz
  have hz1 : z ≠ 1 := ee_ne_one_of_lt hQ hj hjQ
  have hpow : ∀ n : ℕ, z ^ n = ee ((((j : ℝ) * n / Q : ℝ)) : ℂ) := by
    intro n
    rw [hz, ee, ee, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hterm : ∀ n : ℕ, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
      * ee (((((0 : ℤ)) : ℝ) * tailLarge P b n : ℝ) : ℂ) = z ^ n := by
    intro n
    rw [hpow n]
    norm_num [ee]
  have hsum : ∀ N : ℕ, ∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
      * ee (((((0 : ℤ)) : ℝ) * tailLarge P b n : ℝ) : ℂ) = (z ^ N - 1) / (z - 1) := by
    intro N
    simp only [hterm]
    exact geom_sum_eq hz1 N
  have hzn : ∀ N : ℕ, ‖z ^ N‖ = 1 := by
    intro N
    rw [hpow N, norm_ee_real]
  have hd : (0 : ℝ) < ‖z - 1‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero_of_ne hz1
  have hbound : ∀ N : ℕ, ‖(∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
      * ee (((((0 : ℤ)) : ℝ) * tailLarge P b n : ℝ) : ℂ)) / (N : ℂ)‖
      ≤ (2 / ‖z - 1‖) / N := by
    intro N
    rw [hsum N, norm_div, norm_div]
    have h1 : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hzn N, norm_one]; norm_num
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hNR : (0 : ℝ) < ‖((N : ℕ) : ℂ)‖ := by
        rw [Complex.norm_natCast]; exact_mod_cast hN
      have hNR' : ‖((N : ℕ) : ℂ)‖ = (N : ℝ) := Complex.norm_natCast N
      rw [hNR']
      have hNpos : (0 : ℝ) < (N : ℝ) := by rw [← hNR']; exact hNR
      rw [div_le_div_iff₀ hNpos hNpos]
      have hq : ‖z ^ N - 1‖ / ‖z - 1‖ ≤ 2 / ‖z - 1‖ := by gcongr
      nlinarith [hq, hNpos]
  exact squeeze_zero_norm hbound
    (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop)

/-! ### The free part: exact CRT at finite level -/

/-- An arithmetic progression occupies its share of `[0, N)` up to an additive `1`. -/
theorem card_modEq_sub_div_le {M : ℕ} (hM : 0 < M) (a N : ℕ) :
    |(((range N).filter (fun n => n ≡ a [MOD M])).card : ℝ) - (N : ℝ) / M| ≤ 1 := by
  classical
  have hcount : ((range N).filter (fun n => n ≡ a [MOD M])).card
      = N / M + if a % M < N % M then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card N hM a
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNe : (N : ℝ) = (M : ℝ) * ((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N M).symm
  have hdiv : (N : ℝ) / M = ((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) / M := by
    rw [hNe]; field_simp
  have hmod : (0 : ℝ) ≤ ((N % M : ℕ) : ℝ) / M ∧ ((N % M : ℕ) : ℝ) / M < 1 := by
    constructor
    · positivity
    · rw [div_lt_one hMR]
      exact_mod_cast Nat.mod_lt N hM
  rw [hcount, hdiv]
  push_cast
  by_cases h : a % M < N % M <;> simp only [h, if_true, if_false] <;> rw [abs_le] <;>
    constructor <;> push_cast <;> linarith [hmod.1, hmod.2]

/-- **Exact CRT at finite level.**  For coprime moduli the two congruences combine, and the
joint progression still occupies its share `1/(M·M')` up to an additive `1`. -/
theorem card_modEq_crt_sub_div_le {M M' : ℕ} (hM : 0 < M) (hM' : 0 < M')
    (hcop : Nat.Coprime M M') (a c N : ℕ) :
    ∃ e : ℕ, (∀ n : ℕ, (n ≡ a [MOD M] ∧ n ≡ c [MOD M']) ↔ n ≡ e [MOD M * M']) ∧
      |(((range N).filter (fun n => n ≡ a [MOD M] ∧ n ≡ c [MOD M'])).card : ℝ)
        - (N : ℝ) / (M * M')| ≤ 1 := by
  classical
  obtain ⟨e, he1, he2⟩ := Nat.chineseRemainder hcop a c
  have hiff : ∀ n : ℕ, (n ≡ a [MOD M] ∧ n ≡ c [MOD M']) ↔ n ≡ e [MOD M * M'] := by
    intro n
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.trans he1.symm, h2.trans he2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.trans he1, h2.trans he2⟩
  refine ⟨e, hiff, ?_⟩
  have hfilt : (range N).filter (fun n => n ≡ a [MOD M] ∧ n ≡ c [MOD M'])
      = (range N).filter (fun n => n ≡ e [MOD M * M']) := by
    apply Finset.filter_congr
    intro n _
    exact hiff n
  rw [hfilt]
  have := card_modEq_sub_div_le (M := M * M') (by positivity) e N
  push_cast at this ⊢
  exact this

/-- Every prime `> P` is coprime to a modulus all of whose prime factors are `≤ P`; hence so is
any product of such primes. -/
theorem coprime_prod_primes_gt {P Q : ℕ} (hQP : ∀ p, p.Prime → p ∣ Q → p ≤ P)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ P < p) : Nat.Coprime Q (∏ p ∈ S, p) := by
  classical
  refine Nat.Coprime.prod_right fun p hp => ?_
  obtain ⟨hpp, hpP⟩ := hS p hp
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun hdvd => ?_)
  have := hQP p hpp hdvd
  omega

/-- **"Large primes do not see small ones" — the exact statement, and it is free.**  Let every
prime factor of `Q` be `≤ P` and let `D` be any product of primes `> P`.  Then the class mod `Q`
and any divisibility pattern mod `D` are jointly equidistributed in `[0, N)`, with density
*exactly* `1/(Q·D)` and error at most `1` — no sieve, no level of distribution, no asymptotics.

This is the whole of what the Chinese remainder theorem gives Leaf B.  The obstruction is that
`tailLarge P b n` is not a function of boundedly many such patterns: the error is `O(1)` per
pattern and `E_n[∑_{p>K} c_p(n)] ≍ loglog N − loglog K` patterns are needed. -/
theorem card_modEq_class_pattern_sub_div_le {P Q : ℕ} (hQ : 0 < Q)
    (hQP : ∀ p, p.Prime → p ∣ Q → p ≤ P)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ P < p) (r a N : ℕ) :
    |(((range N).filter (fun n => n ≡ r [MOD Q] ∧ n ≡ a [MOD ∏ p ∈ S, p])).card : ℝ)
      - (N : ℝ) / (Q * ∏ p ∈ S, p)| ≤ 1 := by
  classical
  have hD : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).1.pos
  obtain ⟨e, -, hbd⟩ :=
    card_modEq_crt_sub_div_le hQ hD (coprime_prod_primes_gt hQP S hS) r a N
  exact hbd

end CastingOut

end NormalNumbers
