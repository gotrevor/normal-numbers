/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtOmegaBridge

/-!
# Absolute convergence of the powerful-number weight

`C3MrtOmegaBridge` writes `z^{ω} = z^{Ω} ⋆ g` with `g = sqfW z` supported on the powerful
numbers, `g(d) = (z − z²)^{ω(d)}`.  To *use* that expansion inside a correlation sum one must
know the tuple sum converges absolutely, i.e.

    ∑_{d powerful} ‖z − z²‖^{ω(d)} / d  <  ∞     (for ‖z‖ = 1).

This file proves exactly that (`summable_norm_sqfW_div`), by two elementary ingredients that
avoid any Euler product:

* **Parametrisation** (`exists_cube_mul_sq_of_powerful`): every powerful `d > 0` is `a³c²`.
  (From `Nat.sq_mul_squarefree_of_pos`: `d = b²a` with `a` squarefree; powerfulness forces
  `a ∣ b`, and substituting `b = a c` gives `d = a³c²`.)
* **A sharp `ω`-bound** (`two_pow_omega_le_of_powerful`): for powerful `d`,
  `2^{ω(d)} ≤ 2 · d^{3/8}`.  Indeed at most one prime factor is `2`, and the *odd* prime
  factors each contribute `p² ≥ 9` to `d`, so `9^{k} ≤ d` for `k` the number of odd prime
  factors; since `256 = 2^8 ≤ 9^3 = 729`, this gives `2^k ≤ d^{3/8}`.

Combining, the summand is `≤ 2·d^{-5/8} = 2·(a³c²)^{-5/8} = 2 a^{-15/8} c^{-5/4}`, and both
exponents exceed `1`.  The `5/8` is not an artefact: `d ↦ 2^{ω(d)}/d` is exactly `1/2 = d^{-1/2}`
at `d = 4`, so no exponent `> 1/2` holds without the constant, and `1/2` alone would leave the
`c`-sum divergent.  The extra room comes precisely from isolating the prime `2`.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-! ### Parametrisation of powerful numbers as `a³c²` -/

/-- Every powerful `d > 0` has the form `a³ c²`. -/
theorem exists_cube_mul_sq_of_powerful {d : ℕ} (hd : 0 < d) (hP : Powerful d) :
    ∃ a c : ℕ, 0 < a ∧ 0 < c ∧ d = a ^ 3 * c ^ 2 := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hd
  -- `a ∣ b`
  have hdvd : a ∣ b := by
    rw [← Nat.factorization_le_iff_dvd ha.ne' hb.ne']
    intro p
    by_cases hp : p.Prime
    · by_cases hpa : p ∣ a
      · have hpd : p ∣ d := hab ▸ (hpa.mul_left _)
        have hp2 : p ^ 2 ∣ d := hP p hp hpd
        have hfa : a.factorization p = 1 := by
          have h1 : a.factorization p ≠ 0 := by
            simpa [Nat.Prime.factorization_pos_of_dvd hp ha.ne' hpa] using
              (Nat.Prime.factorization_pos_of_dvd hp ha.ne' hpa).ne'
          have h2 : a.factorization p < 2 := by
            by_contra hc
            push_neg at hc
            exact (Nat.squarefree_iff_factorization_le_one ha.ne').1 hsq p |>.trans_lt
              (by omega) |>.false
          omega
        have hfd : 2 ≤ d.factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp hd.ne').1 hp2
        have : d.factorization p = 2 * b.factorization p + a.factorization p := by
          rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb.ne') ha.ne']
          simp [Nat.factorization_pow]
        have : 1 ≤ b.factorization p := by omega
        simpa [hfa] using this
      · simp [Nat.factorization_eq_zero_of_not_dvd hpa]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  obtain ⟨c, rfl⟩ := hdvd
  refine ⟨a, c, ha, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with rfl | h
    · simp at hb
    · exact h
  · rw [← hab]; ring

/-! ### The `ω` bound for powerful numbers -/

private lemma nine_pow_card_le {d : ℕ} (hd : 0 < d) (hP : Powerful d) :
    9 ^ (d.primeFactors.erase 2).card ≤ d := by
  set S := d.primeFactors.erase 2 with hS
  have hsub : S ⊆ d.primeFactors := Finset.erase_subset _ _
  have hfac : ∀ p ∈ S, 2 ≤ d.factorization p := by
    intro p hp
    have hp' := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp'
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hd.ne').1
      (hP p hpp (Nat.dvd_of_mem_primeFactors hp'))
  have h1 : (∏ p ∈ S, p ^ 2) ∣ ∏ p ∈ S, p ^ d.factorization p :=
    Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p (hfac p hp)
  have h2 : (∏ p ∈ S, p ^ d.factorization p) ∣ d := by
    have hEq : (∏ p ∈ d.primeFactors, p ^ d.factorization p) = d :=
      (Nat.prod_primeFactors_pow_factorization hd.ne').symm
    calc (∏ p ∈ S, p ^ d.factorization p)
        ∣ ∏ p ∈ d.primeFactors, p ^ d.factorization p :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
      _ = d := hEq
  have h3 : (9 : ℕ) ^ S.card ≤ ∏ p ∈ S, p ^ 2 := by
    calc (9 : ℕ) ^ S.card = ∏ _p ∈ S, 9 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ S, p ^ 2 := by
        refine Finset.prod_le_prod' fun p hp => ?_
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hsub hp)
        have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
        have h2le := hpp.two_le
        have h3 : 3 ≤ p := by omega
        nlinarith
  have hpos : 0 < ∏ p ∈ S, p ^ d.factorization p :=
    Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (hsub hp)).pos _
  exact le_trans h3 (le_trans (Nat.le_of_dvd hpos h1) (Nat.le_of_dvd hd h2))

/-- **The `ω`-bound for powerful numbers**: `2^{ω(d)} ≤ 2 · d^{3/8}`.

At most one prime factor equals `2`; each *odd* prime factor `p` contributes `p² ≥ 9` to `d`,
so `9^k ≤ d` with `k` the number of odd prime factors.  Since `2^8 = 256 ≤ 729 = 9^3`, we get
`(2^k)^8 ≤ (9^k)^3 ≤ d^3`, i.e. `2^k ≤ d^{3/8}`. -/
theorem two_pow_omega_le_of_powerful {d : ℕ} (hd : 0 < d) (hP : Powerful d) :
    (2 : ℝ) ^ omegaNat d ≤ 2 * (d : ℝ) ^ ((3 : ℝ) / 8) := by
  set S := d.primeFactors.erase 2 with hS
  have hcard : omegaNat d ≤ S.card + 1 := by
    have := Finset.pred_card_le_card_erase (s := d.primeFactors) (a := 2)
    simp only [omegaNat, hS]
    omega
  have h9 : (9 : ℕ) ^ S.card ≤ d := nine_pow_card_le hd hP
  -- the integer inequality `(2^k)^8 ≤ d^3`
  have hint : ((2 : ℕ) ^ S.card) ^ 8 ≤ d ^ 3 := by
    calc ((2 : ℕ) ^ S.card) ^ 8 = 256 ^ S.card := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ 729 ^ S.card := Nat.pow_le_pow_left (by norm_num) _
      _ = ((9 : ℕ) ^ S.card) ^ 3 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ d ^ 3 := Nat.pow_le_pow_left h9 3
  -- transfer to `ℝ` and take the `1/8`-th power
  have hx : (0 : ℝ) ≤ (2 : ℝ) ^ S.card := by positivity
  have hy : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hintR : ((2 : ℝ) ^ S.card) ^ (8 : ℕ) ≤ ((d : ℝ)) ^ (3 : ℕ) := by
    exact_mod_cast hint
  have hkey : (2 : ℝ) ^ S.card ≤ (d : ℝ) ^ ((3 : ℝ) / 8) := by
    have h1 : ((2 : ℝ) ^ S.card) = (((2 : ℝ) ^ S.card) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ S.card) 8, ← Real.rpow_mul hx]
      norm_num
    have h2 : ((d : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 8) = (d : ℝ) ^ ((3 : ℝ) / 8) := by
      rw [← Real.rpow_natCast (d : ℝ) 3, ← Real.rpow_mul hy]
      norm_num
    calc (2 : ℝ) ^ S.card = (((2 : ℝ) ^ S.card) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) := h1
      _ ≤ ((d : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 8) :=
          Real.rpow_le_rpow (by positivity) hintR (by norm_num)
      _ = (d : ℝ) ^ ((3 : ℝ) / 8) := h2
  calc (2 : ℝ) ^ omegaNat d ≤ (2 : ℝ) ^ (S.card + 1) := by
        exact pow_le_pow_right₀ (by norm_num) hcard
    _ = 2 * (2 : ℝ) ^ S.card := by ring
    _ ≤ 2 * (d : ℝ) ^ ((3 : ℝ) / 8) := by linarith

/-! ### The summability -/

/-- A choice of `(a, c)` with `d = a³c²`, for powerful `d`. -/
noncomputable def cubeSqPair (d : ℕ) : ℕ × ℕ :=
  if h : 0 < d ∧ Powerful d then
    (Classical.choose (exists_cube_mul_sq_of_powerful h.1 h.2),
      Classical.choose (Classical.choose_spec (exists_cube_mul_sq_of_powerful h.1 h.2)))
  else (0, 0)

lemma cubeSqPair_spec {d : ℕ} (hd : 0 < d) (hP : Powerful d) :
    0 < (cubeSqPair d).1 ∧ 0 < (cubeSqPair d).2 ∧
      d = (cubeSqPair d).1 ^ 3 * (cubeSqPair d).2 ^ 2 := by
  have h : 0 < d ∧ Powerful d := ⟨hd, hP⟩
  rw [cubeSqPair, dif_pos h]
  exact Classical.choose_spec (Classical.choose_spec (exists_cube_mul_sq_of_powerful h.1 h.2))

/-- The majorant on `ℕ × ℕ`: `2 a^{-15/8} c^{-5/4}`. -/
noncomputable def cubeSqMaj (q : ℕ × ℕ) : ℝ :=
  (2 * (q.1 : ℝ) ^ (-(15 : ℝ) / 8)) * ((q.2 : ℝ) ^ (-(5 : ℝ) / 4))

lemma summable_cubeSqMaj : Summable cubeSqMaj := by
  have h1 : Summable (fun a : ℕ => 2 * (a : ℝ) ^ (-(15 : ℝ) / 8)) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left 2
  have h2 : Summable (fun c : ℕ => (c : ℝ) ^ (-(5 : ℝ) / 4)) :=
    Real.summable_nat_rpow.2 (by norm_num)
  exact h1.mul_of_nonneg h2 (fun a => by positivity) (fun c => Real.rpow_nonneg (by positivity) _)

lemma cubeSqMaj_eq {d : ℕ} (hd : 0 < d) (hP : Powerful d) :
    cubeSqMaj (cubeSqPair d) = 2 * (d : ℝ) ^ (-(5 : ℝ) / 8) := by
  obtain ⟨ha, hc, hac⟩ := cubeSqPair_spec hd hP
  set a := (cubeSqPair d).1
  set c := (cubeSqPair d).2
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hdR : (d : ℝ) = (a : ℝ) ^ (3 : ℕ) * (c : ℝ) ^ (2 : ℕ) := by exact_mod_cast hac
  rw [cubeSqMaj, hdR]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast (a : ℝ) 3, ← Real.rpow_natCast (c : ℝ) 2,
    ← Real.rpow_mul haR.le, ← Real.rpow_mul hcR.le]
  norm_num
  ring

/-- **Absolute convergence of the bridge weight.**  For `‖z‖ = 1`,
`∑_{d} ‖g(d)‖/d = ∑_{d powerful} ‖z − z²‖^{ω(d)}/d < ∞`, so the tuple expansion of
`C3MrtOmegaBridge` may be truncated at `d ≤ Y` with a tail `→ 0` uniformly in `N`. -/
theorem summable_norm_sqfW_div (z : ℂ) (hz : ‖z‖ = 1) :
    Summable fun d : ℕ => ‖sqfW z d‖ / (d : ℝ) := by
  set s : Set ℕ := {d : ℕ | 0 < d ∧ Powerful d} with hs
  have hw : ‖z - z ^ 2‖ ≤ 2 := by
    have h2 : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
    calc ‖z - z ^ 2‖ ≤ ‖z‖ + ‖z ^ 2‖ := norm_sub_le _ _
      _ = 2 := by rw [hz, h2]; norm_num
  have hzero : ∀ d : ℕ, d ∉ s → ‖sqfW z d‖ / (d : ℝ) = 0 := by
    intro d hd
    simp only [hs, Set.mem_setOf_eq, not_and_or, not_lt, Nat.le_zero] at hd
    rcases hd with hd | hd
    · have : d = 0 := by omega
      subst this; simp [sqfW]
    · rcases eq_or_ne d 0 with rfl | hd0
      · simp [sqfW]
      · rw [sqfW_apply hd0, if_neg hd]; simp
  -- bound on `s`
  have hbound : ∀ x : s, ‖sqfW z x.val‖ / (x.val : ℝ) ≤ cubeSqMaj (cubeSqPair x.val) := by
    rintro ⟨d, hd, hP⟩
    have hd0 : d ≠ 0 := hd.ne'
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    rw [cubeSqMaj_eq hd hP]
    have hnum : ‖sqfW z d‖ ≤ (2 : ℝ) ^ omegaNat d := by
      rw [sqfW_apply hd0, if_pos hP, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hw _
    have hbd : (2 : ℝ) ^ omegaNat d ≤ 2 * (d : ℝ) ^ ((3 : ℝ) / 8) :=
      two_pow_omega_le_of_powerful hd hP
    have hstep : ‖sqfW z d‖ / (d : ℝ) ≤ (2 * (d : ℝ) ^ ((3 : ℝ) / 8)) / (d : ℝ) :=
      div_le_div_of_nonneg_right (le_trans hnum hbd) hdR.le
    refine hstep.trans_eq ?_
    rw [mul_div_assoc]
    congr 1
    rw [eq_comm, eq_div_iff hdR.ne']
    nth_rw 2 [show (d : ℝ) = (d : ℝ) ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hdR]
    norm_num
  have hsub : Summable fun x : s => ‖sqfW z x.val‖ / (x.val : ℝ) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) hbound ?_
    refine summable_cubeSqMaj.comp_injective ?_
    rintro ⟨d₁, hd₁, hP₁⟩ ⟨d₂, hd₂, hP₂⟩ h
    obtain ⟨_, _, he₁⟩ := cubeSqPair_spec hd₁ hP₁
    obtain ⟨_, _, he₂⟩ := cubeSqPair_spec hd₂ hP₂
    have h' : cubeSqPair d₁ = cubeSqPair d₂ := h
    simp only [Subtype.mk.injEq]
    rw [he₁, he₂, h']
  have hsub' : Summable ((fun d : ℕ => ‖sqfW z d‖ / (d : ℝ)) ∘ (Subtype.val : s → ℕ)) := hsub
  rw [summable_subtype_iff_indicator] at hsub'
  refine hsub'.congr fun d => ?_
  by_cases hd : d ∈ s
  · simp [Set.indicator_of_mem hd]
  · simp [Set.indicator_of_notMem hd, hzero d hd]

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.summable_norm_sqfW_div
#print axioms NormalNumbers.CastingOut.exists_cube_mul_sq_of_powerful
#print axioms NormalNumbers.CastingOut.two_pow_omega_le_of_powerful
