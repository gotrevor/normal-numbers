/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Var

/-!
# The signed skeleton: the exact Euler product of the truncated phase

Lap 16 refuted the whole "truncate at `K`, bound the discarded tail in `L¹`" family: the tail's
mass is `≍ N(loglog N − loglog K)` and no admissible `K` makes it `o(N)`.  What kills every such
attempt is that absolute values cost `∏_p (1 + |w_p|)` where the truth is `∏_p (1 + w_p)` with
`Re w_p < 0` — all of the decay lives in the signs.

This file builds the signed object.  For a prime `p`, the **Euler factor** is the complete-period
mean of the one-prime phase,

    primeFactor b p h = (1/p) ∑_{r<p} e(h · tailPrimeTerm b p r),

and the main theorem is that the complete-period mean of the *truncated* phase is EXACTLY the
product of the factors:

    (1/∏_{P<p≤K} p) ∑_{n < ∏_{P<p≤K} p} e(h · tailTrunc b P K n)
        = ∏_{P<p≤K} primeFactor b p h.

This is the Selberg–Delange skeleton, and it is exact — no analytic input, only CRT.  The engine
is `sum_filter_prod_eq_prod`: a product of periodic factors with pairwise coprime periods has a
complete sum that factorizes, proved by the same peel-one-prime-and-refine-the-progression
induction as `SwingC3Var.norm_sum_addChar_prod_le`, with base case "an arithmetic progression
mod `m` meets `range m` exactly once".

With `primeFactor` in hand the crux's decay is a statement about `∏(1 + w_p)`, `w_p = factor − 1`:
writing `A_p = ∑_{r<p}(1 − cos 2π h c_p(r)) > 0` and `B_p = ∑_{r<p} sin 2π h c_p(r)`,

    ‖primeFactor b p h‖² = (1 − A_p/p)² + (B_p/p)²  =  1 − 2A_p/p + O(1/p²),

with `A_p → ∑_{d≥1}(1 − cos 2π h b^{−d}) =: a(h) > 0` whenever `b ∤ h`.  Since `∑_p 1/p` diverges,
`∏_{P<p≤K} ‖primeFactor‖ → 0` as `K → ∞` — and `a(h)` is exactly the exponent the lap-11 probe
measured (`b=3, h=1`: predicted `1.76`, measured `≈ 1.9`).  That quantitative step is the next
lap; this file supplies the exact algebraic identity it will be applied to, plus the trivial
bound `‖primeFactor‖ ≤ 1`.
-/

open Finset

namespace NormalNumbers

/-! ### CRT: a product of coprime-periodic factors has a factorizing complete sum -/

/-- An arithmetic progression mod `m` meets `range m` exactly once. -/
theorem card_filter_modEq_range (m a : ℕ) (hm : 0 < m) :
    ((range m).filter (fun n => n ≡ a [MOD m])).card = 1 := by
  classical
  have := Nat.count_modEq_card (b := m) (r := m) hm a
  rw [Nat.count_eq_card_filter_range] at this
  simp only [Nat.mod_self, Nat.not_lt_zero, if_false, Nat.div_self hm] at this
  simpa using this

/-- **The complete sum factorizes.**  For `p`-periodic factors `g_p` with `p` ranging over a
finite pairwise-coprime set `F`, all coprime to an ambient modulus `m`, the sum over a complete
period of the progression `n ≡ a [MOD m]` is the product of the one-modulus complete sums.  This
is the Chinese remainder theorem in the only form the swing needs. -/
theorem sum_filter_prod_eq_prod (g : ℕ → ℕ → ℂ) :
    ∀ F : Finset ℕ, (∀ p ∈ F, 0 < p) → (∀ p ∈ F, ∀ n, g p (n + p) = g p n) →
      ((F : Set ℕ).Pairwise Nat.Coprime) →
      ∀ m a : ℕ, 0 < m → (∀ p ∈ F, Nat.Coprime p m) →
      ∑ n ∈ (range (m * ∏ p ∈ F, p)).filter (fun n => n ≡ a [MOD m]), ∏ p ∈ F, g p n
        = ∏ p ∈ F, ∑ r ∈ range p, g p r := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
      intro _ _ _ m a hm _
      simp only [Finset.prod_empty, mul_one]
      rw [Finset.sum_const, card_filter_modEq_range m a hm]
      simp
  | @insert q s hq ih =>
      intro hpos hper hpair m a hm hcopm
      have hqmem : q ∈ insert q s := Finset.mem_insert_self q s
      have hsmem : ∀ p, p ∈ s → p ∈ insert q s := fun p hp => Finset.mem_insert_of_mem hp
      have hqpos : 0 < q := hpos q hqmem
      have hmq : Nat.Coprime m q := (hcopm q hqmem).symm
      have hrange : m * ∏ p ∈ insert q s, p = (m * q) * ∏ p ∈ s, p := by
        rw [Finset.prod_insert hq]; ring
      rw [hrange, Finset.prod_insert hq]
      -- fibre over the residue mod `q`
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (range ((m * q) * ∏ p ∈ s, p)).filter (fun n => n ≡ a [MOD m]))
        (t := range q) (g := fun n => n % q)
        (f := fun n => ∏ p ∈ insert q s, g p n)
        (fun x _ => Finset.mem_range.2 (Nat.mod_lt x hqpos))
      rw [← hfib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hrq : r < q := Finset.mem_range.1 hr
      obtain ⟨c, hca, hcr⟩ : ∃ c : ℕ, c ≡ a [MOD m] ∧ c ≡ r [MOD q] :=
        ⟨(Nat.chineseRemainder hmq a r : ℕ), (Nat.chineseRemainder hmq a r).2.1,
          (Nat.chineseRemainder hmq a r).2.2⟩
      have hset : ((range ((m * q) * ∏ p ∈ s, p)).filter (fun n => n ≡ a [MOD m])).filter
            (fun n => n % q = r)
          = (range ((m * q) * ∏ p ∈ s, p)).filter (fun n => n ≡ c [MOD m * q]) := by
        rw [Finset.filter_filter]
        refine Finset.filter_congr ?_
        intro n _
        constructor
        · rintro ⟨h1, h2⟩
          refine (Nat.modEq_and_modEq_iff_modEq_mul hmq).1 ⟨h1.trans hca.symm, ?_⟩
          have hnr : n ≡ r [MOD q] := by
            show n % q = r % q
            rw [h2, Nat.mod_eq_of_lt hrq]
          exact hnr.trans hcr.symm
        · intro h
          obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hmq).2 h
          refine ⟨h1.trans hca, ?_⟩
          have hnr : n ≡ r [MOD q] := h2.trans hcr
          have hval : n % q = r % q := hnr
          rwa [Nat.mod_eq_of_lt hrq] at hval
      have hcongr : ∀ n ∈ ((range ((m * q) * ∏ p ∈ s, p)).filter (fun n => n ≡ a [MOD m])).filter
            (fun n => n % q = r),
          ∏ p ∈ insert q s, g p n = g q r * ∏ p ∈ s, g p n := by
        intro n hn
        have hnq : n % q = r := (Finset.mem_filter.1 hn).2
        have hgn : g q n = g q r := by
          rw [periodic_eq_mod (g q) (hper q hqmem) n, hnq]
        rw [Finset.prod_insert hq, hgn]
      rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, hset]
      have hcop' : ∀ p ∈ s, Nat.Coprime p (m * q) := by
        intro p hp
        refine Nat.Coprime.mul_right (hcopm p (hsmem p hp)) ?_
        have hne : p ≠ q := fun hpq => hq (hpq ▸ hp)
        exact hpair (hsmem p hp) hqmem hne
      rw [ih (fun p hp => hpos p (hsmem p hp)) (fun p hp => hper p (hsmem p hp))
        (hpair.mono (by intro x hx; exact hsmem x hx)) (m * q) c (Nat.mul_pos hm hqpos) hcop']

/-- The complete sum over one period, with no ambient progression. -/
theorem sum_range_prod_eq_prod (g : ℕ → ℕ → ℂ) (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hper : ∀ p ∈ F, ∀ n, g p (n + p) = g p n) (hpair : ((F : Set ℕ)).Pairwise Nat.Coprime) :
    ∑ n ∈ range (∏ p ∈ F, p), ∏ p ∈ F, g p n = ∏ p ∈ F, ∑ r ∈ range p, g p r := by
  classical
  have := sum_filter_prod_eq_prod g F hpos hper hpair 1 0 Nat.one_pos
    (fun p _ => Nat.coprime_one_right p)
  rwa [one_mul, Finset.filter_true_of_mem (fun x _ => Nat.modEq_one)] at this

/-! ### The Euler factor of one prime -/

/-- **The Euler factor**: the complete-period mean of the one-prime phase
`e(h · b^{n mod p}/(b^p − 1))`.  `primeFactor − 1 = w_p` is the signed per-prime weight whose
negative real part carries the whole decay. -/
noncomputable def primeFactor (b p : ℕ) (h : ℤ) : ℂ :=
  (∑ r ∈ range p, ee (((h : ℝ) * tailPrimeTerm b p r : ℝ) : ℂ)) / p

/-- A mean of unit vectors: `‖primeFactor‖ ≤ 1`. -/
theorem norm_primeFactor_le_one {b p : ℕ} (hp : 0 < p) (h : ℤ) :
    ‖primeFactor b p h‖ ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [primeFactor, norm_div, Complex.norm_natCast]
  rw [div_le_one hpR]
  calc ‖∑ r ∈ range p, ee (((h : ℝ) * tailPrimeTerm b p r : ℝ) : ℂ)‖
      ≤ ∑ r ∈ range p, ‖ee (((h : ℝ) * tailPrimeTerm b p r : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ = (p : ℝ) := by
        rw [Finset.sum_congr rfl (fun r _ => norm_ee_real ((h : ℝ) * tailPrimeTerm b p r))]
        simp

/-! ### The exact Euler product for the truncated phase -/

/-- The truncated phase is the product of its one-prime factors. -/
theorem ee_tailTrunc_eq_prod {b : ℕ} (P K : ℕ) (h : ℤ) (n : ℕ) :
    ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)
      = ∏ p ∈ (Finset.Ioc P K).filter Nat.Prime,
          ee (((h : ℝ) * tailPrimeTerm b p n : ℝ) : ℂ) := by
  have hsum : (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)
      = ∑ p ∈ (Finset.Ioc P K).filter Nat.Prime, (((h : ℝ) * tailPrimeTerm b p n : ℝ) : ℂ) := by
    rw [tailTrunc, Finset.mul_sum]
    push_cast
    rfl
  rw [hsum, ee_sum]

/-- **THE EULER PRODUCT.**  Over a complete period, the mean of the truncated phase is exactly
the product of the one-prime Euler factors.  Exact, CRT-only — this is the object every
Selberg–Delange argument works with, and the point of lap 16's refutation is that the crux can
only be reached through it, never through `L¹` bounds on the same quantity. -/
theorem sum_range_ee_tailTrunc_eq {b : ℕ} (P K : ℕ) (h : ℤ) :
    ∑ n ∈ range (primePeriod P K), ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)
      = (primePeriod P K : ℂ)
        * ∏ p ∈ (Finset.Ioc P K).filter Nat.Prime, primeFactor b p h := by
  classical
  set F : Finset ℕ := (Finset.Ioc P K).filter Nat.Prime with hF
  set g : ℕ → ℕ → ℂ := fun p n => ee (((h : ℝ) * tailPrimeTerm b p n : ℝ) : ℂ) with hg
  have hmemF : ∀ p ∈ F, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have hpos : ∀ p ∈ F, 0 < p := fun p hp => (hmemF p hp).pos
  have hper : ∀ p ∈ F, ∀ n, g p (n + p) = g p n := by
    intro p _ n
    simp only [hg]
    rw [tailPrimeTerm_congr (Nat.add_modEq_right)]
  have hpair : ((F : Set ℕ)).Pairwise Nat.Coprime := by
    intro x hx y hy hxy
    exact (Nat.coprime_primes (hmemF x (by simpa using hx)) (hmemF y (by simpa using hy))).2 hxy
  have hper' : primePeriod P K = ∏ p ∈ F, p := rfl
  calc ∑ n ∈ range (primePeriod P K), ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)
      = ∑ n ∈ range (∏ p ∈ F, p), ∏ p ∈ F, g p n := by
        rw [hper']
        exact Finset.sum_congr rfl fun n _ => ee_tailTrunc_eq_prod P K h n
    _ = ∏ p ∈ F, ∑ r ∈ range p, g p r := sum_range_prod_eq_prod g F hpos hper hpair
    _ = ∏ p ∈ F, ((p : ℂ) * primeFactor b p h) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpR : ((p : ℂ)) ≠ 0 := by
          have h0 : p ≠ 0 := (hmemF p hp).pos.ne'
          exact_mod_cast h0
        simp only [hg, primeFactor]
        rw [mul_comm, div_mul_cancel₀ _ hpR]
    _ = (primePeriod P K : ℂ) * ∏ p ∈ F, primeFactor b p h := by
        rw [Finset.prod_mul_distrib, hper', Nat.cast_prod]

end NormalNumbers
