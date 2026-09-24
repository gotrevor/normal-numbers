/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Closed

/-!
# The complete sum vanishes: where the crux's difficulty actually lives

`SwingC3Closed` writes the large-prime tail as `∑_{p>P} b^{n mod p}/(b^p − 1)`, a sum of
functions periodic with prime periods `p > P`, and shows that truncating at `K` costs only
`2 b^{n−K}` — so for `n < N` the cut at `K = 2N` is free.

The truncated tail `tailTrunc b P K` is therefore *exactly periodic*, with period
`primePeriod P K = ∏_{P<p≤K} p`, and that period is **coprime to `Q`** whenever every prime
factor of `Q` is `≤ P` (which is the standing setup: `Q = ∏_{p≤P} p`).

This file proves the consequence, which is the sharpest statement available about the crux:

> **`sum_addChar_mul_periodic_eq_zero`.**  For `f` with period `M`, `gcd(M,Q) = 1` and
> `0 < j < Q`, the COMPLETE sum `∑_{n < M·Q} e(jn/Q) f(n)` is **exactly zero**.

So `AddCharTail` is not false for any structural reason: over a full period the cancellation is
perfect and free.  The entire difficulty is that the period is `∏_{P<p≤2N} p ≈ e^{2N}`, while
the available range is `N`.  **The crux is an incomplete-sum problem, not a cancellation
problem** — that is what this lap pins down, and it tells the next lap what to look for:
a handle that lets a short interval see the complete-sum cancellation (a large sieve /
Erdős–Turán / Weyl-differencing input), not a new source of cancellation.
-/

open Finset

namespace NormalNumbers

/-! ### The complete sum over a full period vanishes -/

/-- **Complete cancellation.**  An `M`-periodic weight is orthogonal to every nontrivial
additive character mod `Q`, provided `gcd(M, Q) = 1`, when summed over a full period `M·Q`. -/
theorem sum_addChar_mul_periodic_eq_zero {M Q j : ℕ} (hM : 0 < M) (hQ : 0 < Q)
    (hcop : Nat.Coprime M Q) (hj0 : 0 < j) (hjQ : j < Q)
    (f : ℕ → ℂ) (hf : ∀ n, f (n + M) = f n) :
    ∑ n ∈ range (M * Q), ee (((j : ℝ) * n / Q : ℝ) : ℂ) * f n = 0 := by
  classical
  have hfper : ∀ s t : ℕ, f (s + M * t) = f s := by
    intro s t
    induction t with
    | zero => simp
    | succ t ih =>
      have : s + M * (t + 1) = (s + M * t) + M := by ring
      rw [this, hf, ih]
  -- reindex `range (M*Q)` as `s + M*t`, `s < M`, `t < Q`
  set G : ℕ → ℂ := fun n => ee (((j : ℝ) * n / Q : ℝ) : ℂ) * f n with hG
  have hre : ∑ n ∈ range (M * Q), G n
      = ∑ q ∈ range M ×ˢ range Q, G (q.1 + M * q.2) := by
    refine Finset.sum_nbij' (i := fun n => (n % M, n / M)) (j := fun q => q.1 + M * q.2)
      ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_range] at hn
      show (n % M, n / M) ∈ range M ×ˢ range Q
      simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hM, ?_⟩
      exact Nat.div_lt_of_lt_mul hn
    · rintro ⟨s, t⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      show s + M * t ∈ range (M * Q)
      simp only [Finset.mem_range]
      calc s + M * t < M + M * t := by omega
        _ = M * (t + 1) := by ring
        _ ≤ M * Q := Nat.mul_le_mul_left M (by omega)
    · intro n hn
      show n % M + M * (n / M) = n
      exact Nat.mod_add_div n M
    · rintro ⟨s, t⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      show ((s + M * t) % M, (s + M * t) / M) = (s, t)
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1,
        Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hp.1]
      simp
    · intro n hn
      show G n = G (n % M + M * (n / M))
      rw [Nat.mod_add_div n M]
  rw [hre, Finset.sum_product]
  simp only
  have hinner : ∀ s ∈ range M, ∑ t ∈ range Q, G (s + M * t) = 0 := by
    intro s _
    have hsplit : ∀ t : ℕ, G (s + M * t)
        = (ee (((j : ℝ) * s / Q : ℝ) : ℂ) * f s) * ee (((t : ℝ) * ((j * M : ℕ) : ℤ) / Q : ℝ) : ℂ) := by
      intro t
      rw [hG]
      simp only
      rw [hfper s t]
      have : ee (((j : ℝ) * ((s + M * t : ℕ) : ℝ) / Q : ℝ) : ℂ)
          = ee (((j : ℝ) * s / Q : ℝ) : ℂ) * ee (((t : ℝ) * ((j * M : ℕ) : ℤ) / Q : ℝ) : ℂ) := by
        rw [← ee_add]
        congr 1
        push_cast
        ring
      rw [this]; ring
    rw [Finset.sum_congr rfl (fun t _ => hsplit t), ← Finset.mul_sum,
      sum_ee_div Q hQ ((j * M : ℕ) : ℤ), if_neg, mul_zero]
    intro hdvd
    have hdvd' : Q ∣ j * M := by exact_mod_cast hdvd
    have : Q ∣ j := (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm hcop) hdvd')
    have := Nat.le_of_dvd hj0 this
    omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const_zero]

/-! ### The truncated tail is exactly periodic, with period coprime to `Q` -/

/-- `∏_{P < p ≤ K, p prime} p`: the exact period of the truncated tail. -/
def primePeriod (P K : ℕ) : ℕ := ∏ p ∈ (Finset.Ioc P K).filter Nat.Prime, p

theorem primePeriod_pos (P K : ℕ) : 0 < primePeriod P K :=
  Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos

/-- The truncated large-prime tail. -/
noncomputable def tailTrunc (b P K n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc P K).filter Nat.Prime, tailPrimeTerm b p n

/-- **The truncated tail is `primePeriod P K`-periodic.** -/
theorem tailTrunc_congr {b P K n n' : ℕ} (h : n ≡ n' [MOD primePeriod P K]) :
    tailTrunc b P K n = tailTrunc b P K n' := by
  refine Finset.sum_congr rfl fun p hp => ?_
  refine tailPrimeTerm_congr (Nat.ModEq.of_dvd ?_ h)
  exact Finset.dvd_prod_of_mem _ hp

theorem tailTrunc_add_period (b P K n : ℕ) :
    tailTrunc b P K (n + primePeriod P K) = tailTrunc b P K n :=
  tailTrunc_congr Nat.add_modEq_right

/-- **The period is coprime to `Q`** whenever every prime factor of `Q` is `≤ P`. -/
theorem coprime_primePeriod {P K Q : ℕ} (hQ : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ P) :
    Nat.Coprime (primePeriod P K) Q := by
  refine Nat.Coprime.prod_left (fun p hp => ?_)
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Nat.Prime.coprime_iff_not_dvd hp.2]
  intro hd
  exact absurd (hQ p hp.2 hd) (by omega)

/-- **The crux, over a complete period: exactly zero.**  Combining the two halves: the truncated
tail is orthogonal to every nontrivial additive character mod `Q` over a full period. -/
theorem sum_addChar_tailTrunc_eq_zero {b P K Q j : ℕ} (hQ : 0 < Q)
    (hQP : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ P) (hj0 : 0 < j) (hjQ : j < Q) (h : ℤ) :
    ∑ n ∈ range (primePeriod P K * Q),
        ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ) = 0 :=
  sum_addChar_mul_periodic_eq_zero (primePeriod_pos P K) hQ (coprime_primePeriod hQP) hj0 hjQ
    _ (fun n => by rw [tailTrunc_add_period])

end NormalNumbers
