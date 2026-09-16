/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation

/-!
# Mertens' theorem for a subset of the primes — the interface and its residue-class instance

Campaign A (prime-subset Lambert series).  The base-`b` schedule of `G4SchedB*` consumes the
lower Mertens bound `log log R ≤ ∑_{p < R} 1/p + 1` at one single place
(`G4SchedBParams.sum_inv_smallPrimes_ge`, feeding `G4SchedBBudget.main_term_le`).  The audit of
2026-09-16 (`DESIGN-2026-09-16-prime-subset.md`) shows that what the schedule actually needs is a
**rate**: for the cutoff exponent `e` (i.e. `R = 2^{2^e}`) it needs

    ∑_{p ∈ S, p < R} 1/p  ≥  c·e − C     for a fixed `c > 0`,

because the cutoff exponent may be inflated by any constant factor (the schedule's window for `e`
is `[exp(O(K log K)), exp(Θ(K²))]`) but **not** by an unbounded one — so mere divergence of
`∑_{p ∈ S} 1/p` is not enough for this route.  This module isolates that hypothesis as
`MertensRate` and sets up the elementary chain that establishes it for a residue class.

## The chain (each step a named leaf)

With `A_S(N) = ∑_{p ∈ S, p < N} (log p)/p` and `x = 1 + λ/log N`:

* `sumLog_tail_le` — `∑_{n > N} Λ(n)·n^{−x} ≤ C₁·e^{−λ}·(log N)/λ`, from Chebyshev's
  `ψ t ≤ (log 4 + 4)·t` by Abel summation.
* `sumLog_ge_of_LSeries_ge` — the transfer `LSeries lower bound ⟹ A_S(N) ≥ c·log N − C`,
  using the tail bound and `p^{−(x−1)} ≤ 1`.
* `mertensRate_of_sumLog` — partial summation `1/p = (log p / p)·(log p)⁻¹`, turning
  `A_S(N) ≥ c log N − C` into `∑_{p ∈ S, p < N} 1/p ≥ c·log log N − C'`.
* `sumLog_residueClass_ge` / `mertensRate_residueClass` — the instance for `p ≡ a (mod q)`,
  fed by `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`.

Nothing here mentions the schedule; `MertensRate` is the whole interface it will consume.
-/

open Finset Real

namespace NormalNumbers.G4.MertensAP

variable (S : ℕ → Prop) [DecidablePred S]

/-- `∑_{p < N, p ∈ S} 1/p`, the quantity the schedule consumes. -/
noncomputable def sumInvPrimesIn (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow with S p, (p : ℝ)⁻¹

/-- `∑_{p < N, p ∈ S} (log p)/p`, the Mertens-with-`log` intermediate. -/
noncomputable def sumLogPrimesIn (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow with S p, Real.log p / p

/-- **The interface.**  `S` has Mertens rate `c` with defect `C`: the prime reciprocals of `S`
below `N` exceed `c·log log N − C`.  The schedule needs exactly this, with `c` fixed and `C`
arbitrary, because it may inflate the cutoff exponent by the constant factor `1/c`. -/
def MertensRate (c C : ℝ) : Prop :=
  0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * Real.log (Real.log N) - C ≤ sumInvPrimesIn S N

variable {S}

lemma sumInvPrimesIn_nonneg (N : ℕ) : 0 ≤ sumInvPrimesIn S N :=
  Finset.sum_nonneg fun p _ => by positivity

lemma sumLogPrimesIn_nonneg (N : ℕ) : 0 ≤ sumLogPrimesIn S N := by
  refine Finset.sum_nonneg fun p hp => ?_
  have : 1 ≤ p := (Nat.prime_of_mem_primesBelow (Finset.mem_filter.1 hp).1).one_lt.le.trans' le_rfl
  positivity

/-- Subsetting only shrinks the sums: the monotonicity that makes every *upper* use of the
harmonic sum in the schedule free. -/
lemma sumInvPrimesIn_le_of_subset {S' : ℕ → Prop} [DecidablePred S']
    (h : ∀ p, S p → S' p) (N : ℕ) : sumInvPrimesIn S N ≤ sumInvPrimesIn S' N := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, h p hp.2⟩

/-! ### Leaf 1 — the Chebyshev tail (no residue classes) -/

/-- **Leaf.**  The von Mangoldt tail beyond `N` at exponent `x = 1 + λ/log N`, bounded by Abel
summation against Chebyshev's `ψ t ≤ (log 4 + 4)·t`.  The shape recorded here is the one the
transfer step needs: the tail is `≤ 11·e^{−λ}·(log N)/λ`. -/
theorem sumLog_tail_le {N : ℕ} (hN : 16 ≤ N) {lam : ℝ} (hlam : 1 ≤ lam)
    (hlam' : lam ≤ Real.log N) :
    ∑' n : ℕ, (if N < n then ArithmeticFunction.vonMangoldt n else 0)
        / (n : ℝ) ^ (1 + lam / Real.log N)
      ≤ 11 * Real.exp (-lam) * Real.log N / lam := by
  sorry

/-! ### Leaf 2 — the transfer from the `L`-series lower bound to `A_S(N)` -/

/-- **Leaf.**  If the Dirichlet series of `S`-primes weighted by `log` is bounded below by
`c/(x−1) − C₀` on `(1, 2]`, then `A_S(N) = ∑_{p ∈ S, p < N} (log p)/p ≥ c'·log N − C'` for
constants depending only on `c, C₀`.  Steps 1, 3, 4 of the design chain: split at `N`, use
`p^{−(x−1)} ≤ 1` below `N` and `sumLog_tail_le` above, and choose `λ = log(11/c₁)` with
`c₁ = c/2`. -/
theorem sumLog_ge_of_LSeries_ge {c C₀ : ℝ} (hc : 0 < c)
    (h : ∀ x : ℝ, 1 < x → x ≤ 2 →
      c / (x - 1) - C₀
        ≤ ∑' n : ℕ, (if n.Prime ∧ S n then Real.log n else 0) / (n : ℝ) ^ x) :
    ∃ c' C' : ℝ, 0 < c' ∧ ∀ N : ℕ, 2 ≤ N → c' * Real.log N - C' ≤ sumLogPrimesIn S N := by
  sorry

/-! ### Leaf 3 — partial summation `A_S ↦ ∑ 1/p`

Done dyadically, at the cutoffs `NN j = 2^(2^j)` (so `log (NN j) = 2^j log 2`), which turns the
Abel summation into the finite identity `abel_parts` and needs **no** upper bound on `A_S`: the
only place `A_S` appears with a negative sign is the single constant `A_S (NN 0)`. -/

/-- The dyadic-tower cutoffs `NN j = 2^(2^j)`. -/
private def NN (j : ℕ) : ℕ := 2 ^ 2 ^ j

/-- `log (NN j) = 2^j · log 2`. -/
private lemma log_NN (j : ℕ) : Real.log ((NN j : ℕ) : ℝ) = (2 : ℝ) ^ j * Real.log 2 := by
  unfold NN
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

private lemma NN_mono {i j : ℕ} (h : i ≤ j) : NN i ≤ NN j :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

private lemma two_le_NN (j : ℕ) : 2 ≤ NN j := by
  have : NN 0 ≤ NN j := NN_mono (Nat.zero_le _)
  simpa [NN] using this

/-- Summation by parts, finite form. -/
private lemma abel_parts (A w : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, (A (j + 1) - A j) * w (j + 1)
      = A J * w J - A 0 * w 0 + ∑ j ∈ Finset.range J, A j * (w j - w (j + 1)) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := fun j => A j * (w j - w (j + 1)))]
      ring

/-- One dyadic step: dividing the `log`-weighted increment by `log (NN (j+1))` under-counts the
reciprocal increment, because `log p ≤ log (NN (j+1))` on the block. -/
private lemma step_le (j : ℕ) :
    (sumLogPrimesIn S (NN (j + 1)) - sumLogPrimesIn S (NN j)) / ((2 : ℝ) ^ (j + 1) * Real.log 2)
      ≤ sumInvPrimesIn S (NN (j + 1)) - sumInvPrimesIn S (NN j) := by
  set L : ℝ := (2 : ℝ) ^ (j + 1) * Real.log 2 with hL
  have hL0 : 0 < L := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hsub : {p ∈ (NN j).primesBelow | S p} ⊆ {p ∈ (NN (j + 1)).primesBelow | S p} := by
    intro p hp
    simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp ⊢
    exact ⟨⟨lt_of_lt_of_le hp.1.1 (NN_mono (Nat.le_succ j)), hp.1.2⟩, hp.2⟩
  have h1 : sumLogPrimesIn S (NN (j + 1)) - sumLogPrimesIn S (NN j)
      = ∑ p ∈ {p ∈ (NN (j + 1)).primesBelow | S p} \ {p ∈ (NN j).primesBelow | S p},
          Real.log p / p := (Finset.sum_sdiff_eq_sub hsub).symm
  have h2 : sumInvPrimesIn S (NN (j + 1)) - sumInvPrimesIn S (NN j)
      = ∑ p ∈ {p ∈ (NN (j + 1)).primesBelow | S p} \ {p ∈ (NN j).primesBelow | S p},
          (p : ℝ)⁻¹ := (Finset.sum_sdiff_eq_sub hsub).symm
  rw [h1, h2, Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' : p ∈ (NN (j + 1)).primesBelow := by
    have := Finset.mem_sdiff.1 hp
    exact (Finset.mem_filter.1 this.1).1
  rw [Nat.mem_primesBelow] at hp'
  have hp2 : 2 ≤ p := hp'.2.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hlogp : Real.log p ≤ L := by
    have : Real.log p ≤ Real.log ((NN (j + 1) : ℕ) : ℝ) := by
      apply Real.log_le_log (by linarith)
      exact_mod_cast hp'.1.le
    rwa [log_NN] at this
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hp0 : (0 : ℝ) < p := by linarith
  have hfrac : Real.log p / L ≤ 1 := (div_le_one hL0).2 hlogp
  calc Real.log p / p / L = (Real.log p / L) * (p : ℝ)⁻¹ := by field_simp
    _ ≤ 1 * (p : ℝ)⁻¹ := by gcongr
    _ = (p : ℝ)⁻¹ := one_mul _

/-- **The dyadic lower bound.**  `A_S(N) ≥ c·log N − C` gives
`∑_{p ∈ S, p < NN J} 1/p ≥ (c/2)·J − D` with an absolute `D`. -/
private lemma tower_lower {c C : ℝ} (hc : 0 < c)
    (h : ∀ N : ℕ, 2 ≤ N → c * Real.log N - C ≤ sumLogPrimesIn S N) :
    ∃ D : ℝ, ∀ J : ℕ, c / 2 * J - D ≤ sumInvPrimesIn S (NN J) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set w : ℕ → ℝ := fun j => (Real.log 2)⁻¹ * (1 / 2 : ℝ) ^ j with hw
  set A : ℕ → ℝ := fun j => sumLogPrimesIn S (NN j) with hA
  set F : ℕ → ℝ := fun j => sumInvPrimesIn S (NN j) with hF
  have hwpos : ∀ j, 0 < w j := fun j => by rw [hw]; positivity
  have hwle : ∀ j, w j ≤ (Real.log 2)⁻¹ := by
    intro j
    have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : (0 : ℝ) ≤ (Real.log 2)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    rw [mul_one] at this
    exact this
  have hwmul : ∀ j, (2 : ℝ) ^ j * Real.log 2 * w j = 1 := by
    intro j
    rw [hw]
    simp only
    field_simp
    rw [div_pow, one_pow]
    field_simp
  -- the `A`-lower bound at the tower cutoffs
  have hAlow : ∀ j, c * ((2 : ℝ) ^ j * Real.log 2) - C ≤ A j := by
    intro j
    have := h (NN j) (two_le_NN j)
    rwa [log_NN] at this
  -- one step
  have hstep : ∀ j, (A (j + 1) - A j) * w (j + 1) ≤ F (j + 1) - F j := by
    intro j
    have := step_le (S := S) j
    rw [div_eq_mul_inv] at this
    have he : ((2 : ℝ) ^ (j + 1) * Real.log 2)⁻¹ = w (j + 1) := by
      rw [hw]; simp only; rw [mul_inv, div_pow, one_pow]; field_simp
    rwa [he] at this
  refine ⟨2 * |C| * (Real.log 2)⁻¹ + |A 0| * (Real.log 2)⁻¹, fun J => ?_⟩
  have hsum : ∑ j ∈ Finset.range J, (A (j + 1) - A j) * w (j + 1) ≤ F J - F 0 := by
    calc ∑ j ∈ Finset.range J, (A (j + 1) - A j) * w (j + 1)
        ≤ ∑ j ∈ Finset.range J, (F (j + 1) - F j) := Finset.sum_le_sum fun j _ => hstep j
      _ = F J - F 0 := Finset.sum_range_sub F J
  rw [abel_parts A w J] at hsum
  -- the three lower bounds
  have hwsub : ∀ j, w j - w (j + 1) = w (j + 1) := by
    intro j; rw [hw]; simp only [pow_succ]; ring
  have hterm : ∀ j ∈ Finset.range J, c / 2 - |C| * w (j + 1) ≤ A j * (w j - w (j + 1)) := by
    intro j _
    rw [hwsub j]
    have h1 : (c * ((2 : ℝ) ^ j * Real.log 2) - C) * w (j + 1) ≤ A j * w (j + 1) :=
      mul_le_mul_of_nonneg_right (hAlow j) (hwpos (j + 1)).le
    have h2 : c * ((2 : ℝ) ^ j * Real.log 2) * w (j + 1) = c / 2 := by
      have : (2 : ℝ) ^ j * Real.log 2 * w (j + 1) = 1 / 2 := by
        have := hwmul (j + 1)
        rw [pow_succ] at this
        nlinarith [this]
      nlinarith [this]
    have h3 : -(C * w (j + 1)) ≥ -(|C| * w (j + 1)) := by
      have := le_abs_self C
      nlinarith [(hwpos (j + 1)).le]
    nlinarith [h1, h2, h3]
  have hgeom : ∑ j ∈ Finset.range J, |C| * w (j + 1) ≤ |C| * (Real.log 2)⁻¹ := by
    have hgeo : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := by
      have key : ∀ n : ℕ, ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) = 1 - (1 / 2 : ℝ) ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
      rw [key J]
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := by positivity
      linarith
    calc ∑ j ∈ Finset.range J, |C| * w (j + 1)
        = |C| * (Real.log 2)⁻¹ * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ (j + 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [hw]; ring
      _ ≤ |C| * (Real.log 2)⁻¹ * 1 := by
          have : (0 : ℝ) ≤ |C| * (Real.log 2)⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left hgeo this
      _ = |C| * (Real.log 2)⁻¹ := by ring
  have hbig : c / 2 * J - |C| * (Real.log 2)⁻¹ ≤ ∑ j ∈ Finset.range J, A j * (w j - w (j + 1)) := by
    calc c / 2 * J - |C| * (Real.log 2)⁻¹
        ≤ ∑ j ∈ Finset.range J, (c / 2) - ∑ j ∈ Finset.range J, |C| * w (j + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          linarith [hgeom]
      _ = ∑ j ∈ Finset.range J, (c / 2 - |C| * w (j + 1)) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ j ∈ Finset.range J, A j * (w j - w (j + 1)) := Finset.sum_le_sum hterm
  have hAJ : -(|C| * (Real.log 2)⁻¹) ≤ A J * w J := by
    have h1 : (c * ((2 : ℝ) ^ J * Real.log 2) - C) * w J ≤ A J * w J :=
      mul_le_mul_of_nonneg_right (hAlow J) (hwpos J).le
    have h2 : c * ((2 : ℝ) ^ J * Real.log 2) * w J = c := by nlinarith [hwmul J]
    have h3 : C * w J ≤ |C| * (Real.log 2)⁻¹ := by
      have hc1 : C * w J ≤ |C| * w J := mul_le_mul_of_nonneg_right (le_abs_self C) (hwpos J).le
      have hc2 : |C| * w J ≤ |C| * (Real.log 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (hwle J) (abs_nonneg C)
      linarith
    nlinarith [h1, h2, h3]
  have hA0 : A 0 * w 0 ≤ |A 0| * (Real.log 2)⁻¹ := by
    have hc1 : A 0 * w 0 ≤ |A 0| * w 0 := mul_le_mul_of_nonneg_right (le_abs_self _) (hwpos 0).le
    have hc2 : |A 0| * w 0 ≤ |A 0| * (Real.log 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (hwle 0) (abs_nonneg _)
    linarith
  have hF0 : 0 ≤ F 0 := sumInvPrimesIn_nonneg _
  linarith [hsum, hbig, hAJ, hA0, hF0]

/-- **Leaf.**  Partial summation: `1/p = (log p / p)·(log p)⁻¹`, so a linear-in-`log N` lower
bound for `A_S` gives a `log log N` lower bound for the reciprocal sum (with the constant
degraded by the dyadic step, which the schedule tolerates). -/
theorem mertensRate_of_sumLog {c C : ℝ} (hc : 0 < c)
    (h : ∀ N : ℕ, 2 ≤ N → c * Real.log N - C ≤ sumLogPrimesIn S N) :
    ∃ c' C' : ℝ, 0 < c' ∧ MertensRate S c' C' := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨D, hD⟩ := tower_lower hc h
  have hcp : 0 < c / (2 * Real.log 2) := div_pos hc (by linarith)
  refine ⟨c / (2 * Real.log 2), D + c / 2, hcp, hcp, fun N hN => ?_⟩
  set u : ℕ := Nat.log 2 N with hu
  set J : ℕ := Nat.log 2 u with hJ
  have hN0 : N ≠ 0 := by omega
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact Nat.log_pos (by norm_num) hN
  have hu0 : u ≠ 0 := by omega
  -- `NN J ≤ N`
  have hpowJ : 2 ^ J ≤ u := Nat.pow_log_le_self 2 hu0
  have hNNle : NN J ≤ N := by
    calc NN J = 2 ^ 2 ^ J := rfl
      _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hpowJ
      _ ≤ N := Nat.pow_log_le_self 2 hN0
  have hmono : sumInvPrimesIn S (NN J) ≤ sumInvPrimesIn S N := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp ⊢
    exact ⟨⟨lt_of_lt_of_le hp.1.1 hNNle, hp.1.2⟩, hp.2⟩
  -- `log log N ≤ (J+1) log 2`
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hNR)
  have h1 : (N : ℝ) ≤ (2 : ℝ) ^ (u + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    have : N ≤ 2 ^ (u + 1) := by rw [hu]; omega
    exact_mod_cast this
  have h2 : u + 1 ≤ 2 ^ (J + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) u
    rw [hJ]; omega
  have h3 : Real.log N ≤ (2 : ℝ) ^ (J + 1) * Real.log 2 := by
    have hA : Real.log N ≤ ((u : ℝ) + 1) * Real.log 2 := by
      have := Real.log_le_log (show (0:ℝ) < N by linarith) h1
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hB : ((u : ℝ) + 1) ≤ (2 : ℝ) ^ (J + 1) := by exact_mod_cast h2
    nlinarith [hlog2.le]
  have h4 : Real.log (Real.log N) ≤ ((J : ℝ) + 1) * Real.log 2 := by
    have := Real.log_le_log hlogN h3
    rw [Real.log_mul (by positivity) hlog2.ne'] at this
    have h5 : Real.log ((2 : ℝ) ^ (J + 1)) = ((J : ℝ) + 1) * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    have h6 : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith [Real.log_two_lt_d9])
    linarith [h5 ▸ this]
  have hJge : Real.log (Real.log N) / Real.log 2 - 1 ≤ (J : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hlog2]
    linarith [h4]
  have := hD J
  have hfin : c / (2 * Real.log 2) * Real.log (Real.log N) - (D + c / 2) ≤ c / 2 * J - D := by
    have : c / 2 * (Real.log (Real.log N) / Real.log 2 - 1) ≤ c / 2 * J :=
      mul_le_mul_of_nonneg_left hJge (by positivity)
    have he : c / 2 * (Real.log (Real.log N) / Real.log 2 - 1)
        = c / (2 * Real.log 2) * Real.log (Real.log N) - c / 2 := by
      field_simp
    linarith [he ▸ this]
  unfold MertensRate at *
  linarith [hmono, hD J, hfin]

/-! ### The residue-class instance -/

section ResidueClass

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Leaf.**  The hypothesis of `sumLog_ge_of_LSeries_ge` for `S = {p : p ≡ a (q)}`, obtained
from `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` after discarding the
prime-power part (`summable_residueClass_non_primes_div`, uniformly `O(1)` for `x ≥ 1`). -/
theorem LSeries_residueClass_primes_ge (ha : IsUnit a) :
    ∃ C₀ : ℝ, ∀ x : ℝ, 1 < x → x ≤ 2 →
      ((q.totient : ℝ)⁻¹) / (x - 1) - C₀
        ≤ ∑' n : ℕ, (if n.Prime ∧ (n : ZMod q) = a then Real.log n else 0) / (n : ℝ) ^ x := by
  sorry

/-- **Mertens in arithmetic progressions, in the form the schedule needs.**  Not in mathlib;
assembled here from the `L`-series lower bound plus Chebyshev and two partial summations. -/
theorem mertensRate_residueClass (ha : IsUnit a) :
    ∃ c C : ℝ, MertensRate (fun p => (p : ZMod q) = a) c C := by
  obtain ⟨C₀, hC₀⟩ := LSeries_residueClass_primes_ge ha
  obtain ⟨c', C', hc', hA⟩ :=
    sumLog_ge_of_LSeries_ge (S := fun p => (p : ZMod q) = a)
      (inv_pos.mpr (mod_cast q.totient.pos_of_neZero)) hC₀
  obtain ⟨c'', C'', hc'', hM⟩ := mertensRate_of_sumLog hc' hA
  exact ⟨c'', C'', hM⟩

end ResidueClass

end NormalNumbers.G4.MertensAP
