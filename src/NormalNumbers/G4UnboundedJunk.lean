/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightJunk

/-!
# Campaign B: the junk estimate with the coefficients kept **inside** the sum

`G4WeightJunk.sum_junk_le` prices the junk of `w_c = ω + excess c` against a *uniform* bound
`c_p ≤ C`.  That uniform bound is one of exactly two places where the closed headline
`isDisjunctive_weight` needs `c` bounded (the other is the far field's `w_c ≤ (max C 1)·Ω`), so
removing it is campaign B's first obligation.

This module re-proves the estimate with the coefficients inside.  With `N = X + ρ`:

  `∑_{n∈P} junk_c(n+ρ) ≤ (X/P₀)·( ∑_{p∣P₀} c_p/(p−1) + ∑_{p<N+1} c_p/(p(p−1)) )
                          + log₂(N)·∑_{p<√N+1} c_p`.

Nothing in the proof of `sum_junk_le` used boundedness except to pull `C` out of the two sums,
so the `C`-free statement is the honest one and it exposes exactly two hypotheses on `c`:

* a **tail condition** — `∑_p c_p/(p(p−1))` must be bounded (morally `∑_p c_p/p² < ∞`);
* a **growth condition** — the prime prefix sum `∑_{p ≤ √N} c_p` must be `o(N/log N)`, i.e.
  `c_p = o(p)` on average.  This is the binding one: it is *not* implied by the tail condition.

`sum_junk_le` is the case `c_p ≤ C` (`∑_{p<N+1} C/(p(p−1)) ≤ C` by `sum_inv_mul_pred_le`, and
`∑_{p<√N+1} C ≤ C·(√N+1)`), recovered in `sum_junk_le_of_bounded`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

open NormalNumbers.G4

/-- The prime powers `p^{E'_p+u} ≤ N` with `u ≥ 1` live in `{p < √N+1 prime} × [1, log₂ N]` —
the `Finset`-level form of `card_filter_pow_le`, keeping primality so the `+1`s can be weighted
by `c_p`. -/
lemma filter_pow_subset_primesBelow {N P₀ : ℕ} :
    ((N + 1).primesBelow ×ˢ Icc 1 N).filter
        (fun pu : ℕ × ℕ => pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) ≤ N)
      ⊆ (Nat.sqrt N + 1).primesBelow ×ˢ Icc 1 (Nat.log 2 N) := by
  intro pu hpu
  obtain ⟨hmem, hle⟩ := Finset.mem_filter.1 hpu
  obtain ⟨hp, hu⟩ := Finset.mem_product.1 hmem
  have hpp := (Nat.mem_primesBelow.1 hp).2
  have hu1 := (Finset.mem_Icc.1 hu).1
  have hE := one_le_frozenDepth P₀ pu.1
  refine Finset.mem_product.2 ⟨Nat.mem_primesBelow.2 ⟨Nat.lt_succ_of_le ?_, hpp⟩,
    Finset.mem_Icc.2 ⟨hu1, ?_⟩⟩
  · rw [Nat.le_sqrt']
    calc pu.1 ^ 2 ≤ pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) :=
          Nat.pow_le_pow_right hpp.pos (by omega)
      _ ≤ N := hle
  · refine Nat.le_log_of_pow_le (by norm_num) ?_
    calc 2 ^ pu.2 ≤ pu.1 ^ pu.2 := Nat.pow_le_pow_left hpp.two_le _
      _ ≤ pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) := Nat.pow_le_pow_right hpp.pos (by omega)
      _ ≤ N := hle

/-- **The sample sum of the junk, with no uniform bound on `c`.**  For
`P = {n < X : n ≡ b₀ (P₀)}`, any shift `ρ ≥ 1` and `N = X + ρ`,

  `∑_{n∈P} junk_c(n+ρ) ≤ (X/P₀)·(∑_{p∣P₀} c_p/(p−1) + ∑_{p<N+1} c_p/(p(p−1)))
                          + log₂(N)·∑_{p<√N+1} c_p`. -/
theorem sum_junk_le' (c : ℕ → ℕ) {X P₀ b₀ ρ : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) :
    ∑ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ)
      ≤ (X : ℝ) / P₀ * ((∑ p ∈ P₀.primeFactors, (c p : ℝ) / ((p : ℝ) - 1))
            + ∑ p ∈ (X + ρ + 1).primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
        + (Nat.log 2 (X + ρ) : ℝ) * ∑ p ∈ (Nat.sqrt (X + ρ) + 1).primesBelow, (c p : ℝ) := by
  classical
  set N := X + ρ with hN
  set pb := (N + 1).primesBelow with hpb
  set A := (pb ×ˢ Icc 1 N).filter
    (fun pu : ℕ × ℕ => pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) ≤ N) with hA
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  rw [sum_junk_eq_sum_junkCount c hρ]
  -- restrict to `A`: outside it the count vanishes
  have hres : ∑ pu ∈ pb ×ˢ Icc 1 N, (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2
      = ∑ pu ∈ A, (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2 := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun pu _ => ?_
    split_ifs with h
    · rfl
    · rw [junkCount_eq_zero hρ (by omega), mul_zero]
  rw [hres]
  -- term-by-term, keeping `c_p` where it is
  have hterm : ∀ pu ∈ A, (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2
      ≤ (c pu.1 : ℝ) * (1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1))
            * ((X : ℝ) / P₀)) + (c pu.1 : ℝ) := by
    intro pu hpu
    have hpp := (Nat.mem_primesBelow.1 (Finset.mem_product.1 (Finset.mem_filter.1 hpu).1).1).2
    have hcount := card_filter_pow_dvd_le (X := X) (b₀ := b₀) (ρ := ρ) hpp hP₀ pu.2
    have hpr : (0 : ℝ) < (pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1) := by
      have : (0 : ℝ) < pu.1 := by exact_mod_cast hpp.pos
      positivity
    have hcount' : junkCount X P₀ b₀ ρ pu.1 pu.2
        ≤ 1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1)) * ((X : ℝ) / P₀)
          + 1 := by
      unfold junkCount
      refine hcount.trans (le_of_eq ?_)
      field_simp
    calc (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2
        ≤ (c pu.1 : ℝ) * (1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1))
            * ((X : ℝ) / P₀) + 1) := mul_le_mul_of_nonneg_left hcount' (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · -- the main term: extend to the full product, sum the geometric series at each prime
    have hext : ∑ pu ∈ A, (c pu.1 : ℝ)
            * (1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1))
              * ((X : ℝ) / P₀))
        ≤ ∑ pu ∈ pb ×ˢ Icc 1 N, (c pu.1 : ℝ)
            * (1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1))
              * ((X : ℝ) / P₀)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun pu _ _ => by positivity
    refine hext.trans ?_
    rw [Finset.sum_product]
    have hstep : ∀ p ∈ pb, ∑ u ∈ Icc 1 N, (c p : ℝ)
          * (1 / ((p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p)) * ((X : ℝ) / P₀))
        ≤ (X : ℝ) / P₀ * ((c p : ℝ)
            * (if p ∣ P₀ then 1 / ((p : ℝ) - 1) else 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
      intro p hp
      have hpp := (Nat.mem_primesBelow.1 hp).2
      have hgeo := sum_inv_pow_shift_le hpp P₀ N
      rw [main_term_le hpp P₀ hP₀.ne'] at hgeo
      have hrw : ∑ u ∈ Icc 1 N, (c p : ℝ)
            * (1 / ((p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p)) * ((X : ℝ) / P₀))
          = (c p : ℝ) * ((X : ℝ) / P₀) * ∑ u ∈ Icc 1 N,
              1 / ((p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [hrw]
      calc (c p : ℝ) * ((X : ℝ) / P₀) * ∑ u ∈ Icc 1 N,
              1 / ((p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p))
          ≤ (c p : ℝ) * ((X : ℝ) / P₀)
              * (if p ∣ P₀ then 1 / ((p : ℝ) - 1) else 1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsplit : ∑ p ∈ pb, (c p : ℝ)
          * (if p ∣ P₀ then 1 / ((p : ℝ) - 1) else 1 / ((p : ℝ) * ((p : ℝ) - 1)))
        = (∑ p ∈ pb.filter (fun p => p ∣ P₀), (c p : ℝ) / ((p : ℝ) - 1))
          + ∑ p ∈ pb.filter (fun p => ¬ p ∣ P₀), (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [← Finset.sum_filter_add_sum_filter_not pb (fun p => p ∣ P₀)]
      congr 1
      · exact Finset.sum_congr rfl fun p hp => by
          rw [if_pos (Finset.mem_filter.1 hp).2]; ring
      · exact Finset.sum_congr rfl fun p hp => by
          rw [if_neg (Finset.mem_filter.1 hp).2]; ring
    rw [hsplit]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
      · intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
        exact Nat.mem_primeFactors.2 ⟨(Nat.mem_primesBelow.1 hp1).2, hp2, hP₀.ne'⟩
      · have h2 := (Nat.mem_primeFactors.1 hp).1.two_le
        have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
    · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ => ?_
      have h2 := (Nat.mem_primesBelow.1 hp).2.two_le
      have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
  · -- the `+1`s, weighted by `c_p`
    calc ∑ pu ∈ A, (c pu.1 : ℝ)
        ≤ ∑ pu ∈ (Nat.sqrt N + 1).primesBelow ×ˢ Icc 1 (Nat.log 2 N), (c pu.1 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg filter_pow_subset_primesBelow
            fun pu _ _ => by positivity
      _ = (Nat.log 2 N : ℝ) * ∑ p ∈ (Nat.sqrt N + 1).primesBelow, (c p : ℝ) := by
          rw [Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]

/-! ### The `C`-free shift bound, and the recovery of `sum_junk_le` -/

lemma primesBelow_mono {m n : ℕ} (h : m ≤ n) : m.primesBelow ⊆ n.primesBelow := fun p hp =>
  Nat.mem_primesBelow.2 ⟨lt_of_lt_of_le (Nat.mem_primesBelow.1 hp).1 h, (Nat.mem_primesBelow.1 hp).2⟩

lemma primesBelow_subset_range (n : ℕ) : n.primesBelow ⊆ Finset.range n := fun p hp =>
  Finset.mem_range.2 (Nat.mem_primesBelow.1 hp).1

/-- The `C`-free replacement for `C · junkShiftBound P₀ X ρmax`: the right-hand side of
`sum_junk_le'` at the worst shift, with the coefficients kept inside. -/
noncomputable def junkShiftBoundC (c : ℕ → ℕ) (P₀ X ρmax : ℕ) : ℝ :=
  (X : ℝ) / P₀ * ((∑ p ∈ P₀.primeFactors, (c p : ℝ) / ((p : ℝ) - 1))
      + ∑ p ∈ (X + ρmax + 1).primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
    + (Nat.log 2 (X + ρmax) : ℝ) * ∑ p ∈ (Nat.sqrt (X + ρmax) + 1).primesBelow, (c p : ℝ)

lemma junkShiftBoundC_nonneg (c : ℕ → ℕ) (P₀ X ρmax : ℕ) :
    0 ≤ junkShiftBoundC c P₀ X ρmax := by
  unfold junkShiftBoundC
  have h1 : (0 : ℝ) ≤ ∑ p ∈ P₀.primeFactors, (c p : ℝ) / ((p : ℝ) - 1) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have h2 := (Nat.mem_primeFactors.1 hp).1.two_le
    have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have h2 : (0 : ℝ) ≤ ∑ p ∈ (X + ρmax + 1).primesBelow,
      (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have h2 := (Nat.mem_primesBelow.1 hp).2.two_le
    have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have h3 : (0 : ℝ) ≤ ∑ p ∈ (Nat.sqrt (X + ρmax) + 1).primesBelow, (c p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  positivity

/-- **The sample sum of the junk at any shift `1 ≤ ρ ≤ ρmax`, with no bound on `c`.**  The
`C`-free analogue of `G4WeightJunkAvg.sum_junk_C_le`. -/
theorem sum_junk_C_le' (c : ℕ → ℕ) {X P₀ b₀ ρ ρmax : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ)
    (hρm : ρ ≤ ρmax) :
    ∑ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ) ≤ junkShiftBoundC c P₀ X ρmax := by
  refine (sum_junk_le' c (b₀ := b₀) hP₀ hρ).trans ?_
  unfold junkShiftBoundC
  have hpb : ∑ p ∈ (X + ρ + 1).primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ (X + ρmax + 1).primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (primesBelow_mono (by omega)) fun p hp _ => ?_
    have h2 := (Nat.mem_primesBelow.1 hp).2.two_le
    have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hsq : ∑ p ∈ (Nat.sqrt (X + ρ) + 1).primesBelow, (c p : ℝ)
      ≤ ∑ p ∈ (Nat.sqrt (X + ρmax) + 1).primesBelow, (c p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (primesBelow_mono (by have := Nat.sqrt_le_sqrt (show X + ρ ≤ X + ρmax by omega); omega))
      fun p _ _ => by positivity
  have hlog : (Nat.log 2 (X + ρ) : ℝ) ≤ (Nat.log 2 (X + ρmax) : ℝ) := by
    exact_mod_cast Nat.log_mono_right (show X + ρ ≤ X + ρmax by omega)
  have hsq0 : (0 : ℝ) ≤ ∑ p ∈ (Nat.sqrt (X + ρ) + 1).primesBelow, (c p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hlog0 : (0 : ℝ) ≤ (Nat.log 2 (X + ρ) : ℝ) := by positivity
  have hXP : (0 : ℝ) ≤ (X : ℝ) / P₀ := by positivity
  have : (Nat.log 2 (X + ρ) : ℝ) * ∑ p ∈ (Nat.sqrt (X + ρ) + 1).primesBelow, (c p : ℝ)
      ≤ (Nat.log 2 (X + ρmax) : ℝ) * ∑ p ∈ (Nat.sqrt (X + ρmax) + 1).primesBelow, (c p : ℝ) := by
    calc (Nat.log 2 (X + ρ) : ℝ) * ∑ p ∈ (Nat.sqrt (X + ρ) + 1).primesBelow, (c p : ℝ)
        ≤ (Nat.log 2 (X + ρ) : ℝ) * ∑ p ∈ (Nat.sqrt (X + ρmax) + 1).primesBelow, (c p : ℝ) :=
          mul_le_mul_of_nonneg_left hsq hlog0
      _ ≤ _ := mul_le_mul_of_nonneg_right hlog (hsq0.trans hsq)
  nlinarith

/-- **Faithfulness check**: at a uniform bound `c ≤ C` the `C`-free estimate recovers
`G4WeightJunk.sum_junk_le` exactly. -/
theorem sum_junk_le_of_bounded (c : ℕ → ℕ) {C : ℝ} (hC : ∀ p, (c p : ℝ) ≤ C)
    {X P₀ b₀ ρ : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) :
    ∑ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ)
      ≤ C * ((X : ℝ) / P₀ * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1)
          + (((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ) : ℝ)) := by
  classical
  set N := X + ρ with hN
  have hC0 : 0 ≤ C := (by positivity : (0:ℝ) ≤ (c 0 : ℝ)).trans (hC 0)
  refine (sum_junk_le' c (b₀ := b₀) hP₀ hρ).trans ?_
  -- the frozen sum
  have h1 : ∑ p ∈ P₀.primeFactors, (c p : ℝ) / ((p : ℝ) - 1)
      ≤ C * ∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h2 := (Nat.mem_primeFactors.1 hp).1.two_le
    have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hrw : C * (1 / ((p : ℝ) - 1)) = C / ((p : ℝ) - 1) := by ring
    rw [hrw]
    gcongr
    exact hC p
  -- the tail sum: `∑_{p<N+1} c_p/(p(p−1)) ≤ C·∑_{n∈[2,N]} 1/(n(n−1)) ≤ C`
  have h2 : ∑ p ∈ (N + 1).primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ C := by
    have hstep : ∑ p ∈ (N + 1).primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ C * ∑ p ∈ (N + 1).primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have h2 := (Nat.mem_primesBelow.1 hp).2.two_le
      have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
      have hp1 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      have hrw : C * (1 / ((p : ℝ) * ((p : ℝ) - 1))) = C / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
      rw [hrw]
      gcongr
      exact hC p
    have hsub : ∑ p ∈ (N + 1).primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ n ∈ Icc 2 N, 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
      · intro p hp
        have h1 := Nat.mem_primesBelow.1 hp
        exact Finset.mem_Icc.2 ⟨h1.2.two_le, by omega⟩
      · have h2 := (Finset.mem_Icc.1 hn).1
        have h2' : (2 : ℝ) ≤ n := by exact_mod_cast h2
        have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        positivity
    nlinarith [sum_inv_mul_pred_le N]
  -- the `+1`s: at most `√N+1` primes, each weighted by `C`
  have h3 : (Nat.log 2 N : ℝ) * ∑ p ∈ (Nat.sqrt N + 1).primesBelow, (c p : ℝ)
      ≤ C * (((Nat.sqrt N + 1) * Nat.log 2 N : ℕ) : ℝ) := by
    have hcard : ((Nat.sqrt N + 1).primesBelow.card : ℝ) ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) := by
      have := Finset.card_le_card (primesBelow_subset_range (Nat.sqrt N + 1))
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hsum : ∑ p ∈ (Nat.sqrt N + 1).primesBelow, (c p : ℝ)
        ≤ C * ((Nat.sqrt N + 1).primesBelow.card : ℝ) := by
      calc ∑ p ∈ (Nat.sqrt N + 1).primesBelow, (c p : ℝ)
          ≤ ∑ _p ∈ (Nat.sqrt N + 1).primesBelow, C := Finset.sum_le_sum fun p _ => hC p
        _ = C * ((Nat.sqrt N + 1).primesBelow.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hlog0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) := by positivity
    have hpush : (((Nat.sqrt N + 1) * Nat.log 2 N : ℕ) : ℝ)
        = ((Nat.sqrt N + 1 : ℕ) : ℝ) * (Nat.log 2 N : ℝ) := by push_cast; ring
    rw [hpush]
    nlinarith [mul_le_mul_of_nonneg_left hsum hlog0,
      mul_le_mul_of_nonneg_left hcard (mul_nonneg hlog0 hC0)]
  have hXP : (0 : ℝ) ≤ (X : ℝ) / P₀ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) hXP, h3]

/-! ### The hypothesis class: tame coefficients

`sum_junk_le'` exposes exactly two demands on `c`.  `Tame c A` is the smallest package that
meets both with one constant, and it is *strictly* weaker than `c ≤ C`:

* `tail` — `∑_{p<M} c_p/(p(p−1)) ≤ A`, the convergence of `∑_p c_p/p²`;
* `pref` — `∑_{p<M} c_p ≤ A·M`, the prime prefix sums grow at most linearly.

`pref` is Chebyshev-shaped, so it holds for **unbounded** `c`: `c_p = ⌊log₂ p⌋` satisfies it
because `∑_{p≤M} log₂ p = log₂(primorial M) ≤ 2M` (mathlib's `Nat.primorial_le_4_pow`).  A
bounded `c ≤ C` satisfies both with `A = max C 1` (`∑_{p<M} C/(p(p−1)) ≤ C` and
`∑_{p<M} C ≤ C·M`). -/

/-- **Tame coefficients**: the hypothesis class that replaces a uniform bound `c ≤ C`. -/
structure Tame (c : ℕ → ℕ) (A : ℝ) : Prop where
  /-- the constant is at least one -/
  one_le : 1 ≤ A
  /-- the tail condition: `∑_p c_p/p²` converges, uniformly in the cutoff -/
  tail : ∀ M : ℕ, ∑ p ∈ M.primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ A
  /-- the growth condition: the prime prefix sums are at most linear -/
  pref : ∀ M : ℕ, ∑ p ∈ M.primesBelow, (c p : ℝ) ≤ A * M

lemma Tame.nonneg {c : ℕ → ℕ} {A : ℝ} (h : Tame c A) : 0 ≤ A := by linarith [h.one_le]

/-- A tame `c` grows at most linearly at each prime — enough for the Lambert series to
converge at every base `b ≥ 2`. -/
lemma Tame.coeff_le {c : ℕ → ℕ} {A : ℝ} (h : Tame c A) {p : ℕ} (hp : p.Prime) :
    (c p : ℝ) ≤ A * ((p : ℝ) + 1) := by
  have hmem : p ∈ (p + 1).primesBelow := Nat.mem_primesBelow.2 ⟨by omega, hp⟩
  have hsingle := Finset.single_le_sum (f := fun q : ℕ => (c q : ℝ))
    (fun q _ => by positivity) hmem
  have h2 := h.pref (p + 1)
  push_cast at h2
  linarith

/-- A uniformly bounded `c` is tame with `A = max C 1`. -/
theorem tame_of_bounded {c : ℕ → ℕ} {C : ℕ} (hC : ∀ p, c p ≤ C) :
    Tame c ((max C 1 : ℕ) : ℝ) := by
  have hC1 : (1 : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right C 1
  have hCC : (C : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left C 1
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  refine ⟨hC1, fun M => ?_, fun M => ?_⟩
  · have hstep : ∑ p ∈ M.primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ p ∈ M.primesBelow, (C : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h2 := (Nat.mem_primesBelow.1 hp).2.two_le
      have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
      have hp1 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      have hrw : (C : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) = (C : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
        by ring
      rw [hrw]
      gcongr
      exact_mod_cast hC p
    have hsub : ∑ p ∈ M.primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ n ∈ Icc 2 M, 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
      · intro p hp
        have h1 := Nat.mem_primesBelow.1 hp
        exact Finset.mem_Icc.2 ⟨h1.2.two_le, by omega⟩
      · have h2 := (Finset.mem_Icc.1 hn).1
        have h2' : (2 : ℝ) ≤ n := by exact_mod_cast h2
        have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        positivity
    rw [← Finset.mul_sum] at hstep
    nlinarith [sum_inv_mul_pred_le M]
  · have hstep : ∑ p ∈ M.primesBelow, (c p : ℝ) ≤ ∑ _p ∈ M.primesBelow, ((max C 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum fun p _ => le_trans (by exact_mod_cast hC p) hCC
    have hcard : (M.primesBelow.card : ℝ) ≤ (M : ℝ) := by
      have := Finset.card_le_card (primesBelow_subset_range M)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by positivity
    rw [Finset.sum_const, nsmul_eq_mul] at hstep
    nlinarith

end NormalNumbers.PrimeLambert
