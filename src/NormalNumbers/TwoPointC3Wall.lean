/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Split
import NormalNumbers.TwoPointDelangeOmega

/-!
# Rung 2 of the C3 depth ladder: the wall

`DIRECTION.md`'s rung 2.  The C3 crux is about the large-prime tail
`T_n = tailLarge P b n = ∑_{i≥1} ω_{>P}(n+i)·b^{−i}`, and every route that truncates the tail at
a **fixed** depth `K` is doomed, because the mean of `T_n` itself is unbounded:

    (1/N) ∑_{n<N} tailLarge P b n  →  ∞ .

This file proves that, unconditionally, for every `b ≥ 2` and every prime cut `P`.  It is the
kernel fact that turns "the peel must grow with `N`" from a heuristic into a theorem: a
fixed-depth truncation controls a quantity of bounded mean, while the object it approximates has
mean `→ ∞`, so the approximation error cannot be uniformly small.

The proof needs only the **`i = 1` term** of the tail and Mertens' second theorem in divergence
form (`tendsto_delangeL_atTop`, in-tree):

    (1/N) ∑_{n<N} T_n ≥ (1/(bN)) ∑_{n<N} ω_{>P}(n+1)
                       = (1/(bN)) ∑_{P<p≤N} ⌊N/p⌋
                       ≥ (1/b) (∑_{p≤N} 1/p − ∑_{p≤P} 1/p − 2) → ∞ .

The true rate is `(log log N)/(b−1)`, from summing all `i`; the crude divergence above is all any
consumer needs.
-/

open Filter Topology Finset

namespace NormalNumbers.CastingOut

open PrimeLambert

/-! ### Counting the large prime factors of `n+1`, `n < N` -/

/-- The primes in `(P, N]`. -/
noncomputable def primesBigLe (P N : ℕ) : Finset ℕ :=
  open Classical in (primesLe N).filter (fun p => ¬ p ≤ P)

/-- For `1 ≤ m ≤ N`, the large prime factors of `m` are exactly the primes in `(P, N]` dividing
`m`.  (`≤ N` is what lets the ambient set be independent of `m`, which is what makes the double
count possible.) -/
lemma omegaLarge_eq_card_primesBigLe {P N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    omegaLarge P m = ((primesBigLe P N).filter (fun p => p ∣ m)).card := by
  classical
  have hset : (m.primeFactors.filter (fun p => ¬ p ≤ P))
      = ((primesBigLe P N).filter (fun p => p ∣ m)) := by
    ext p
    simp only [primesBigLe, Finset.mem_filter, Nat.mem_primeFactors, primesLe, Finset.mem_range]
    constructor
    · rintro ⟨⟨hpp, hpd, -⟩, hPp⟩
      exact ⟨⟨⟨by have := Nat.le_of_dvd (by omega) hpd; omega, hpp⟩, hPp⟩, hpd⟩
    · rintro ⟨⟨⟨-, hpp⟩, hPp⟩, hpd⟩
      exact ⟨⟨hpp, hpd, by omega⟩, hPp⟩
  rw [omegaLarge, hset]

/-- **The double count.**  `∑_{n<N} ω_{>P}(n+1) = ∑_{P<p≤N} ⌊N/p⌋`. -/
lemma sum_omegaLarge_succ (P N : ℕ) :
    ∑ n ∈ range N, omegaLarge P (n + 1) = ∑ p ∈ primesBigLe P N, N / p := by
  classical
  have hleft : ∀ n ∈ range N, omegaLarge P (n + 1)
      = ((primesBigLe P N).filter (fun p => p ∣ (n + 1))).card := by
    intro n hn
    exact omegaLarge_eq_card_primesBigLe (by omega) (by have := mem_range.1 hn; omega)
  rw [Finset.sum_congr rfl hleft]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.card_filter]
  exact Nat.card_multiples N p

/-! ### From the double count to divergence -/

/-- Only the `i = 1` term of the tail is needed. -/
lemma tailLarge_ge_first {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) :
    (omegaLarge P (n + 1) : ℝ) / (b : ℝ) ≤ tailLarge P b n := by
  have hterm := (summable_tailLarge hb P n).le_tsum 0 (fun i _ => by positivity)
  simpa [tailLarge, pow_one] using hterm

/-- Nat division loses at most one. -/
lemma cast_div_ge {N p : ℕ} (hp : 0 < p) : (N : ℝ) / (p : ℝ) - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmod := Nat.div_add_mod N p
  have hlt : N % p < p := Nat.mod_lt _ hp
  have h1 : (N : ℝ) = (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) := by
    exact_mod_cast hmod.symm
  have h2 : ((N % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hlt
  rw [sub_le_iff_le_add, div_le_iff₀ hpR]
  nlinarith

/-- The primes in `(P, N]` carry at least `∑_{p≤N}1/p − ∑_{p≤P}1/p` of harmonic weight. -/
lemma sum_inv_primesBigLe_ge (P N : ℕ) :
    delangeL N - delangeL P ≤ ∑ p ∈ primesBigLe P N, 1 / (p : ℝ) := by
  classical
  have hsplit : delangeL N
      = ∑ p ∈ primesBigLe P N, 1 / (p : ℝ)
        + ∑ p ∈ (primesLe N).filter (fun p => p ≤ P), 1 / (p : ℝ) := by
    rw [delangeL, primesBigLe, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (primesLe N) (fun p => p ≤ P) _).symm
  have hsmall : ∑ p ∈ (primesLe N).filter (fun p => p ≤ P), 1 / (p : ℝ) ≤ delangeL P := by
    rw [delangeL]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [primesLe, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, prime_of_mem_primesLe hp.1⟩
  linarith

lemma card_primesBigLe_le (P N : ℕ) : ((primesBigLe P N).card : ℝ) ≤ (N : ℝ) + 1 := by
  classical
  have h1 : (primesBigLe P N).card ≤ (primesLe N).card :=
    Finset.card_filter_le _ _
  have h2 : (primesLe N).card ≤ N + 1 := by
    rw [primesLe]
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  have : (primesBigLe P N).card ≤ N + 1 := le_trans h1 h2
  exact_mod_cast this

/-- **The quantitative wall.**  `(1/N) ∑_{n<N} T_n ≥ (∑_{p≤N}1/p − ∑_{p≤P}1/p − 2)/b`. -/
theorem sum_tailLarge_lower {b : ℕ} (hb : 2 ≤ b) (P N : ℕ) (hN : 1 ≤ N) :
    (delangeL N - delangeL P - 2) / (b : ℝ)
      ≤ (∑ n ∈ range N, tailLarge P b n) / (N : ℝ) := by
  classical
  have hbR : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- step 1: drop to the `i = 1` term
  have h1 : (∑ n ∈ range N, (omegaLarge P (n + 1) : ℝ)) / (b : ℝ)
      ≤ ∑ n ∈ range N, tailLarge P b n := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun n _ => tailLarge_ge_first hb P n
  -- step 2: the double count
  have h2 : (∑ n ∈ range N, (omegaLarge P (n + 1) : ℝ))
      = ∑ p ∈ primesBigLe P N, ((N / p : ℕ) : ℝ) := by
    have h := sum_omegaLarge_succ P N
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
  -- step 3: nat division, and Mertens
  have h3 : (N : ℝ) * (delangeL N - delangeL P) - ((N : ℝ) + 1)
      ≤ ∑ p ∈ primesBigLe P N, ((N / p : ℕ) : ℝ) := by
    have hlow : ∀ p ∈ primesBigLe P N,
        (N : ℝ) * (1 / (p : ℝ)) - 1 ≤ ((N / p : ℕ) : ℝ) := by
      intro p hp
      have hpp : p.Prime := prime_of_mem_primesLe (Finset.mem_filter.mp hp).1
      have := cast_div_ge (N := N) hpp.pos
      calc (N : ℝ) * (1 / (p : ℝ)) - 1 = (N : ℝ) / (p : ℝ) - 1 := by ring
        _ ≤ _ := this
    have hsum := Finset.sum_le_sum hlow
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    have hcard : ∑ _p ∈ primesBigLe P N, (1 : ℝ) = ((primesBigLe P N).card : ℝ) := by simp
    rw [hcard] at hsum
    have hmert := sum_inv_primesBigLe_ge P N
    have hc := card_primesBigLe_le P N
    nlinarith [hsum, hmert, hc, hNR.le]
  -- assemble
  have hkey : (N : ℝ) * (delangeL N - delangeL P - 2)
      ≤ ∑ n ∈ range N, (omegaLarge P (n + 1) : ℝ) := by
    have hN1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    rw [h2]
    nlinarith [h3]
  rw [div_le_div_iff₀ hbR hNR]
  have hstep : (delangeL N - delangeL P - 2) * (N : ℝ)
      ≤ (∑ n ∈ range N, (omegaLarge P (n + 1) : ℝ)) := by
    rw [mul_comm]; exact hkey
  have h1' : (∑ n ∈ range N, (omegaLarge P (n + 1) : ℝ))
      ≤ (∑ n ∈ range N, tailLarge P b n) * (b : ℝ) := by
    rw [← div_le_iff₀ hbR] at *
    linarith [h1]
  linarith

/-- **Rung 2.**  The mean of the large-prime tail diverges.  Hence no truncation of the tail at a
FIXED depth can control it: the truncated mean is bounded (by `∑_{i≤K} ω/b^i` with `ω` of bounded
mean — indeed the depth-`K` truncation has mean `O_K(log log N)` only through the same mechanism),
while the full tail's mean is unbounded.  The peel must grow with `N`. -/
theorem tendsto_mean_tailLarge_atTop {b : ℕ} (hb : 2 ≤ b) (P : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, tailLarge P b n) / (N : ℝ)) atTop atTop := by
  have hbR : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hlow : Tendsto (fun N : ℕ => (delangeL N - delangeL P - 2) / (b : ℝ)) atTop atTop := by
    have h2 : Tendsto (fun N : ℕ => delangeL N + (-(delangeL P) - 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_delangeL_atTop
    exact (h2.congr (fun N => by ring)).atTop_div_const hbR
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact sum_tailLarge_lower hb P N hN

end NormalNumbers.CastingOut
