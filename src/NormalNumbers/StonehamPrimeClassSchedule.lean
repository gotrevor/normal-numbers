/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPrimeClassState

/-!
# Multiplicative fixed-gap cells for one prime Stoneham class

The kick-depth pattern for parameters `p ^ s i` is not additively periodic.  It is covariant
under multiplication of the orbit position by a common power of `p`.  Starting from the single
integer cell `[A, A + 1)`, dilation by `p ^ (L * t)`, where `L = ∏ i, s i`, produces an interval
of length `p ^ (L * t)` on which all depth gaps are fixed.

This file packages that scheduling fact and combines it with the cleared-state divisibility from
`StonehamPrimeClassState`.  A complementary cyclotomic relation then makes the rational Stoneham
state integral throughout every dilated cell.  The remaining non-normality argument is purely
analytic: an orbit which shadows a finite grid on intervals of fixed positive upper density
cannot be equidistributed.
-/

namespace NormalNumbers.StonehamPrimeClass

open Finset

/-- The common exponent period used to dilate every `p ^ s i` family simultaneously. -/
def primeClassScalePeriod {r : ℕ} (s : Fin r → ℕ) : ℕ :=
  ∏ i, s i

/-- The increment of the `i`-th kick depth during one common dilation period. -/
def primeClassScaleStep {r : ℕ} (s : Fin r → ℕ) (i : Fin r) : ℕ :=
  ∏ j ∈ (univ : Finset (Fin r)).erase i, s j

/-- A canonical orbit position at which every family has at least one entered kick. -/
def primeClassScheduleSeed {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) : ℕ :=
  ∑ i, u i * p ^ s i

/-- The kick depths at the canonical seed position. -/
def primeClassScheduleDepth {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (i : Fin r) : ℕ :=
  StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i (primeClassScheduleSeed p s u)

/-- A common top depth for the canonical seed.  The sum is deliberately used instead of a
maximum: it is elementary, uniform in the empty family, and bounds every component. -/
def primeClassScheduleTop {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) : ℕ :=
  ∑ i, s i * primeClassScheduleDepth p s u i

/-- The fixed gap from the common top to the `i`-th seed depth. -/
def primeClassScheduleGap {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (i : Fin r) : ℕ :=
  primeClassScheduleTop p s u - s i * primeClassScheduleDepth p s u i

/-- Content anchor: for the singleton `p = 3`, `s = u = 1`, the seed and top depth are both
the expected first kick. -/
theorem primeClassSchedule_singleton_three_anchor :
    primeClassScheduleSeed 3 ![1] ![1] = 3 ∧
      primeClassScalePeriod ![1] = 1 ∧
      primeClassScheduleDepth 3 ![1] ![1] 0 = 1 ∧
      primeClassScheduleTop 3 ![1] ![1] = 1 ∧
      primeClassScheduleGap 3 ![1] ![1] 0 = 0 := by
  norm_num [primeClassScheduleSeed, primeClassScalePeriod, primeClassScheduleDepth,
    StonehamSumsNormal.stonehamK, primeClassScheduleTop, primeClassScheduleGap]

/-- Degenerate-case anchor: the empty family has period one, seed zero, and top zero. -/
theorem primeClassSchedule_empty_anchor (p : ℕ) :
    primeClassScalePeriod (fun i : Fin 0 => Fin.elim0 i) = 1 ∧
      primeClassScheduleSeed p (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) = 0 ∧
      primeClassScheduleTop p (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) = 0 := by
  simp [primeClassScalePeriod, primeClassScheduleSeed, primeClassScheduleTop]

lemma primeClassScaleStep_factorization {r : ℕ} (s : Fin r → ℕ) (i : Fin r) :
    s i * primeClassScaleStep s i = primeClassScalePeriod s := by
  exact mul_prod_erase (univ : Finset (Fin r)) s (mem_univ i)

lemma primeClassScalePeriod_pos {r : ℕ} (s : Fin r → ℕ) (hs : ∀ i, 1 ≤ s i) :
    0 < primeClassScalePeriod s := by
  unfold primeClassScalePeriod
  exact prod_pos fun i _ ↦ lt_of_lt_of_le Nat.zero_lt_one (hs i)

lemma two_le_prime_pow (p s : ℕ) (hp : p.Prime) (hs : 1 ≤ s) : 2 ≤ p ^ s := by
  calc
    2 ≤ p := hp.two_le
    _ = p ^ 1 := by simp
    _ ≤ p ^ s := Nat.pow_le_pow_right hp.pos hs

/-- Exact characterization of a kick depth by its two adjacent thresholds. -/
lemma stonehamK_eq_of_bounds {r : ℕ} (c m : Fin r → ℕ) (i : Fin r) (n K : ℕ)
    (hc : 2 ≤ c i) (hm : 1 ≤ m i) (hK : 1 ≤ K)
    (hlower : m i * c i ^ K ≤ n) (hupper : n < m i * c i ^ (K + 1)) :
    StonehamSumsNormal.stonehamK c m i n = K := by
  apply le_antisymm
  · by_contra hnot
    have hsucc : K + 1 ≤ StonehamSumsNormal.stonehamK c m i n := by omega
    have hentered := (StonehamSumsNormal.le_stonehamK_iff c m i n (K + 1)
      hc hm (by omega)).1 hsucc
    omega
  · exact (StonehamSumsNormal.le_stonehamK_iff c m i n K hc hm hK).2 hlower

/-- A seed kick depth stays exact throughout the dilation of its unit cell. -/
lemma stonehamK_eq_on_primeClass_dilated_unitCell
    (p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (i : Fin r) (A K t n : ℕ)
    (hp : p.Prime) (hs : ∀ j, 1 ≤ s j) (hu : ∀ j, 1 ≤ u j) (hKpos : 1 ≤ K)
    (hK : StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i A = K)
    (hnlower : A * p ^ (primeClassScalePeriod s * t) ≤ n)
    (hnupper : n < (A + 1) * p ^ (primeClassScalePeriod s * t)) :
    StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n =
      K + primeClassScaleStep s i * t := by
  let c : ℕ := p ^ s i
  let q : ℕ := primeClassScaleStep s i * t
  let R : ℕ := p ^ (primeClassScalePeriod s * t)
  have hc : 2 ≤ c := two_le_prime_pow p (s i) hp (hs i)
  have hRpos : 0 < R := pow_pos hp.pos _
  have hscale : c ^ q = R := by
    dsimp only [c, q, R]
    calc
      (p ^ s i) ^ (primeClassScaleStep s i * t) =
          p ^ (s i * (primeClassScaleStep s i * t)) :=
        (pow_mul p (s i) (primeClassScaleStep s i * t)).symm
      _ = p ^ ((s i * primeClassScaleStep s i) * t) := by
        rw [Nat.mul_assoc]
      _ = p ^ (primeClassScalePeriod s * t) := by
        rw [primeClassScaleStep_factorization]
  have hlowerSeed : u i * c ^ K ≤ A := by
    have hle : K ≤ StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i A := by
      rw [hK]
    exact (StonehamSumsNormal.le_stonehamK_iff (fun j ↦ p ^ s j) u i A K
      hc (hu i) hKpos).1 hle
  have hupperSeed : A + 1 ≤ u i * c ^ (K + 1) := by
    have hnext : A < u i * c ^ (K + 1) := by
      simpa only [c, hK] using StonehamSumsNormal.lt_mul_stonehamK_succ
        (fun j ↦ p ^ s j) u i A hc (hu i)
    omega
  have hlower : u i * c ^ (K + q) ≤ n := by
    calc
      u i * c ^ (K + q) = (u i * c ^ K) * c ^ q := by rw [pow_add]; ring
      _ ≤ A * c ^ q := Nat.mul_le_mul_right (c ^ q) hlowerSeed
      _ = A * R := by rw [hscale]
      _ ≤ n := by simpa only [R] using hnlower
  have hupper : n < u i * c ^ ((K + q) + 1) := by
    calc
      n < (A + 1) * R := by simpa only [R] using hnupper
      _ = (A + 1) * c ^ q := by rw [hscale]
      _ ≤ (u i * c ^ (K + 1)) * c ^ q :=
        Nat.mul_le_mul_right (c ^ q) hupperSeed
      _ = u i * c ^ ((K + q) + 1) := by
        calc
          (u i * c ^ (K + 1)) * c ^ q =
              u i * (c ^ (K + 1) * c ^ q) := by rw [mul_assoc]
          _ = u i * c ^ ((K + 1) + q) := by
            congr 1
            exact (pow_add c (K + 1) q).symm
          _ = u i * c ^ ((K + q) + 1) := by
            congr 2
            omega
  exact stonehamK_eq_of_bounds (fun j ↦ p ^ s j) u i n (K + q)
    hc (hu i) (by omega) hlower hupper

/-- Every canonical seed depth is positive. -/
lemma primeClassScheduleDepth_pos
    (p : ℕ) {r : ℕ} (s u : Fin r → ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i) (i : Fin r) :
    1 ≤ primeClassScheduleDepth p s u i := by
  apply (StonehamSumsNormal.le_stonehamK_iff (fun j ↦ p ^ s j) u i
    (primeClassScheduleSeed p s u) 1
    (two_le_prime_pow p (s i) hp (hs i)) (hu i) le_rfl).2
  simpa only [pow_one, primeClassScheduleSeed] using
    (single_le_sum (fun j _ ↦ Nat.zero_le (u j * p ^ s j)) (mem_univ i))

lemma primeClassScheduleDepth_le_top
    (p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (i : Fin r) :
    s i * primeClassScheduleDepth p s u i ≤ primeClassScheduleTop p s u := by
  unfold primeClassScheduleTop
  exact single_le_sum
    (fun j _ ↦ Nat.zero_le (s j * primeClassScheduleDepth p s u j)) (mem_univ i)

lemma primeClassScheduleGap_add_depth
    (p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (i : Fin r) :
    primeClassScheduleGap p s u i + s i * primeClassScheduleDepth p s u i =
      primeClassScheduleTop p s u := by
  exact Nat.sub_add_cancel (primeClassScheduleDepth_le_top p s u i)

/-- The exact kick-depth formula throughout every canonical dilated cell. -/
theorem primeClassScheduleDepth_dilatedCell
    (p : ℕ) {r : ℕ} (s u : Fin r → ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (t n : ℕ)
    (hnlower : primeClassScheduleSeed p s u * p ^ (primeClassScalePeriod s * t) ≤ n)
    (hnupper : n < (primeClassScheduleSeed p s u + 1) *
      p ^ (primeClassScalePeriod s * t)) (i : Fin r) :
    StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n =
      primeClassScheduleDepth p s u i + primeClassScaleStep s i * t := by
  exact stonehamK_eq_on_primeClass_dilated_unitCell p s u i
    (primeClassScheduleSeed p s u) (primeClassScheduleDepth p s u i) t n hp hs hu
    (primeClassScheduleDepth_pos p s u hp hs hu i) rfl hnlower hnupper

/-- The gaps from the common depth are fixed on every dilated cell.  This is the scheduling
lemma needed by the dependent/non-normal half of Theorem T-B′. -/
theorem primeClassSchedule_fixedGap
    (p : ℕ) {r : ℕ} (s u : Fin r → ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (t n : ℕ)
    (hnlower : primeClassScheduleSeed p s u * p ^ (primeClassScalePeriod s * t) ≤ n)
    (hnupper : n < (primeClassScheduleSeed p s u + 1) *
      p ^ (primeClassScalePeriod s * t)) (i : Fin r) :
    primeClassScheduleGap p s u i +
        s i * StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n =
      primeClassScheduleTop p s u + primeClassScalePeriod s * t := by
  rw [primeClassScheduleDepth_dilatedCell p s u hp hs hu t n hnlower hnupper i]
  calc
    primeClassScheduleGap p s u i +
          s i * (primeClassScheduleDepth p s u i + primeClassScaleStep s i * t) =
        (primeClassScheduleGap p s u i +
          s i * primeClassScheduleDepth p s u i) +
          (s i * primeClassScaleStep s i) * t := by ring
    _ = primeClassScheduleTop p s u + primeClassScalePeriod s * t := by
      rw [primeClassScheduleGap_add_depth, primeClassScaleStep_factorization]

/-- The abstract fixed-gap arithmetic makes the rational Stoneham state an integer. -/
theorem stonehamState_eq_int_of_fixedGaps
    (p b T D n : ℕ) {r : ℕ} (s u δ : Fin r → ℕ) (a : Fin r → ℤ)
    (hp : p.Prime) (hpb : Nat.Coprime p b) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (hgap : ∀ i, δ i + s i *
      StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n = T)
    (hδD : ∀ i, δ i ≤ D) (hDT : D ≤ T)
    (hrel : ∀ E, (p : ℤ) ^ E ∣ ∑ i,
      a i * ((b : ℤ) ^ (p ^ E)) ^ primeClassComplementExponent u i) :
    ∃ z : ℤ,
      StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u
          (fun i ↦ primeClassStateCoefficient p (s i) (δ i) D (a i)) n = (z : ℚ) := by
  let K : Fin r → ℕ := fun i ↦
    StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n
  have hK : ∀ i, StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n = K i :=
    fun i ↦ rfl
  have hdepth : ∀ i, T - D ≤ s i * K i := by
    intro i
    have hi := hgap i
    have hiD := hδD i
    dsimp only [K]
    omega
  have hprecision : D + (T - D) ≤ T + 1 := by omega
  have hentered : ∀ i, ∀ k ∈ Icc 1 (K i), u i * p ^ (s i * k) ≤ n := by
    intro i k hk
    have hk' := (StonehamSumsNormal.le_stonehamK_iff (fun j ↦ p ^ s j) u i n k
      (two_le_prime_pow p (s i) hp (hs i)) (hu i) (mem_Icc.mp hk).1).1
      ((mem_Icc.mp hk).2.trans_eq (hK i).symm)
    simpa only [pow_mul] using hk'
  have hdiv := prime_pow_add_dvd_primeClassClearedStateNumerator
    p b T n D (T - D) s u K δ a hp hpb hK hgap hδD hdepth hprecision hentered
      (hrel (T - D))
  have hDE : D + (T - D) = T := by omega
  rw [hDE] at hdiv
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z, ?_⟩
  rw [stonehamState_eq_primeClassClearedStateNumerator_div b p T n s u
    (fun i ↦ primeClassStateCoefficient p (s i) (δ i) D (a i)) hp
    (fun i ↦ by have := hgap i; omega), hz]
  push_cast
  field_simp [hp.ne_zero]

/-- A complementary cyclotomic relation makes one fixed nonzero-coefficient state integral on
all canonical dilated cells.  The coefficient vector and gaps do not depend on `t` or `n`. -/
theorem primeClassSchedule_state_eq_int
    (p b : ℕ) {r : ℕ} (s u : Fin r → ℕ) (a : Fin r → ℤ)
    (hp : p.Prime) (hpb : Nat.Coprime p b) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (hrel : ∀ E, (p : ℤ) ^ E ∣ ∑ i,
      a i * ((b : ℤ) ^ (p ^ E)) ^ primeClassComplementExponent u i)
    (t n : ℕ)
    (hnlower : primeClassScheduleSeed p s u * p ^ (primeClassScalePeriod s * t) ≤ n)
    (hnupper : n < (primeClassScheduleSeed p s u + 1) *
      p ^ (primeClassScalePeriod s * t)) :
    ∃ z : ℤ,
      StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u
          (fun i ↦ primeClassStateCoefficient p (s i)
            (primeClassScheduleGap p s u i) (primeClassScheduleTop p s u) (a i)) n =
        (z : ℚ) := by
  apply stonehamState_eq_int_of_fixedGaps p b
    (primeClassScheduleTop p s u + primeClassScalePeriod s * t)
    (primeClassScheduleTop p s u) n s u (primeClassScheduleGap p s u) a hp hpb hs hu
  · exact primeClassSchedule_fixedGap p s u hp hs hu t n hnlower hnupper
  · intro i
    unfold primeClassScheduleGap
    exact Nat.sub_le _ _
  · omega
  · exact hrel

end NormalNumbers.StonehamPrimeClass
