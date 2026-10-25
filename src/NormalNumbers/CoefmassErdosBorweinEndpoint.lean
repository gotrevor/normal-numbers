/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassErdosBorweinPositive

/-!
# Random Erdős–Borwein subseries: the growing-moment criterion

Statements copied VERBATIM from the private KB packet `NNErdosBorweinRandom.lean` at 2a0cfb6c
(namespace relocated).  Paper argument: `nn-erdos-borwein-random-2026-10-12.md`, section "The
endpoint resolved", Step 1.  LOCAL-ONLY branch.

Step 1 only: if the selection-variance mass over the divisors of `n + a₀` above
`P₀(N) = exp((log log N)²)` diverges in density, then a.s. `E_b` is normal in every base.  The
endpoint input (Step 2, Erdős–Kac walk maximum) is NOT in this module.
-/

namespace NormalNumbers.ErdosBorweinEndpoint

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive
open NormalNumbers.RandomLambertMoment

/-- Selection-variance mass over the divisors of `n` above `P`: `Σ_{m ∣ n, m > P} v_m`. -/
noncomputable def divisorVarianceMass (v : ℕ → ℝ) (P n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => P < m), v m

/-- The collision cutoff `P₀(N) = ⌊exp((log log N)²)⌋`. -/
noncomputable def collisionCutoff (N : ℕ) : ℕ :=
  ⌊Real.exp (Real.log (Real.log N) ^ 2)⌋₊

/-- No large anchored divisor of one tuple coordinate divides any of the last `K` shifts of a
different coordinate.  This is the deterministic complement of the collision event. -/
def TupleCollisionFree (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ) : Prop :=
  ∀ (i j : Fin (2 * k)) (r p : ℕ), i ≠ j → r ∈ Finset.Icc 1 K → P₀ < p →
    p ∣ n i + a₀ → ¬ p ∣ n j + r

/-- A divisibility condition on one coordinate of `Fin N` occupies at most one residue class
per complete block of length `p`, plus one incomplete block. -/
theorem card_fin_dvd_add_le (N p a : ℕ) (hp : 0 < p) :
    ((Finset.univ : Finset (Fin N)).filter (fun x => p ∣ x.val + a)).card ≤ N / p + 1 := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (t := Finset.range (N / p + 1))
    (fun x : Fin N => x.val / p) ?_ ?_) ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx
    simpa only [Finset.mem_coe, Finset.mem_range] using
      Nat.lt_succ_of_le (Nat.div_le_div_right x.isLt.le)
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx hy
    change x.val / p = y.val / p at hxy
    apply Fin.ext
    rcases le_total y.val x.val with hyx | hxyv
    · have hdvd : p ∣ x.val - y.val := by
        have := Nat.dvd_sub hx hy
        simpa only [Nat.add_sub_add_right] using this
      have hlt : x.val - y.val < p := by
        have hxmod := Nat.mod_lt x.val hp
        have hymod := Nat.mod_lt y.val hp
        have hxsplit := Nat.div_add_mod x.val p
        have hysplit := Nat.div_add_mod y.val p
        rw [hxy] at hxsplit
        omega
      rcases Nat.eq_zero_or_pos (x.val - y.val) with hzero | hpos
      · omega
      · exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
    · have hdvd : p ∣ y.val - x.val := by
        have := Nat.dvd_sub hy hx
        simpa only [Nat.add_sub_add_right] using this
      have hlt : y.val - x.val < p := by
        have hxmod := Nat.mod_lt x.val hp
        have hymod := Nat.mod_lt y.val hp
        have hxsplit := Nat.div_add_mod x.val p
        have hysplit := Nat.div_add_mod y.val p
        rw [hxy] at hxsplit
        omega
      rcases Nat.eq_zero_or_pos (y.val - x.val) with hzero | hpos
      · omega
      · exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  · simp

/-- Tuples realizing one fixed collision between two distinct coordinates. -/
def tupleCollisionFiber (a r p N k : ℕ) (i j : Fin (2 * k)) :
    Finset (Fin (2 * k) → Fin N) :=
  Finset.univ.filter fun n => p ∣ (n i).val + a ∧ p ∣ (n j).val + r

/-- A fixed collision fiber has the product density expected from its two independent
coordinates.  The remaining `2k - 2` coordinates are unrestricted. -/
theorem card_tupleCollisionFiber_le {a r p N k : ℕ} {i j : Fin (2 * k)}
    (hij : i ≠ j) (hp : 0 < p) :
    (tupleCollisionFiber a r p N k i j).card ≤
      (N / p + 1) ^ 2 * N ^ (2 * k - 2) := by
  classical
  let A : Finset (Fin N) := Finset.univ.filter fun x => p ∣ x.val + a
  let B : Finset (Fin N) := Finset.univ.filter fun x => p ∣ x.val + r
  let C : Fin (2 * k) → Finset (Fin N) := fun t =>
    if t = i then A else if t = j then B else Finset.univ
  have hfiber : tupleCollisionFiber a r p N k i j = Fintype.piFinset C := by
    ext n
    simp only [tupleCollisionFiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨hni, hnj⟩ t
      by_cases hti : t = i
      · subst t
        simp only [C, if_pos, A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hni
      · by_cases htj : t = j
        · subst t
          simp only [C, if_neg hij.symm, if_pos, B, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact hnj
        · simp [C, hti, htj]
    · intro hn
      constructor
      · have := hn i
        simpa only [C, if_pos, A, Finset.mem_filter, Finset.mem_univ, true_and] using this
      · have := hn j
        simpa only [C, if_neg hij.symm, if_pos, B, Finset.mem_filter, Finset.mem_univ,
          true_and] using this
  have hA : A.card ≤ N / p + 1 := card_fin_dvd_add_le N p a hp
  have hB : B.card ≤ N / p + 1 := card_fin_dvd_add_le N p r hp
  have hjmem : j ∈ (Finset.univ : Finset (Fin (2 * k))).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hrest :
      (∏ t ∈ (Finset.univ : Finset (Fin (2 * k))).erase i |>.erase j, (C t).card) =
        N ^ (2 * k - 2) := by
    calc
      (∏ t ∈ (Finset.univ : Finset (Fin (2 * k))).erase i |>.erase j, (C t).card) =
          ∏ _t ∈ (Finset.univ : Finset (Fin (2 * k))).erase i |>.erase j, N := by
        apply Finset.prod_congr rfl
        intro t ht
        have htj : t ≠ j := (Finset.mem_erase.mp ht).1
        have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_of_mem_erase ht)).1
        simp [C, hti, htj]
      _ = N ^ ((Finset.univ : Finset (Fin (2 * k))).erase i |>.erase j).card :=
        Finset.prod_const N
      _ = N ^ (2 * k - 2) := by
        congr 1
        rw [Finset.card_erase_of_mem hjmem,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
        omega
  have hprod : (∏ t, (C t).card) = A.card * B.card * N ^ (2 * k - 2) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin (2 * k)))
      (fun t => (C t).card) (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase ((Finset.univ : Finset (Fin (2 * k))).erase i)
      (fun t => (C t).card) hjmem]
    rw [hrest]
    simp [C, hij.symm, mul_assoc]
  rw [hfiber, Fintype.card_piFinset, hprod]
  calc
    A.card * B.card * N ^ (2 * k - 2) ≤
        (N / p + 1) * (N / p + 1) * N ^ (2 * k - 2) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul hA hB) le_rfl
    _ = (N / p + 1) ^ 2 * N ^ (2 * k - 2) := by ring

/-- The finite union of all large-divisor collisions relevant at tuple length `N`. -/
def tupleCollisionSet (a K P₀ N k : ℕ) : Finset (Fin (2 * k) → Fin N) :=
  (Finset.univ : Finset (Fin (2 * k))).biUnion fun i =>
    (Finset.univ.erase i).biUnion fun j =>
      (Finset.Icc 1 K).biUnion fun r =>
        (Finset.Ioc P₀ (N + K)).biUnion fun p => tupleCollisionFiber a r p N k i j

/-- Membership in the finite collision union is exactly failure of collision freedom.  The upper
cutoff `N + K` loses nothing because a collision modulus divides the positive number `n_j + r`. -/
theorem mem_tupleCollisionSet_iff_not_collisionFree {a K P₀ N k : ℕ}
    {n : Fin (2 * k) → Fin N} :
    n ∈ tupleCollisionSet a K P₀ N k ↔
      ¬ TupleCollisionFree a K P₀ k (fun t => (n t).val) := by
  classical
  constructor
  · intro hn hfree
    rcases Finset.mem_biUnion.mp hn with ⟨i, hi, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨j, hj, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨r, hr, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨p, hp, hn⟩
    have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    rcases Finset.mem_filter.mp hn with ⟨_, hpi, hpj⟩
    exact (hfree i j r p hij hr (Finset.mem_Ioc.mp hp).1 hpi) hpj
  · intro hfree
    rw [TupleCollisionFree] at hfree
    push Not at hfree
    rcases hfree with ⟨i, j, r, p, hij, hr, hPp, hpi, hpj⟩
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
    have hp_le : p ≤ N + K := by
      have hp_njr : p ≤ (n j).val + r := Nat.le_of_dvd (by omega) hpj
      omega
    rw [tupleCollisionSet]
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_Icc.mpr ⟨hr1, hrK⟩, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_Ioc.mpr ⟨hPp, hp_le⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ n, hpi, hpj⟩

/-- Union-bound form of the collision count, before collapsing the repeated constant sums. -/
theorem card_tupleCollisionSet_le_sum (a K P₀ N k : ℕ) :
    (tupleCollisionSet a K P₀ N k).card ≤
      ∑ i ∈ (Finset.univ : Finset (Fin (2 * k))),
        ∑ j ∈ Finset.univ.erase i, ∑ r ∈ Finset.Icc 1 K,
          ∑ p ∈ Finset.Ioc P₀ (N + K), (N / p + 1) ^ 2 * N ^ (2 * k - 2) := by
  classical
  unfold tupleCollisionSet
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro i hi
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro r hr
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro p hp
  exact card_tupleCollisionFiber_le (Finset.ne_of_mem_erase hj).symm
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hp).1)

/-- The collision union has the paper's combinatorial prefactor: ordered distinct coordinate
pairs, one of `K` shifts, and the sum of the fixed-modulus fiber bounds. -/
theorem card_tupleCollisionSet_le (a K P₀ N k : ℕ) :
    (tupleCollisionSet a K P₀ N k).card ≤
      (2 * k) * (2 * k - 1) * K *
        ∑ p ∈ Finset.Ioc P₀ (N + K), (N / p + 1) ^ 2 * N ^ (2 * k - 2) := by
  refine (card_tupleCollisionSet_le_sum a K P₀ N k).trans_eq ?_
  classical
  have hcardK : (Finset.Icc 1 K).card = K := by simp [Nat.card_Icc]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem,
    Finset.mem_univ, Finset.card_univ, Fintype.card_fin, hcardK]
  norm_cast
  ac_rfl

/-- The elementary reciprocal-square tail needed to normalize the collision union. -/
theorem sum_inv_sq_Ioc_le_cutoff (P M : ℕ) (hP : 1 ≤ P) :
    ∑ p ∈ Finset.Ioc P M, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / P := by
  by_cases hPM : P ≤ M
  · have htel : ∑ p ∈ Finset.Ioc P M, (1 : ℝ) / (p : ℝ) ^ 2 ≤
        1 / (P : ℝ) - 1 / (M : ℝ) := by
      induction M, hPM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM]
        have hMR : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hP hM
        have hM1R : (0 : ℝ) < (M : ℝ) + 1 := by positivity
        have hstep : (1 : ℝ) / ((M : ℝ) + 1) ^ 2 ≤
            1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
          rw [div_sub_div _ _ (ne_of_gt hMR) (ne_of_gt hM1R)]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          ring_nf
          nlinarith
        have hcast : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith [ih]
    have hMnonneg : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  · have hempty : Finset.Ioc P M = ∅ := by
      exact Finset.Ioc_eq_empty (by omega)
    simp [hempty]

/-- On an interval of length at most `2N`, the squared residue-class density has the paper's
uniform elementary bound. -/
theorem sum_divisor_collision_density_le (P N K : ℕ)
    (hP : 1 ≤ P) (hN : 1 ≤ N) (hK : K ≤ N) :
    ∑ p ∈ Finset.Ioc P (N + K),
        ((1 : ℝ) / (p : ℝ) + 1 / (N : ℝ)) ^ 2 ≤
      3 / (P : ℝ) + 4 / (N : ℝ) := by
  let S := Finset.Ioc P (N + K)
  have hpoint (p : ℕ) : ((1 : ℝ) / p + 1 / N) ^ 2 ≤
      2 * ((1 : ℝ) / p) ^ 2 + 2 * ((1 : ℝ) / N) ^ 2 := by
    nlinarith [sq_nonneg ((1 : ℝ) / p - 1 / N)]
  have hsplit : ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 ≤
      2 * (∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2) +
        (S.card : ℝ) * (2 * ((1 : ℝ) / N) ^ 2) := by
    calc
      ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 ≤
          ∑ p ∈ S, (2 * ((1 : ℝ) / p) ^ 2 + 2 * ((1 : ℝ) / N) ^ 2) := by
            exact Finset.sum_le_sum fun p _ => hpoint p
      _ = 2 * (∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2) +
          (S.card : ℝ) * (2 * ((1 : ℝ) / N) ^ 2) := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              Finset.mul_sum]
            ring
  have htail : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / P := by
    simpa only [S] using sum_inv_sq_Ioc_le_cutoff P (N + K) hP
  have hcardNat : S.card ≤ 2 * N := by
    dsimp only [S]
    rw [Nat.card_Ioc]
    omega
  have hcard : (S.card : ℝ) ≤ 2 * N := by exact_mod_cast hcardNat
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ∑ p ∈ Finset.Ioc P (N + K), ((1 : ℝ) / p + 1 / N) ^ 2 =
        ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 := by rfl
    _ ≤ 2 * (∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2) +
        (S.card : ℝ) * (2 * ((1 : ℝ) / N) ^ 2) := hsplit
    _ ≤ 2 * (1 / (P : ℝ)) +
        (2 * (N : ℝ)) * (2 * ((1 : ℝ) / N) ^ 2) := by
      gcongr
    _ ≤ 3 / (P : ℝ) + 4 / (N : ℝ) := by
      have hPreal : (0 : ℝ) < P := by exact_mod_cast hP
      have htwo : 2 * (1 / (P : ℝ)) ≤ 3 / (P : ℝ) := by
        simp only [div_eq_mul_inv, one_mul]
        nlinarith [inv_pos.mpr hPreal]
      have hfour : (2 * (N : ℝ)) * (2 * ((1 : ℝ) / N) ^ 2) =
          4 / (N : ℝ) := by
        field_simp [ne_of_gt hNreal]
        norm_num
      rw [hfour]
      exact add_le_add htwo le_rfl

/-- After casting, one fixed-modulus fiber bound is at most the ambient tuple count times the
corresponding squared residue-class density. -/
theorem cast_collision_fiber_bound_le (N p k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (((N / p + 1) ^ 2 * N ^ (2 * k - 2) : ℕ) : ℝ) ≤
      (N : ℝ) ^ (2 * k) * ((1 : ℝ) / p + 1 / N) ^ 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hquot : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
  have hbase : ((N / p + 1 : ℕ) : ℝ) ≤
      (N : ℝ) * ((1 : ℝ) / p + 1 / N) := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      ((N / p : ℕ) : ℝ) + 1 ≤ (N : ℝ) / (p : ℝ) + 1 :=
        by linarith
      _ = (N : ℝ) * ((1 : ℝ) / p + 1 / N) := by
        by_cases hp : p = 0
        · subst p
          simp [ne_of_gt hNreal]
        · field_simp [hp, ne_of_gt hNreal]
  have hleft0 : (0 : ℝ) ≤ ((N / p + 1 : ℕ) : ℝ) := by positivity
  have hright0 : (0 : ℝ) ≤ (N : ℝ) * ((1 : ℝ) / p + 1 / N) := by
    positivity
  have hsquare : (((N / p + 1 : ℕ) : ℝ)) ^ 2 ≤
      ((N : ℝ) * ((1 : ℝ) / p + 1 / N)) ^ 2 := by
    nlinarith
  have hsquare' : (((N / p : ℕ) : ℝ) + 1) ^ 2 ≤
      ((N : ℝ) * ((1 : ℝ) / p + 1 / N)) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsquare
  push_cast
  calc
    (((N / p : ℕ) : ℝ) + 1) ^ 2 * (N : ℝ) ^ (2 * k - 2) ≤
        ((N : ℝ) * ((1 : ℝ) / p + 1 / N)) ^ 2 *
          (N : ℝ) ^ (2 * k - 2) := by
      exact mul_le_mul_of_nonneg_right hsquare' (by positivity)
    _ = ((N : ℝ) ^ 2 * (N : ℝ) ^ (2 * k - 2)) *
        ((1 : ℝ) / p + 1 / N) ^ 2 := by ring
    _ = (N : ℝ) ^ (2 * k) * ((1 : ℝ) / p + 1 / N) ^ 2 := by
      rw [← pow_add]
      congr 2
      omega

/-- The bad collision union has the normalized density predicted by the union bound. -/
theorem collisionDensity_le (a K P N k : ℕ)
    (hP : 1 ≤ P) (hN : 1 ≤ N) (hK : K ≤ N) (hk : 1 ≤ k) :
    ((tupleCollisionSet a K P N k).card : ℝ) / (N : ℝ) ^ (2 * k) ≤
      (((2 * k) * (2 * k - 1) * K : ℕ) : ℝ) *
        (3 / (P : ℝ) + 4 / (N : ℝ)) := by
  let S := Finset.Ioc P (N + K)
  let C : ℕ := (2 * k) * (2 * k - 1) * K
  have hcardNat := card_tupleCollisionSet_le a K P N k
  have hcard : ((tupleCollisionSet a K P N k).card : ℝ) ≤
      (C : ℝ) * ∑ p ∈ S,
        (((N / p + 1) ^ 2 * N ^ (2 * k - 2) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hsum : (∑ p ∈ S,
        (((N / p + 1) ^ 2 * N ^ (2 * k - 2) : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (2 * k) *
        ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 := by
    calc
      (∑ p ∈ S, (((N / p + 1) ^ 2 * N ^ (2 * k - 2) : ℕ) : ℝ)) ≤
          ∑ p ∈ S, (N : ℝ) ^ (2 * k) *
            ((1 : ℝ) / p + 1 / N) ^ 2 := by
        exact Finset.sum_le_sum fun p _ => cast_collision_fiber_bound_le N p k hN hk
      _ = (N : ℝ) ^ (2 * k) *
          ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 := by
        rw [Finset.mul_sum]
  have hcount : ((tupleCollisionSet a K P N k).card : ℝ) ≤
      (C : ℝ) * ((N : ℝ) ^ (2 * k) *
        ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2) :=
    hcard.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hNpow : 0 < (N : ℝ) ^ (2 * k) := by positivity
  have htail : ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 ≤
      3 / (P : ℝ) + 4 / (N : ℝ) := by
    simpa only [S] using sum_divisor_collision_density_le P N K hP hN hK
  calc
    ((tupleCollisionSet a K P N k).card : ℝ) / (N : ℝ) ^ (2 * k) ≤
        ((C : ℝ) * ((N : ℝ) ^ (2 * k) *
          ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2)) /
            (N : ℝ) ^ (2 * k) := div_le_div_of_nonneg_right hcount hNpow.le
    _ = (C : ℝ) * ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 := by
      field_simp [ne_of_gt hNpow]
    _ ≤ (C : ℝ) * (3 / (P : ℝ) + 4 / (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (((2 * k) * (2 * k - 1) * K : ℕ) : ℝ) *
        (3 / (P : ℝ) + 4 / (N : ℝ)) := by rfl

/-- A convenient weakening of `collisionDensity_le` with the paper's `4k²K` prefactor. -/
theorem collisionDensity_le_four (a K P N k : ℕ)
    (hP : 1 ≤ P) (hN : 1 ≤ N) (hK : K ≤ N) (hk : 1 ≤ k) :
    ((tupleCollisionSet a K P N k).card : ℝ) / (N : ℝ) ^ (2 * k) ≤
      4 * (k : ℝ) ^ 2 * K * (3 / (P : ℝ) + 4 / (N : ℝ)) := by
  have hmain := collisionDensity_le a K P N k hP hN hK hk
  have hcoeffNat : (2 * k) * (2 * k - 1) * K ≤ 4 * k ^ 2 * K := by
    calc
      (2 * k) * (2 * k - 1) * K ≤ (2 * k) * (2 * k) * K := by
        gcongr
        omega
      _ = 4 * k ^ 2 * K := by ring
  have hcoeff : ((((2 * k) * (2 * k - 1) * K : ℕ) : ℝ)) ≤
      4 * (k : ℝ) ^ 2 * K := by exact_mod_cast hcoeffNat
  have htail0 : 0 ≤ 3 / (P : ℝ) + 4 / (N : ℝ) := by positivity
  exact hmain.trans (mul_le_mul_of_nonneg_right hcoeff htail0)

/-- On a collision-free tuple, every large divisor anchored at a coordinate is a good modulus at
that coordinate. -/
theorem mem_tupleGoodModuli_of_collisionFree {a₀ K P₀ k p : ℕ}
    {n : Fin (2 * k) → ℕ} {i : Fin (2 * k)}
    (ha₀ : 1 ≤ a₀) (hKP : K ≤ P₀) (hfree : TupleCollisionFree a₀ K P₀ k n)
    (hpdiv : p ∣ n i + a₀) (hPp : P₀ < p) :
    p ∈ tupleGoodModuli a₀ K P₀ k n i := by
  rw [mem_tupleGoodModuli ha₀]
  refine ⟨hpdiv, hPp, ?_⟩
  intro j hji
  by_contra hjsep
  have hbad : ¬ ∀ j, j ≠ i → n j % p < p - K := by
    intro hall
    exact hjsep (hall j hji)
  obtain ⟨j', hj'i, r, hr, hpgcd⟩ :=
    bad_modulus_dvd_shifted_gcd (lt_of_le_of_lt hKP hPp) hpdiv hbad
  have hpjr : p ∣ n j' + r := hpgcd.trans (Nat.gcd_dvd_right _ _)
  exact (hfree i j' r p hj'i.symm hr hPp hpdiv) hpjr

/-- Collision freedom identifies the good set at an anchor with all of its divisors above the
cutoff. -/
theorem tupleGoodModuli_eq_large_divisors_of_collisionFree
    {a₀ K P₀ k : ℕ} {n : Fin (2 * k) → ℕ} (i : Fin (2 * k))
    (ha₀ : 1 ≤ a₀) (hKP : K ≤ P₀) (hfree : TupleCollisionFree a₀ K P₀ k n) :
    tupleGoodModuli a₀ K P₀ k n i =
      (n i + a₀).divisors.filter (fun p => P₀ < p) := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpdivs, hPp, _⟩
    exact Finset.mem_filter.mpr ⟨hpdivs, hPp⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpdivs, hPp⟩
    exact mem_tupleGoodModuli_of_collisionFree ha₀ hKP hfree
      (Nat.dvd_of_mem_divisors hpdivs) hPp

/-- Thus the good-modulus variance sum is exactly the frozen divisor-variance mass on a
collision-free tuple. -/
theorem sum_tupleGoodModuli_eq_divisorVarianceMass_of_collisionFree
    (v : ℕ → ℝ) {a₀ K P₀ k : ℕ} {n : Fin (2 * k) → ℕ} (i : Fin (2 * k))
    (ha₀ : 1 ≤ a₀) (hKP : K ≤ P₀) (hfree : TupleCollisionFree a₀ K P₀ k n) :
    (∑ p ∈ tupleGoodModuli a₀ K P₀ k n i, v p) =
      divisorVarianceMass v P₀ (n i + a₀) := by
  rw [tupleGoodModuli_eq_large_divisors_of_collisionFree i ha₀ hKP hfree]
  rfl

/-- Good-modulus sets at distinct anchors are disjoint once the anchor shift lies within the
protected residue tail. -/
theorem disjoint_tupleGoodModuli {a₀ K P₀ k : ℕ} {n : Fin (2 * k) → ℕ}
    (i j : Fin (2 * k)) (hij : i ≠ j) (ha₀ : 1 ≤ a₀) (ha₀K : a₀ ≤ K)
    (hKP : 2 * K ≤ P₀) :
    Disjoint (tupleGoodModuli a₀ K P₀ k n i) (tupleGoodModuli a₀ K P₀ k n j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rcases (mem_tupleGoodModuli ha₀).mp hpi with ⟨hpdivi, hPp, hsepi⟩
  rcases (mem_tupleGoodModuli ha₀).mp hpj with ⟨hpdivj, _, _⟩
  have ha₀p : a₀ < p := by omega
  have hjres : n j % p = p - a₀ := anchor_residue_of_dvd ha₀ ha₀p hpdivj
  have hsep := hsepi j hij.symm
  rw [hjres] at hsep
  omega

/-- The union of the good-modulus sets over every tuple coordinate. -/
def tupleAllGoodModuli (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin (2 * k))).biUnion fun i => tupleGoodModuli a₀ K P₀ k n i

/-- Because distinct anchors have disjoint good sets, mass over all good moduli factors exactly
as the sum of the anchor masses. -/
theorem sum_tupleAllGoodModuli (v : ℕ → ℝ) {a₀ K P₀ k : ℕ}
    {n : Fin (2 * k) → ℕ} (ha₀ : 1 ≤ a₀) (ha₀K : a₀ ≤ K) (hKP : 2 * K ≤ P₀) :
    (∑ p ∈ tupleAllGoodModuli a₀ K P₀ k n, v p) =
      ∑ i : Fin (2 * k), ∑ p ∈ tupleGoodModuli a₀ K P₀ k n i, v p := by
  unfold tupleAllGoodModuli
  rw [Finset.sum_biUnion]
  intro i hi j hj hij
  exact disjoint_tupleGoodModuli i j hij ha₀ ha₀K hKP

/-- The good moduli at one anchor contract by the exponential of their actual retained
Bernoulli-variance mass.  This is the mass-valued form of the power-bound lemma used in the
positive-exponent argument. -/
theorem tupleGoodModuli_bernMod_product_le_mass (delta : ℕ → ℝ)
    (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (b e m K P₀ k : ℕ) (h : ℤ) (n : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀) :
    ∏ r ∈ (tupleGoodModuli (e + 1) K P₀ k n i).image (fun p => p - 1),
        bernMod (delta (r + 1)) (tuplePhase b h k (r + 1) n) ≤
      Real.exp (-spectralConst b *
        ∑ p ∈ tupleGoodModuli (e + 1) K P₀ k n i, delta p * (1 - delta p)) := by
  classical
  let G := tupleGoodModuli (e + 1) K P₀ k n i
  have hp_two (p : ℕ) (hp : p ∈ G) : 2 ≤ p := by
    have hcut := ((mem_tupleGoodModuli (a₀ := e + 1) (K := K) (P₀ := P₀)
      (k := k) (p := p) (n := n) (i := i) (by omega)).mp hp).2.1
    omega
  have hinj : Set.InjOn (fun p : ℕ => p - 1) ↑G := by
    intro p hp q hq hpq
    change p ∈ G at hp
    change q ∈ G at hq
    have hp1 : 1 ≤ p := le_trans (by omega) (hp_two p hp)
    have hq1 : 1 ≤ q := le_trans (by omega) (hp_two q hq)
    change p - 1 = q - 1 at hpq
    omega
  have hreindex :
      (∏ r ∈ G.image (fun p => p - 1),
          bernMod (delta (r + 1)) (tuplePhase b h k (r + 1) n)) =
        ∏ p ∈ G, bernMod (delta p) (tuplePhase b h k p n) := by
    rw [Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.sub_add_cancel (by have := hp_two p hp; omega : 1 ≤ p)]
  rw [show tupleGoodModuli (e + 1) K P₀ k n i = G by rfl, hreindex]
  apply prod_bernMod_le_exp_neg_spectral
  · intro p hp
    exact hdelta p
  · intro p hp
    exact tupleGoodModuli_cos_le b e m K P₀ k p h n i hb hk hfac hm hK hlarge hKP hp

/-- A fixed initial product contains every good modulus at a chosen tuple anchor, and therefore
inherits contraction by the anchor's actual retained Bernoulli-variance mass. -/
theorem global_bernMod_product_le_good_anchor_mass (delta : ℕ → ℝ)
    (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (b e m K P₀ k N : ℕ) (h : ℤ) (n : Fin (2 * k) → Fin N) (i : Fin (2 * k))
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀) :
    ∏ r ∈ Finset.range (N + e + 1),
        bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun j => (n j).val)) ≤
      Real.exp (-spectralConst b *
        ∑ p ∈ tupleGoodModuli (e + 1) K P₀ k (fun j => (n j).val) i,
          delta p * (1 - delta p)) := by
  let G := (tupleGoodModuli (e + 1) K P₀ k (fun j => (n j).val) i).image
    (fun p => p - 1)
  have hsubset : G ⊆ Finset.range (N + e + 1) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    have hpdiv := ((mem_tupleGoodModuli (a₀ := e + 1) (K := K) (P₀ := P₀)
      (k := k) (p := p) (n := fun j => (n j).val) (i := i) (by omega)).mp hp).1
    have hple : p ≤ (n i).val + (e + 1) := Nat.le_of_dvd (by omega) hpdiv
    rw [Finset.mem_range]
    omega
  have hglobal :
      (∏ r ∈ Finset.range (N + e + 1),
          bernMod (delta (r + 1))
            (tuplePhase b h k (r + 1) (fun j => (n j).val))) ≤
        ∏ r ∈ G, bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun j => (n j).val)) := by
    apply Finset.prod_le_prod_of_subset_of_le_one hsubset
    · intro r hr
      exact bernMod_nonneg _ _
    · intro r hr hrG
      exact bernMod_le_one (hdelta (r + 1)).1 (hdelta (r + 1)).2 _
  refine hglobal.trans ?_
  simpa only [G] using tupleGoodModuli_bernMod_product_le_mass delta hdelta
    b e m K P₀ k h (fun j => (n j).val) i hb hk hfac hm hK hlarge hKP

/-- The initial characteristic product contracts by the sum of retained variance masses over all
tuple anchors.  Disjointness of the good-modulus sets is what preserves the full sum. -/
theorem global_bernMod_product_le_all_good_mass (delta : ℕ → ℝ)
    (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (b e m K P₀ k N : ℕ) (h : ℤ) (n : Fin (2 * k) → Fin N)
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀) :
    ∏ r ∈ Finset.range (N + e + 1),
        bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun j => (n j).val)) ≤
      Real.exp (-spectralConst b *
        ∑ i : Fin (2 * k),
          ∑ p ∈ tupleGoodModuli (e + 1) K P₀ k (fun j => (n j).val) i,
            delta p * (1 - delta p)) := by
  classical
  let A := tupleAllGoodModuli (e + 1) K P₀ k (fun j => (n j).val)
  let G := A.image (fun p => p - 1)
  have hp_two (p : ℕ) (hp : p ∈ A) : 2 ≤ p := by
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
    have hcut := ((mem_tupleGoodModuli (a₀ := e + 1) (K := K) (P₀ := P₀)
      (k := k) (p := p) (n := fun j => (n j).val) (i := i) (by omega)).mp hpi).2.1
    omega
  have hsubset : G ⊆ Finset.range (N + e + 1) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
    have hpdiv := ((mem_tupleGoodModuli (a₀ := e + 1) (K := K) (P₀ := P₀)
      (k := k) (p := p) (n := fun j => (n j).val) (i := i) (by omega)).mp hpi).1
    have hple : p ≤ (n i).val + (e + 1) := Nat.le_of_dvd (by omega) hpdiv
    rw [Finset.mem_range]
    omega
  have hglobal :
      (∏ r ∈ Finset.range (N + e + 1),
          bernMod (delta (r + 1))
            (tuplePhase b h k (r + 1) (fun j => (n j).val))) ≤
        ∏ r ∈ G, bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun j => (n j).val)) := by
    apply Finset.prod_le_prod_of_subset_of_le_one hsubset
    · intro r hr
      exact bernMod_nonneg _ _
    · intro r hr hrG
      exact bernMod_le_one (hdelta (r + 1)).1 (hdelta (r + 1)).2 _
  have hinj : Set.InjOn (fun p : ℕ => p - 1) ↑A := by
    intro p hp q hq hpq
    have hp1 : 1 ≤ p := le_trans (by omega) (hp_two p hp)
    have hq1 : 1 ≤ q := le_trans (by omega) (hp_two q hq)
    change p - 1 = q - 1 at hpq
    omega
  have hreindex :
      (∏ r ∈ G, bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun j => (n j).val))) =
        ∏ p ∈ A, bernMod (delta p)
          (tuplePhase b h k p (fun j => (n j).val)) := by
    dsimp only [G]
    rw [Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.sub_add_cancel (by have := hp_two p hp; omega : 1 ≤ p)]
  have hall :
      (∏ p ∈ A, bernMod (delta p)
          (tuplePhase b h k p (fun j => (n j).val))) ≤
        Real.exp (-spectralConst b *
          ∑ p ∈ A, delta p * (1 - delta p)) := by
    apply prod_bernMod_le_exp_neg_spectral
    · intro p hp
      exact hdelta p
    · intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
      exact tupleGoodModuli_cos_le b e m K P₀ k p h (fun j => (n j).val) i
        hb hk hfac hm hK hlarge hKP hpi
  refine hglobal.trans (hreindex.le.trans (hall.trans_eq ?_))
  congr 2
  simpa only [A] using sum_tupleAllGoodModuli (fun p => delta p * (1 - delta p))
    (a₀ := e + 1) (K := K) (P₀ := P₀) (k := k)
    (n := fun j => (n j).val) (by omega) hK hKP

/-- On the no-collision event, the characteristic product contracts by the sum of the frozen
divisor-variance masses of all tuple coordinates. -/
theorem global_bernMod_product_le_divisorVarianceMass_of_collisionFree
    (delta : ℕ → ℝ) (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (b e m K P₀ k N : ℕ) (h : ℤ) (n : Fin (2 * k) → Fin N)
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀)
    (hfree : TupleCollisionFree (e + 1) K P₀ k (fun j => (n j).val)) :
    ∏ r ∈ Finset.range (N + e + 1),
        bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun j => (n j).val)) ≤
      Real.exp (-spectralConst b *
        ∑ i : Fin (2 * k), divisorVarianceMass (fun p => delta p * (1 - delta p))
          P₀ ((n i).val + (e + 1))) := by
  refine (global_bernMod_product_le_all_good_mass delta hdelta b e m K P₀ k N h n
    hb hk hfac hm hK hlarge hKP).trans_eq ?_
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_tupleGoodModuli_eq_divisorVarianceMass_of_collisionFree
    (fun p => delta p * (1 - delta p)) i (by omega) (by omega) hfree

/-- Split the tuple sum into collision tuples, which cost at most one, and collision-free tuples,
whose contraction factors into independent one-coordinate divisor-mass weights. -/
theorem tupleBernMod_sum_le_collision_add_pow
    (delta : ℕ → ℝ) (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (b e m K P k N : ℕ) (h : ℤ)
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P) :
    (∑ n : Fin (2 * k) → Fin N,
        ∏ r ∈ Finset.range (N + e + 1),
          bernMod (delta (r + 1))
            (tuplePhase b h k (r + 1) (fun j => (n j).val))) ≤
      ((tupleCollisionSet (e + 1) K P N k).card : ℝ) +
        (∑ x : Fin N, Real.exp (-spectralConst b *
          divisorVarianceMass (fun p => delta p * (1 - delta p))
            P (x.val + (e + 1)))) ^ (2 * k) := by
  classical
  let S := tupleCollisionSet (e + 1) K P N k
  let W : Fin N → ℝ := fun x =>
    divisorVarianceMass (fun p => delta p * (1 - delta p)) P (x.val + (e + 1))
  let g : Fin N → ℝ := fun x => Real.exp (-spectralConst b * W x)
  let f : (Fin (2 * k) → Fin N) → ℝ := fun n =>
    ∏ r ∈ Finset.range (N + e + 1),
      bernMod (delta (r + 1))
        (tuplePhase b h k (r + 1) (fun j => (n j).val))
  have hf_one (n : Fin (2 * k) → Fin N) : f n ≤ 1 := by
    dsimp only [f]
    apply Finset.prod_le_one
    · intro r hr
      exact bernMod_nonneg _ _
    · intro r hr
      exact bernMod_le_one (hdelta (r + 1)).1 (hdelta (r + 1)).2 _
  have hg_nonneg (x : Fin N) : 0 ≤ g x := (Real.exp_pos _).le
  have hout (n : Fin (2 * k) → Fin N) (hn : n ∉ S) :
      f n ≤ ∏ i, g (n i) := by
    have hfree : TupleCollisionFree (e + 1) K P k (fun j => (n j).val) := by
      by_contra hnot
      exact hn ((mem_tupleCollisionSet_iff_not_collisionFree (a := e + 1)
        (K := K) (P₀ := P) (N := N) (k := k) (n := n)).2 hnot)
    have hcontract :=
      global_bernMod_product_le_divisorVarianceMass_of_collisionFree delta hdelta
        b e m K P k N h n hb hk hfac hm hK hlarge hKP hfree
    calc
      f n ≤ Real.exp (-spectralConst b * ∑ i : Fin (2 * k), W (n i)) := by
        simpa only [f, W] using hcontract
      _ = ∏ i : Fin (2 * k), g (n i) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
  have hfilterS : (Finset.univ : Finset (Fin (2 * k) → Fin N)).filter
      (fun n => n ∈ S) = S := by
    ext n
    simp
  have hinside : (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∈ S,
      f n) ≤ (S.card : ℝ) := by
    rw [hfilterS]
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] using
      (Finset.sum_le_card_nsmul S f 1 (fun n _ => hf_one n))
  have houtside :
      (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S, f n) ≤
        ∑ n : Fin (2 * k) → Fin N, ∏ i, g (n i) := by
    calc
      (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S, f n) ≤
          ∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S,
            ∏ i, g (n i) := by
        exact Finset.sum_le_sum fun n hn => hout n (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n : Fin (2 * k) → Fin N, ∏ i, g (n i) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => Finset.prod_nonneg fun i _ => hg_nonneg (n i))
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin (2 * k) → Fin N))) (p := fun n => n ∈ S) f
  calc
    (∑ n : Fin (2 * k) → Fin N, f n) =
        (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∈ S, f n) +
          ∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S, f n :=
      hsplit.symm
    _ ≤ (S.card : ℝ) + ∑ n : Fin (2 * k) → Fin N, ∏ i, g (n i) :=
      add_le_add hinside houtside
    _ = (S.card : ℝ) + (∑ x : Fin N, g x) ^ (2 * k) := by
      rw [← Fintype.prod_sum, Fin.prod_const]
    _ = ((tupleCollisionSet (e + 1) K P N k).card : ℝ) +
        (∑ x : Fin N, Real.exp (-spectralConst b *
          divisorVarianceMass (fun p => delta p * (1 - delta p))
            P (x.val + (e + 1)))) ^ (2 * k) := by rfl

/-- Moment bound after normalizing the tuple split: a power of the one-coordinate divisor-mass
average plus the explicit collision density. -/
theorem ebMoment_le_divisorMassAvg_pow_add_collision
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (b e m K P k N : ℕ) (h : ℤ)
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hN : 1 ≤ N) (hP : 1 ≤ P) (hKN : K ≤ N)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P) :
    (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
      ((∑ x : Fin N, Real.exp (-spectralConst b *
        divisorVarianceMass (fun p => delta p * (1 - delta p))
          P (x.val + (e + 1)))) / (N : ℝ)) ^ (2 * k) +
        4 * (k : ℝ) ^ 2 * K * (3 / (P : ℝ) + 4 / (N : ℝ)) := by
  let f : (Fin (2 * k) → Fin N) → ℝ := fun n =>
    ∏ r ∈ Finset.range (N + e + 1),
      bernMod (delta (r + 1))
        (tuplePhase b h k (r + 1) (fun j => (n j).val))
  let A : ℝ := ∑ x : Fin N, Real.exp (-spectralConst b *
    divisorVarianceMass (fun p => delta p * (1 - delta p)) P (x.val + (e + 1)))
  have hmoment := ebMoment_le_tupleAvg b hb h μ delta X hX
    (Finset.range (N + e + 1)) k N hN 0 1 (Or.inl rfl)
  have hmoment' :
      (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
        (∑ n, f n) / (N : ℝ) ^ (2 * k) := by
    simpa only [f, zero_add, Int.cast_one, one_mul] using hmoment
  have hsum : (∑ n, f n) ≤
      ((tupleCollisionSet (e + 1) K P N k).card : ℝ) + A ^ (2 * k) := by
    simpa only [f, A] using tupleBernMod_sum_le_collision_add_pow delta hX.1
      b e m K P k N h hb hk hfac hm hK hlarge hKP
  have hNpow : 0 < (N : ℝ) ^ (2 * k) := by positivity
  have hcollision := collisionDensity_le_four (e + 1) K P N k hP hN hKN hk
  calc
    (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
        (∑ n, f n) / (N : ℝ) ^ (2 * k) := hmoment'
    _ ≤ (((tupleCollisionSet (e + 1) K P N k).card : ℝ) + A ^ (2 * k)) /
        (N : ℝ) ^ (2 * k) := div_le_div_of_nonneg_right hsum hNpow.le
    _ = ((tupleCollisionSet (e + 1) K P N k).card : ℝ) /
          (N : ℝ) ^ (2 * k) + (A / (N : ℝ)) ^ (2 * k) := by
      rw [add_div, div_pow]
    _ ≤ 4 * (k : ℝ) ^ 2 * K * (3 / (P : ℝ) + 4 / (N : ℝ)) +
        (A / (N : ℝ)) ^ (2 * k) := add_le_add hcollision le_rfl
    _ = (A / (N : ℝ)) ^ (2 * k) +
        4 * (k : ℝ) ^ 2 * K * (3 / (P : ℝ) + 4 / (N : ℝ)) := by ring
    _ = ((∑ x : Fin N, Real.exp (-spectralConst b *
        divisorVarianceMass (fun p => delta p * (1 - delta p))
          P (x.val + (e + 1)))) / (N : ℝ)) ^ (2 * k) +
        4 * (k : ℝ) ^ 2 * K * (3 / (P : ℝ) + 4 / (N : ℝ)) := by rfl

/-- Divisor-variance mass is nonnegative when its weights are nonnegative. -/
theorem divisorVarianceMass_nonneg (v : ℕ → ℝ) (hv : ∀ p, 0 ≤ v p) (P n : ℕ) :
    0 ≤ divisorVarianceMass v P n := by
  unfold divisorVarianceMass
  exact Finset.sum_nonneg fun p _ => hv p

/-- The `Fin N` average is bounded by the density of coordinates with mass at most `T`, plus the
uniform exponential cost above `T`.  The shift by one aligns `Fin N = {0,...,N-1}` with the frozen
`Icc 1 N` density hypothesis. -/
theorem divisorMassExpAvg_le_density_add
    (v : ℕ → ℝ) (hv : ∀ p, 0 ≤ v p) (c : ℝ) (hc : 0 < c)
    (u N : ℕ) (T : ℝ) (hN : 1 ≤ N) :
    (∑ x : Fin N, Real.exp (-c *
        divisorVarianceMass v (collisionCutoff N) (x.val + (u + 1)))) / (N : ℝ) ≤
      ((((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + u) ≤ T)).card : ℝ) / (N : ℝ)) +
        Real.exp (-c * T) := by
  classical
  let W : Fin N → ℝ := fun x =>
    divisorVarianceMass v (collisionCutoff N) (x.val + (u + 1))
  let low : Finset (Fin N) := Finset.univ.filter fun x => W x ≤ T
  let f : Fin N → ℝ := fun x => Real.exp (-c * W x)
  let E : ℝ := Real.exp (-c * T)
  have hf_one (x : Fin N) : f x ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hW0 : 0 ≤ W x := divisorVarianceMass_nonneg v hv _ _
    nlinarith
  have hout (x : Fin N) (hx : x ∉ low) : f x ≤ E := by
    have hxT : T < W x := by
      simpa only [low, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hx
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsum : (∑ x : Fin N, f x) ≤ (low.card : ℝ) + (N : ℝ) * E := by
    simpa only [Fintype.card_fin] using
      (sum_le_card_exceptional_add_uniform low f E (Real.exp_pos _).le
        (fun x _ => hf_one x) hout)
  have hlowcard : low.card =
      ((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + u) ≤ T)).card := by
    apply Finset.card_bij (fun x _ => x.val + 1)
    · intro x hx
      have hx' : W x ≤ T := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by have := x.isLt; omega⟩, ?_⟩
      change divisorVarianceMass v (collisionCutoff N) ((x.val + 1) + u) ≤ T
      change divisorVarianceMass v (collisionCutoff N) (x.val + (u + 1)) ≤ T at hx'
      rw [show (x.val + 1) + u = x.val + (u + 1) by omega]
      exact hx'
    · intro x hx y hy hxy
      apply Fin.ext
      omega
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnT⟩
      rcases Finset.mem_Icc.mp hnIcc with ⟨hn1, hnN⟩
      let x : Fin N := ⟨n - 1, by omega⟩
      refine ⟨x, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        change divisorVarianceMass v (collisionCutoff N) ((n - 1) + (u + 1)) ≤ T
        rw [show (n - 1) + (u + 1) = n + u by omega]
        exact hnT
      · dsimp only [x]
        omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (∑ x : Fin N, Real.exp (-c *
        divisorVarianceMass v (collisionCutoff N) (x.val + (u + 1)))) / (N : ℝ) =
        (∑ x : Fin N, f x) / (N : ℝ) := by rfl
    _ ≤ ((low.card : ℝ) + (N : ℝ) * E) / (N : ℝ) :=
      div_le_div_of_nonneg_right hsum hNreal.le
    _ = (low.card : ℝ) / (N : ℝ) + E := by
      rw [add_div]
      field_simp [ne_of_gt hNreal]
    _ = ((((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + u) ≤ T)).card : ℝ) / (N : ℝ)) +
        Real.exp (-c * T) := by rw [hlowcard]

/-- Divergence in density of the divisor mass forces the one-coordinate exponential mass average
to vanish. -/
theorem tendsto_divisorMassExpAvg
    (v : ℕ → ℝ) (hv : ∀ p, 0 ≤ v p) (c : ℝ) (hc : 0 < c) (u : ℕ)
    (hdiv : ∀ T : ℝ, Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + u) ≤ T)).card : ℝ) / (N : ℝ)))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ x : Fin N, Real.exp (-c *
        divisorVarianceMass v (collisionCutoff N) (x.val + (u + 1)))) / (N : ℝ))
      atTop (𝓝 0) := by
  have hexp : Tendsto (fun T : ℕ => Real.exp (-c * (T : ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hexp (ε / 2) (by positivity)
  have hET : Real.exp (-c * (T : ℝ)) < ε / 2 := by
    have h := hT T le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)] at h
    exact h
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hdiv (T : ℝ)) (ε / 2) (by positivity)
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hdensity := hN₀ N hNN₀
  have hdensity0 : 0 ≤
      ((((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + u) ≤ (T : ℝ))).card : ℝ) /
          (N : ℝ)) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hdensity0] at hdensity
  have havg := divisorMassExpAvg_le_density_add v hv c hc u N (T : ℝ) hN1
  have havg0 : 0 ≤
      (∑ x : Fin N, Real.exp (-c *
        divisorVarianceMass v (collisionCutoff N) (x.val + (u + 1)))) / (N : ℝ) := by
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg havg0]
  exact havg.trans_lt (by linarith)

/-- Along the slow interpolation schedule, the collision cutoff eventually dominates every
fixed polynomial. -/
theorem eventually_pow_le_collisionCutoff_sched (d : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      (j + 3) ^ (d + 3) ≤
        collisionCutoff (NormalNumbers.CantorLiouville.sched (j + 3)) := by
  have hlog : Tendsto (fun j : ℕ => Real.log ((j + 3 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3))
  filter_upwards [hlog.eventually
    (eventually_ge_atTop (4 * ((d : ℝ) + 4)))] with j hj
  let J := j + 3
  let N := NormalNumbers.CantorLiouville.sched J
  have hJ : 1 ≤ J := by omega
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hN : (0 : ℝ) < N := by
    exact_mod_cast NormalNumbers.CantorLiouville.one_le_sched J
  have hsqrt : Real.sqrt (J : ℝ) ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hN]
    exact NormalNumbers.CantorLiouville.exp_sqrt_le_sched J hJ
  have hsqrt0 : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.2 hJR
  have hloglog : Real.log (J : ℝ) / 2 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.log_sqrt hJR.le]
    exact Real.log_le_log hsqrt0 hsqrt
  have hL : 4 * ((d : ℝ) + 4) ≤ Real.log (J : ℝ) := by
    simpa only [J, Nat.cast_add, Nat.cast_ofNat] using hj
  have hsq : ((d : ℝ) + 4) * Real.log (J : ℝ) ≤
      Real.log (Real.log (N : ℝ)) ^ 2 := by
    have hloglog0 : 0 ≤ Real.log (Real.log (N : ℝ)) := by
      have : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
      linarith
    nlinarith [sq_nonneg (Real.log (Real.log (N : ℝ)) - Real.log (J : ℝ) / 2)]
  apply Nat.le_floor
  calc
    (((J ^ (d + 3) : ℕ) : ℝ)) ≤ (J : ℝ) ^ (d + 4) := by
      push_cast
      rw [pow_succ]
      exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hJ)
    _ = Real.exp (((d : ℝ) + 4) * Real.log (J : ℝ)) := by
      rw [← Real.exp_log (pow_pos hJR (d + 4)), Real.log_pow]
      push_cast
      ring
    _ ≤ Real.exp (Real.log (Real.log (N : ℝ)) ^ 2) := Real.exp_le_exp.mpr hsq

/-- Any fixed polynomial divided by the collision cutoff is summable along the slow schedule. -/
theorem summable_pow_div_collisionCutoff_sched (d : ℕ) :
    Summable (fun j : ℕ =>
      ((j + 3 : ℕ) : ℝ) ^ d /
        collisionCutoff (NormalNumbers.CantorLiouville.sched (j + 3))) := by
  have hs : Summable (fun j : ℕ => ((j + 3 : ℕ) : ℝ) ^ (-(3 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 3).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  refine Summable.of_norm_bounded_eventually hs ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_pow_le_collisionCutoff_sched d] with j hj
  have hJ : (0 : ℝ) < (j + 3 : ℕ) := by positivity
  have hP : (0 : ℝ) < collisionCutoff
      (NormalNumbers.CantorLiouville.sched (j + 3)) := by
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < (j + 3) ^ (d + 3)) hj
  rw [Real.norm_of_nonneg (div_nonneg (by positivity) hP.le)]
  rw [Real.rpow_neg (le_of_lt hJ)]
  apply (div_le_iff₀ hP).2
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hJ (3 : ℝ))).2
  calc
    ((j + 3 : ℕ) : ℝ) ^ d * (((j + 3 : ℕ) : ℝ) ^ (3 : ℝ)) =
        (((j + 3 : ℕ) : ℝ) ^ (d + 3)) := by
      rw [show (((j + 3 : ℕ) : ℝ) ^ (3 : ℝ)) =
        (((j + 3 : ℕ) : ℝ) ^ (3 : ℕ)) by norm_num [Real.rpow_natCast], ← pow_add]
    _ ≤ collisionCutoff (NormalNumbers.CantorLiouville.sched (j + 3)) := by
      exact_mod_cast hj

/-- The slow schedule itself also eventually dominates every fixed polynomial. -/
theorem eventually_pow_le_sched (d : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      (j + 3) ^ (d + 3) ≤ NormalNumbers.CantorLiouville.sched (j + 3) := by
  have hJ : Tendsto (fun j : ℕ => ((j + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hlog := hJ.eventually
    (NormalNumbers.CantorLiouville.ev_log_le
      (r := (1 / 2 : ℝ)) (ε := 1 / ((d : ℝ) + 3)) (by norm_num) (by positivity))
  filter_upwards [hlog] with j hj
  let J := j + 3
  have hJ1 : 1 ≤ J := by omega
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ1
  have hroot : ((d : ℝ) + 3) * Real.log (J : ℝ) ≤ Real.sqrt (J : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have hd : (0 : ℝ) < (d : ℝ) + 3 := by positivity
    calc
      ((d : ℝ) + 3) * Real.log (J : ℝ) ≤
          ((d : ℝ) + 3) * (1 / ((d : ℝ) + 3) * (J : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
      _ = (J : ℝ) ^ (1 / 2 : ℝ) := by field_simp
  have hreal : ((J : ℝ) ^ (d + 3)) ≤
      NormalNumbers.CantorLiouville.sched J := by
    calc
      (J : ℝ) ^ (d + 3) = Real.exp (((d : ℝ) + 3) * Real.log (J : ℝ)) := by
        rw [← Real.exp_log (pow_pos hJR (d + 3)), Real.log_pow]
        push_cast
        ring
      _ ≤ Real.exp (Real.sqrt (J : ℝ)) := Real.exp_le_exp.mpr hroot
      _ ≤ NormalNumbers.CantorLiouville.sched J :=
        NormalNumbers.CantorLiouville.exp_sqrt_le_sched J hJ1
  exact_mod_cast hreal

/-- Any fixed polynomial divided by the slow schedule is summable. -/
theorem summable_pow_div_sched (d : ℕ) :
    Summable (fun j : ℕ =>
      ((j + 3 : ℕ) : ℝ) ^ d /
        NormalNumbers.CantorLiouville.sched (j + 3)) := by
  have hs : Summable (fun j : ℕ => ((j + 3 : ℕ) : ℝ) ^ (-(3 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 3).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  refine Summable.of_norm_bounded_eventually hs ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_pow_le_sched d] with j hj
  have hJ : (0 : ℝ) < (j + 3 : ℕ) := by positivity
  have hN : (0 : ℝ) < NormalNumbers.CantorLiouville.sched (j + 3) := by
    exact_mod_cast NormalNumbers.CantorLiouville.one_le_sched (j + 3)
  rw [Real.norm_of_nonneg (div_nonneg (by positivity) hN.le)]
  rw [Real.rpow_neg (le_of_lt hJ)]
  apply (div_le_iff₀ hN).2
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hJ (3 : ℝ))).2
  calc
    ((j + 3 : ℕ) : ℝ) ^ d * (((j + 3 : ℕ) : ℝ) ^ (3 : ℝ)) =
        (((j + 3 : ℕ) : ℝ) ^ (d + 3)) := by
      rw [show (((j + 3 : ℕ) : ℝ) ^ (3 : ℝ)) =
        (((j + 3 : ℕ) : ℝ) ^ (3 : ℕ)) by norm_num [Real.rpow_natCast], ← pow_add]
    _ ≤ NormalNumbers.CantorLiouville.sched (j + 3) := by exact_mod_cast hj

/-- Growing moment order used at the `j`-th slow-schedule checkpoint. -/
def endpointMomentOrder (j : ℕ) : ℕ := Nat.log 2 (j + 3) + 1

/-- Coarse phase cutoff; linear growth in the moment order is enough for the phase separation. -/
def endpointPhaseCutoff (e H j : ℕ) : ℕ :=
  e + 1 + 32 * H * endpointMomentOrder j

theorem endpointMomentOrder_pos (j : ℕ) : 1 ≤ endpointMomentOrder j := by
  unfold endpointMomentOrder
  omega

theorem endpointMomentOrder_le (j : ℕ) : endpointMomentOrder j ≤ 2 * (j + 3) := by
  unfold endpointMomentOrder
  have := Nat.log_le_self 2 (j + 3)
  omega

theorem endpointPhaseCutoff_le (e H j : ℕ) :
    endpointPhaseCutoff e H j ≤ (e + 1 + 64 * H) * (j + 3) := by
  unfold endpointPhaseCutoff
  have hk := endpointMomentOrder_le j
  have hJ : 1 ≤ j + 3 := by omega
  nlinarith

theorem endpoint_phase_large {b e H j : ℕ} (hb : 2 ≤ b) :
    16 * H * (2 * endpointMomentOrder j) ≤ b ^ endpointPhaseCutoff e H j := by
  let A := 32 * H * endpointMomentOrder j
  have hAK : A ≤ endpointPhaseCutoff e H j := by
    simp only [A, endpointPhaseCutoff]
    omega
  calc
    16 * H * (2 * endpointMomentOrder j) = A := by simp only [A]; ring
    _ ≤ 2 ^ A := (Nat.lt_two_pow_self).le
    _ ≤ 2 ^ endpointPhaseCutoff e H j := Nat.pow_le_pow_right (by norm_num) hAK
    _ ≤ b ^ endpointPhaseCutoff e H j := Nat.pow_le_pow_left hb _

theorem eventually_endpoint_cutoff_conditions (e H : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      2 * endpointPhaseCutoff e H j ≤
          collisionCutoff (NormalNumbers.CantorLiouville.sched (j + 3)) ∧
        endpointPhaseCutoff e H j ≤ NormalNumbers.CantorLiouville.sched (j + 3) := by
  let C := 2 * (e + 1 + 64 * H)
  filter_upwards [eventually_pow_le_collisionCutoff_sched 1,
    eventually_pow_le_sched 1, eventually_ge_atTop C] with j hP hN hj
  have hK := endpointPhaseCutoff_le e H j
  have hJ : 1 ≤ j + 3 := by omega
  have hCJ : C * (j + 3) ≤ (j + 3) ^ 4 := by
    calc
      C * (j + 3) ≤ (j + 3) * (j + 3) :=
        Nat.mul_le_mul_right (j + 3) (by omega)
      _ = (j + 3) ^ 2 := by ring
      _ ≤ (j + 3) ^ 4 := pow_le_pow_right' hJ (by omega)
  constructor
  · calc
      2 * endpointPhaseCutoff e H j ≤ C * (j + 3) := by
        calc
          _ ≤ 2 * ((e + 1 + 64 * H) * (j + 3)) := Nat.mul_le_mul_left 2 hK
          _ = C * (j + 3) := by simp only [C]; ring
      _ ≤ (j + 3) ^ (1 + 3) := by simpa using hCJ
      _ ≤ collisionCutoff (NormalNumbers.CantorLiouville.sched (j + 3)) := hP
  · calc
      endpointPhaseCutoff e H j ≤ (e + 1 + 64 * H) * (j + 3) := hK
      _ ≤ C * (j + 3) := by
        exact Nat.mul_le_mul_right (j + 3) (by simp only [C]; omega)
      _ ≤ (j + 3) ^ (1 + 3) := by simpa using hCJ
      _ ≤ NormalNumbers.CantorLiouville.sched (j + 3) := hN

theorem endpoint_threshold_factor_le (q j : ℕ) :
    (q + 1) ^ (2 * endpointMomentOrder j) ≤
      2 ^ (2 * (q + 1)) * (j + 3) ^ (2 * (q + 1)) := by
  let k := endpointMomentOrder j
  let J := j + 3
  let D := 2 * (q + 1)
  have hq : q + 1 ≤ 2 ^ (q + 1) := (Nat.lt_two_pow_self).le
  have hkpow : 2 ^ k ≤ 2 * J := by
    dsimp only [k, endpointMomentOrder, J]
    rw [pow_add, pow_one]
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (x := j + 3) (by omega)))
  calc
    (q + 1) ^ (2 * k) ≤ (2 ^ (q + 1)) ^ (2 * k) := Nat.pow_le_pow_left hq _
    _ = (2 ^ k) ^ D := by
      simp only [D]
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ (2 * J) ^ D := Nat.pow_le_pow_left hkpow _
    _ = 2 ^ D * J ^ D := by rw [mul_pow]
    _ = 2 ^ (2 * (q + 1)) * (j + 3) ^ (2 * (q + 1)) := by rfl

theorem endpoint_collision_prefactor_le (e H q j : ℕ) :
    (q + 1) ^ (2 * endpointMomentOrder j) *
        (4 * endpointMomentOrder j ^ 2 * endpointPhaseCutoff e H j) ≤
      (16 * (e + 1 + 64 * H) * 2 ^ (2 * (q + 1))) *
        (j + 3) ^ (2 * (q + 1) + 3) := by
  let k := endpointMomentOrder j
  let K := endpointPhaseCutoff e H j
  let J := j + 3
  let D := 2 * (q + 1)
  have hth := endpoint_threshold_factor_le q j
  have hk := endpointMomentOrder_le j
  have hK := endpointPhaseCutoff_le e H j
  calc
    (q + 1) ^ (2 * k) * (4 * k ^ 2 * K) ≤
        (2 ^ D * J ^ D) * (4 * (2 * J) ^ 2 * ((e + 1 + 64 * H) * J)) := by
      gcongr
    _ = (16 * (e + 1 + 64 * H) * 2 ^ D) * J ^ (D + 3) := by ring
    _ = (16 * (e + 1 + 64 * H) * 2 ^ (2 * (q + 1))) *
        (j + 3) ^ (2 * (q + 1) + 3) := by rfl

theorem endpoint_half_pow_le (j : ℕ) :
    ((1 / 2 : ℝ) ^ (2 * endpointMomentOrder j)) ≤ 1 / ((j + 3 : ℕ) : ℝ) ^ 2 := by
  have hp : (j + 3) ^ 2 ≤ 2 ^ (2 * endpointMomentOrder j) := by
    have hlt := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (j + 3)
    change j + 3 < 2 ^ endpointMomentOrder j at hlt
    calc
      (j + 3) ^ 2 ≤ (2 ^ endpointMomentOrder j) ^ 2 :=
        Nat.pow_le_pow_left hlt.le _
      _ = 2 ^ (2 * endpointMomentOrder j) := by
        rw [← pow_mul]
        congr 1
        ring
  have hJ : (0 : ℝ) < (j + 3 : ℕ) := by positivity
  have htwo : (0 : ℝ) < 2 ^ (2 * endpointMomentOrder j) := by positivity
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (pow_pos hJ 2)
  exact_mod_cast hp

/-- Variable even moments suffice for almost-sure Weyl convergence when every fixed threshold
has a summable normalized moment along the slow schedule. -/
theorem ae_tendsto_weylMean_of_growing_moment_sums
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → ℝ) (hG : Measurable G) (b : ℕ) (h : ℤ)
    (k : ℕ → ℕ) (hk : ∀ j, 1 ≤ k j)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ =>
      (∫ w, ‖ErdosBorweinPositive.weylMean b h (G w)
        (NormalNumbers.CantorLiouville.sched (j + 3))‖ ^ (2 * k j) ∂μ) /
          ((1 : ℝ) / (q + 1)) ^ (2 * k j))) :
    ∀ᵐ w ∂μ, Tendsto
      (fun N : ℕ => ErdosBorweinPositive.weylMean b h (G w) N) atTop (𝓝 0) := by
  let n : ℕ → ℕ := fun j => NormalNumbers.CantorLiouville.sched (j + 3)
  have hn : StrictMono n := by
    intro i j hij
    exact NormalNumbers.CantorLiouville.sched_strictMono (by omega)
  have hn1 (j : ℕ) : 1 ≤ n j := NormalNumbers.CantorLiouville.one_le_sched (j + 3)
  have hratio : Tendsto (fun j => (n (j + 1) : ℝ) / n j) atTop (𝓝 1) := by
    have hrat := NormalNumbers.CantorLiouville.sched_ratio.comp (tendsto_add_atTop_nat 3)
    simpa [n, Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrat
  have hWm (N : ℕ) : Measurable (fun w =>
      ErdosBorweinPositive.weylMean b h (G w) N) := by
    unfold ErdosBorweinPositive.weylMean
    fun_prop
  have hthreshold : ∀ q : ℕ, ∀ᵐ w ∂μ, ∀ᶠ j : ℕ in atTop,
      ‖ErdosBorweinPositive.weylMean b h (G w) (n j)‖ < (1 : ℝ) / (q + 1) := by
    intro q
    let ε : ℝ := 1 / (q + 1)
    have hε : 0 < ε := by positivity
    let f : ℕ → Ω → ℝ := fun j w =>
      (‖ErdosBorweinPositive.weylMean b h (G w) (n j)‖ / ε) ^ (2 * k j)
    have hf0 : ∀ j w, 0 ≤ f j w := fun j w => by positivity
    have hfm : ∀ j, Measurable (f j) := fun j =>
      (((hWm _).norm.div_const ε).pow_const _)
    have hfi : ∀ j, Integrable (f j) μ := fun j =>
      Integrable.of_bound (hfm j).aestronglyMeasurable
        (((q : ℝ) + 1) ^ (2 * k j)) (Eventually.of_forall fun w => by
          rw [Real.norm_of_nonneg (hf0 j w)]
          dsimp only [f, ε]
          have hnorm := norm_weylMean_le_one b h (G w) (n j) (hn1 j)
          have hbase : ‖ErdosBorweinPositive.weylMean b h (G w) (n j)‖ /
              ((1 : ℝ) / (q + 1)) ≤ (q : ℝ) + 1 := by
            calc
              _ ≤ 1 / ((1 : ℝ) / (q + 1)) :=
                div_le_div_of_nonneg_right hnorm (by positivity)
              _ = (q : ℝ) + 1 := by field_simp
          exact pow_le_pow_left₀ (by positivity) hbase (2 * k j))
    have hfI : ∀ j, ∫ w, f j w ∂μ =
        (∫ w, ‖ErdosBorweinPositive.weylMean b h (G w) (n j)‖ ^ (2 * k j) ∂μ) /
          ε ^ (2 * k j) := by
      intro j
      simp only [f, div_pow]
      rw [integral_div]
    have hsumf : Summable (fun j => ∫ w, f j w ∂μ) := by
      simp_rw [hfI]
      simpa only [n, ε] using hsum q
    have hlin : ∫⁻ w, ∑' j, ENNReal.ofReal (f j w) ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
        (r := ∑' j : ℕ, ∫ w, f j w ∂μ)) ?_
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hf0 j)) hsumf]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hfi j)
        (Eventually.of_forall (hf0 j))]
    have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
      (hfm j).ennreal_ofReal.aemeasurable) hlin
    filter_upwards [hae] with w hw
    have h1 : Tendsto (fun j => ENNReal.ofReal (f j w)) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hw.ne
    have h2 : Tendsto (fun j => f j w) atTop (𝓝 0) := by
      have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ w)] using ht
    obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 h2 1 zero_lt_one
    filter_upwards [eventually_ge_atTop J] with j hj
    have hfj := hJ j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf0 j w)] at hfj
    have hbase : ‖ErdosBorweinPositive.weylMean b h (G w) (n j)‖ / ε < 1 :=
      (pow_lt_one_iff_of_nonneg (by positivity)
        (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt (hk j)))).mp hfj
    dsimp only [ε] at hbase ⊢
    exact (div_lt_one hε).mp hbase
  have hall : ∀ᵐ w ∂μ, ∀ q : ℕ, ∀ᶠ j : ℕ in atTop,
      ‖ErdosBorweinPositive.weylMean b h (G w) (n j)‖ < (1 : ℝ) / (q + 1) := by
    rw [ae_all_iff]
    exact hthreshold
  filter_upwards [hall] with w hw
  have hsched : Tendsto (fun j =>
      ‖ErdosBorweinPositive.weylMean b h (G w) (n j)‖) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨q, hq⟩ := Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
    have hq' := hq q le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 1 / (q + 1))] at hq'
    obtain ⟨J, hJ⟩ := (eventually_atTop.1 (hw q))
    refine ⟨J, fun j hj => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact (hJ j hj).trans hq'
  have hsums : Tendsto (fun j =>
      ‖∑ t ∈ Finset.range (n j),
        Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (b : ℂ)^t * (G w : ℂ))‖ /
          (n j : ℝ)) atTop (𝓝 0) := by
    simpa only [ErdosBorweinPositive.weylMean, norm_div, Complex.norm_natCast] using hsched
  simpa only [ErdosBorweinPositive.weylMean] using
    (NormalNumbers.CantorLiouville.tendsto_of_tendsto_sched
      (fun t => Complex.exp
        (2 * Real.pi * Complex.I * (h : ℂ) * (b : ℂ)^t * (G w : ℂ)))
      (fun t => by
        rw [show 2 * Real.pi * Complex.I * (h : ℂ) * (b : ℂ)^t * (G w : ℂ) =
            ((2 * Real.pi * (h : ℝ) * (b : ℝ)^t * G w : ℝ) : ℂ) * Complex.I by
          norm_cast
          push_cast
          ring]
        exact (Complex.norm_exp_ofReal_mul_I _).le)
      n hn hratio hsums)

/-- The endpoint moment estimate is summable after normalization by every fixed rational
threshold.  This is the quantitative bridge from divisor-mass divergence to the growing-moment
Borel--Cantelli criterion. -/
theorem summable_endpoint_normalized_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (hdiv : ∀ a₀ : ℕ, ∀ T : ℝ, Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass (fun m => delta m * (1 - delta m)) (collisionCutoff N) (n + a₀)
          ≤ T)).card : ℝ) / N) atTop (𝓝 0))
    (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) (q : ℕ) :
    Summable (fun j : ℕ =>
      (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
        (NormalNumbers.CantorLiouville.sched (j + 3))‖ ^
          (2 * endpointMomentOrder j) ∂μ) /
        ((1 : ℝ) / (q + 1)) ^ (2 * endpointMomentOrder j)) := by
  let v : ℕ → ℝ := fun m => delta m * (1 - delta m)
  have hv (m : ℕ) : 0 ≤ v m := by
    dsimp only [v]
    exact mul_nonneg (hX.1 m).1 (sub_nonneg.mpr (hX.1 m).2)
  have hc : 0 < spectralConst b := spectralConst_pos b hb
  have hH0 : h.natAbs ≠ 0 := (Int.natAbs_pos.mpr hh).ne'
  obtain ⟨e, m, hm, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hH0 b (by omega : b ≠ 1)
  let n : ℕ → ℕ := fun j => NormalNumbers.CantorLiouville.sched (j + 3)
  let k : ℕ → ℕ := endpointMomentOrder
  let K : ℕ → ℕ := endpointPhaseCutoff e h.natAbs
  let P : ℕ → ℕ := fun j => collisionCutoff (n j)
  let φ : ℕ → ℝ := fun j =>
    (∑ x : Fin (n j), Real.exp (-spectralConst b *
      divisorVarianceMass v (P j) (x.val + (e + 1)))) / (n j : ℝ)
  have hn : StrictMono n := by
    intro i j hij
    exact NormalNumbers.CantorLiouville.sched_strictMono (by omega)
  have hφ : Tendsto φ atTop (𝓝 0) := by
    exact (tendsto_divisorMassExpAvg v hv (spectralConst b) hc e (hdiv e)).comp
      hn.tendsto_atTop
  let ε : ℝ := 1 / (q + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hφsmall : ∀ᶠ j : ℕ in atTop, φ j < ε / 2 :=
    (tendsto_order.1 hφ).2 (ε / 2) (by positivity)
  have hcut := eventually_endpoint_cutoff_conditions e h.natAbs
  let d : ℕ := 2 * (q + 1) + 3
  let C : ℕ := 16 * (e + 1 + 64 * h.natAbs) * 2 ^ (2 * (q + 1))
  have hsJ : Summable (fun j : ℕ => 1 / (((j + 3 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 3).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have hsP : Summable (fun j : ℕ =>
      (C : ℝ) * 3 * (((j + 3 : ℕ) : ℝ) ^ d /
        collisionCutoff (NormalNumbers.CantorLiouville.sched (j + 3)))) := by
    exact (summable_pow_div_collisionCutoff_sched d).mul_left ((C : ℝ) * 3)
  have hsN : Summable (fun j : ℕ =>
      (C : ℝ) * 4 * (((j + 3 : ℕ) : ℝ) ^ d /
        NormalNumbers.CantorLiouville.sched (j + 3))) := by
    exact (summable_pow_div_sched d).mul_left ((C : ℝ) * 4)
  have href : Summable (fun j : ℕ =>
      1 / (((j + 3 : ℕ) : ℝ) ^ 2) +
        (C : ℝ) * 3 * (((j + 3 : ℕ) : ℝ) ^ d / P j) +
        (C : ℝ) * 4 * (((j + 3 : ℕ) : ℝ) ^ d / n j)) := by
    simpa only [P, n] using (hsJ.add hsP).add hsN
  refine Summable.of_norm_bounded_eventually href ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hφsmall, hcut] with j hsmall hconditions
  have hk : 1 ≤ k j := endpointMomentOrder_pos j
  have hN : 1 ≤ n j := NormalNumbers.CantorLiouville.one_le_sched (j + 3)
  have hK : e + 1 ≤ K j := by simp [K, endpointPhaseCutoff]
  have hK1 : 1 ≤ K j := le_trans (by omega : 1 ≤ e + 1) hK
  have hKP : 2 * K j ≤ P j := by simpa only [K, P, n] using hconditions.1
  have hKN : K j ≤ n j := by simpa only [K, n] using hconditions.2
  have hP : 1 ≤ P j := by omega
  have hlarge : 16 * h.natAbs * (2 * k j) ≤ b ^ (K j) :=
    endpoint_phase_large hb
  have hmoment := ebMoment_le_divisorMassAvg_pow_add_collision μ delta X hX
    b e m (K j) (P j) (k j) (n j) h hb hk hN hP hKN hfac hm hK hlarge hKP
  have hφ0 : 0 ≤ φ j := by dsimp only [φ]; positivity
  have hfirst : (φ j) ^ (2 * k j) / ε ^ (2 * k j) ≤
      1 / (((j + 3 : ℕ) : ℝ) ^ 2) := by
    have hbase : φ j / ε ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hε]
      linarith
    calc
      (φ j) ^ (2 * k j) / ε ^ (2 * k j) = (φ j / ε) ^ (2 * k j) :=
        (div_pow _ _ _).symm
      _ ≤ (1 / 2 : ℝ) ^ (2 * k j) :=
        pow_le_pow_left₀ (div_nonneg hφ0 hε.le) hbase _
      _ ≤ 1 / (((j + 3 : ℕ) : ℝ) ^ 2) := endpoint_half_pow_le j
  have hprefactor :
      (((q + 1 : ℕ) : ℝ) ^ (2 * k j)) *
          (4 * (k j : ℝ) ^ 2 * (K j : ℝ)) ≤
        (C : ℝ) * (((j + 3 : ℕ) : ℝ) ^ d) := by
    exact_mod_cast endpoint_collision_prefactor_le e h.natAbs q j
  have hcollision :
      (4 * (k j : ℝ) ^ 2 * (K j : ℝ) *
          (3 / (P j : ℝ) + 4 / (n j : ℝ))) / ε ^ (2 * k j) ≤
        (C : ℝ) * 3 * (((j + 3 : ℕ) : ℝ) ^ d / (P j : ℝ)) +
          (C : ℝ) * 4 * (((j + 3 : ℕ) : ℝ) ^ d / (n j : ℝ)) := by
    calc
      (4 * (k j : ℝ) ^ 2 * (K j : ℝ) *
          (3 / (P j : ℝ) + 4 / (n j : ℝ))) / ε ^ (2 * k j) =
          ((((q + 1 : ℕ) : ℝ) ^ (2 * k j)) *
            (4 * (k j : ℝ) ^ 2 * (K j : ℝ))) *
              (3 / (P j : ℝ) + 4 / (n j : ℝ)) := by
        dsimp only [ε]
        rw [one_div_pow, one_div, div_inv_eq_mul]
        push_cast
        ring
      _ ≤ ((C : ℝ) * (((j + 3 : ℕ) : ℝ) ^ d)) *
          (3 / (P j : ℝ) + 4 / (n j : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hprefactor (by positivity)
      _ = (C : ℝ) * 3 * (((j + 3 : ℕ) : ℝ) ^ d / (P j : ℝ)) +
          (C : ℝ) * 4 * (((j + 3 : ℕ) : ℝ) ^ d / (n j : ℝ)) := by ring
  have hI0 : 0 ≤ ∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
      (n j)‖ ^ (2 * k j) ∂μ := integral_nonneg fun _ => by positivity
  rw [Real.norm_of_nonneg (div_nonneg hI0 (pow_nonneg hε.le _))]
  calc
    (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
        (n j)‖ ^ (2 * k j) ∂μ) / ε ^ (2 * k j) ≤
        ((φ j) ^ (2 * k j) + 4 * (k j : ℝ) ^ 2 * (K j : ℝ) *
          (3 / (P j : ℝ) + 4 / (n j : ℝ))) / ε ^ (2 * k j) :=
      div_le_div_of_nonneg_right (by simpa only [φ, v, P, n, k, K] using hmoment)
        (pow_nonneg hε.le _)
    _ = (φ j) ^ (2 * k j) / ε ^ (2 * k j) +
        (4 * (k j : ℝ) ^ 2 * (K j : ℝ) *
          (3 / (P j : ℝ) + 4 / (n j : ℝ))) / ε ^ (2 * k j) := by rw [add_div]
    _ ≤ 1 / (((j + 3 : ℕ) : ℝ) ^ 2) +
        ((C : ℝ) * 3 * (((j + 3 : ℕ) : ℝ) ^ d / (P j : ℝ)) +
          (C : ℝ) * 4 * (((j + 3 : ℕ) : ℝ) ^ d / (n j : ℝ))) :=
      add_le_add hfirst hcollision
    _ = 1 / (((j + 3 : ℕ) : ℝ) ^ 2) +
        (C : ℝ) * 3 * (((j + 3 : ℕ) : ℝ) ^ d / P j) +
        (C : ℝ) * 4 * (((j + 3 : ℕ) : ℝ) ^ d / n j) := by ring

/-- **Growing-moment criterion.**  If the variance divisor mass above `P₀(N)` of `n + a₀` diverges
in density, for every shift `a₀`, then a.s. `E_b` is normal in every base.  Proof:
1. Weyl moments factor over the independent coins.
2. A good `m` (dividing exactly one `n_i + a₀`, every other coordinate outside the last `K`
   residues) has `‖θ_m‖ ≥ |h| b^{-a₀}/2`.
3. On the no-collision event every `m > P₀` dividing some `n_i + a₀` is good, giving `φ_N^{2k}`.
   The collision count has expectation `≤ 4k²K(3/P₀ + 4/N)`.
4. Borel–Cantelli with `k_j = ⌈log j⌉`, then interpolation. -/
@[blueprint (title := "Diverging divisor variance mass forces random Erdős–Borwein normality")]
theorem ebRandom_ae_normal_of_divisorVariance_diverges
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (hdiv : ∀ a₀ : ℕ, ∀ T : ℝ, Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass (fun m => delta m * (1 - delta m)) (collisionCutoff N) (n + a₀)
          ≤ T)).card : ℝ) / N) atTop (𝓝 0)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · have hall : ∀ᵐ w ∂μ, ∀ h : ℤ, h ≠ 0 →
        Tendsto (fun N : ℕ => ErdosBorweinPositive.weylMean b h (ebLambert b X w) N)
          atTop (𝓝 0) := by
      rw [ae_all_iff]
      intro h
      by_cases hh : h = 0
      · exact Eventually.of_forall fun _ hne => absurd hh hne
      · have hsum : ∀ q : ℕ, Summable (fun j : ℕ =>
            (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
              (NormalNumbers.CantorLiouville.sched (j + 3))‖ ^
                (2 * endpointMomentOrder j) ∂μ) /
              ((1 : ℝ) / (q + 1)) ^ (2 * endpointMomentOrder j)) :=
          fun q => summable_endpoint_normalized_moments μ delta X hX hdiv b hb h hh q
        filter_upwards [ae_tendsto_weylMean_of_growing_moment_sums μ (ebLambert b X)
          (measurable_ebLambert b X hX.2.1) b h endpointMomentOrder
          endpointMomentOrder_pos hsum] with w hw _
        exact hw
    filter_upwards [hall] with w hw _
    apply NormalNumbers.QSpanCriterion.isNormal_of_weylAvg b hb
    intro h hh
    exact (hw h hh).congr fun N => weylMean_eq_weylAvg b h (ebLambert b X w) N
  · exact Eventually.of_forall fun _ hb' => absurd hb' hb

end NormalNumbers.ErdosBorweinEndpoint
