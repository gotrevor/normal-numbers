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
  sorry

end NormalNumbers.ErdosBorweinEndpoint
