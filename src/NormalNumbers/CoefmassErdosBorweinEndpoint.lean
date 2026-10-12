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
