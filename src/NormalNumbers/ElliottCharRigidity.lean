import NormalNumbers.ElliottTwistBootstrap

/-!
# Input (d) DERIVED: rigidity of character clustering

`ElliottTwistBootstrap` reduced the crux `TwistModulusDichotomy` to two inputs, (c) the
Archimedean prime correlation bound and (d) `CharacterClusterRigidity`.  This file *proves* (d)
from a single standard statement — **Mertens for arithmetic progressions** — plus finite algebra.
So the crux now rests on (c) and the prime density in progressions, and nothing else.

The argument, once the frequency has been de-twisted away (`exists_charDefect_le`):

* clustering `∑_{p≤X}(1 − Re(β̄ χ̄(p)))/p ≤ θM` restricted to the primes in a fixed unit class `a`
  gives `(1 − Re(β̄ χ̄(a)))·S_a ≤ θM`, and `S_a ≥ cM − B` makes the factor `≤ 2θ/c`;
* hence `‖χ̄(a) − β‖² = 2 − 2Re(β̄χ̄(a)) ≤ 4θ/c` for every unit class, in particular for `a = 1`
  where `χ̄(1) = 1`, so `‖β − 1‖ ≤ 2√(θ/c)` and therefore `‖χ(a) − 1‖ ≤ 4√(θ/c)` for all `a`;
* finally `χ(a)^{φ(q)} = 1` (`dirichletChar_pow_totient`) and the elementary gap
  **`eq_one_of_pow_eq_one_of_norm_lt`**: a `k`-th root of unity within `2/k` of `1` *is* `1`.
  Proof: if `z ≠ 1` then `∑_{m<k} z^m = 0`, so `k = ‖∑_{m<k}(1 − z^m)‖ ≤ (∑_{m<k} m)‖1 − z‖
  ≤ (k²/2)‖1 − z‖`.  No root-of-unity classification, no cyclotomic theory.

The quantifier order matters and is honest: `θ` must be smaller than `c/(4A²)`, so rigidity holds
*for each level `A` with its own `θ`* — which is exactly the shape
`exists_delta_twistModulusDichotomy` consumes.
-/

open Finset

namespace NormalNumbers.ElliottCharRigidity

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious NormalNumbers.ElliottTwistBootstrap
  NormalNumbers.CastingOut NormalNumbers.ElliottTwoPointLog

noncomputable section

/-- **The root-of-unity gap.**  A `k`-th root of unity within `1/k` of `1` is `1`.

Elementary: if `z ≠ 1` then `∑_{m<k} z^m = 0`, so `k = ‖∑_{m<k}(1 − z^m)‖ ≤ k²‖1 − z‖`. -/
theorem eq_one_of_pow_eq_one_of_norm_lt {z : ℂ} {k : ℕ} (hk : 0 < k) (hz : z ^ k = 1)
    (hnorm : ‖1 - z‖ < 1 / k) : z = 1 := by
  by_contra hne
  have hznorm : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ k = 1 := by rw [← norm_pow, hz, norm_one]
    rcases (pow_eq_one_iff_cases (R := ℝ)).mp h1 with h | h | h
    · omega
    · exact h
    · exact absurd h.1 (by nlinarith [norm_nonneg z])
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : ∑ m ∈ Finset.range k, z ^ m = 0 := by
    have h := geom_sum_mul z k
    rw [hz, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hz1
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsplit : (k : ℂ) = ∑ m ∈ Finset.range k, (1 - z ^ m) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, Finset.card_range]
    simp
  have hbound : (k : ℝ) ≤ (k : ℝ) * (k : ℝ) * ‖1 - z‖ := by
    calc (k : ℝ) = ‖(k : ℂ)‖ := (Complex.norm_natCast k).symm
      _ = ‖∑ m ∈ Finset.range k, (1 - z ^ m)‖ := by rw [← hsplit]
      _ ≤ ∑ m ∈ Finset.range k, ‖1 - z ^ m‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.range k, (k : ℝ) * ‖1 - z‖ := by
          refine Finset.sum_le_sum ?_
          intro m hm
          refine le_trans (norm_one_sub_pow_le (le_of_eq hznorm) m) ?_
          have : (m : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (Finset.mem_range.mp hm).le
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = (k : ℝ) * (k : ℝ) * ‖1 - z‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  rw [lt_div_iff₀ hkR] at hnorm
  nlinarith

/-! ### Mertens for progressions, as the one analytic input -/

/-- The prime reciprocal mass of a single residue class mod `q`. -/
def primeClassMass (q : ℕ) (a : ZMod q) (X : ℕ) : ℝ :=
  ∑ p ∈ (primesUpTo X).filter (fun p : ℕ => (Nat.cast p : ZMod q) = a), (p : ℝ)⁻¹

/-- **Mertens for arithmetic progressions.**  Every unit class mod `q ≤ A` carries a fixed
positive proportion of the prime reciprocal mass.  Classical (Dirichlet / Mertens in APs); no
zero-free region is needed, only the nonvanishing `L(1,χ) ≠ 0`. -/
def PrimeDensityAP (A : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, ∀ q : ℕ, 0 < q → q ≤ A → ∀ a : ZMod q, IsUnit a →
    ∀ X : ℕ, c * primeMass X - B ≤ primeClassMass q a X

/-- Restricting the clustering sum to one residue class: the class's whole mass is multiplied by
the single defect of that class's character value. -/
theorem class_defect_le {q : ℕ} (χ : DirichletCharacter ℂ q) (β : ℂ) (hβ : ‖β‖ = 1)
    (a : ZMod q) (X : ℕ) :
    (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re) * primeClassMass q a X
      ≤ twistDefect (fun p => (starRingEnd ℂ) (χ p)) β X := by
  classical
  have hwn : ∀ p ∈ primesUpTo X, ‖(starRingEnd ℂ) (χ p)‖ ≤ 1 := by
    intro p _
    rw [RCLike.norm_conj]
    exact χ.norm_le_one p
  have hterms : ∀ p ∈ primesUpTo X, 0 ≤ (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ p)).re) /
      (p : ℝ) := by
    intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (mem_primesUpTo.mp hp).1.pos
    have hnorm : ‖(starRingEnd ℂ) β * (starRingEnd ℂ) (χ p)‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj, hβ, one_mul]
      exact hwn p hp
    have := le_trans (Complex.re_le_norm ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ p))) hnorm
    have hnum : 0 ≤ 1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ p)).re := by linarith
    positivity
  have hsub : (primesUpTo X).filter (fun p : ℕ => (Nat.cast p : ZMod q) = a) ⊆ primesUpTo X :=
    Finset.filter_subset _ _
  calc (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re) * primeClassMass q a X
      = ∑ p ∈ (primesUpTo X).filter (fun p : ℕ => (Nat.cast p : ZMod q) = a),
          (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ p)).re) / (p : ℝ) := by
        rw [primeClassMass, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p hp
        have hpa : ((p : ℕ) : ZMod q) = a := (Finset.mem_filter.mp hp).2
        rw [hpa, div_eq_mul_inv]
    _ ≤ twistDefect (fun p => (starRingEnd ℂ) (χ p)) β X :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hterms p hp)

/-- **INPUT (d), DERIVED.**  Mertens for progressions implies the rigidity of character
clustering, with the explicit admissible `θ = c/(32A²)`. -/
theorem exists_characterClusterRigidity {A : ℕ} (hA : 0 < A) (hdens : PrimeDensityAP A) :
    ∃ θ : ℝ, 0 < θ ∧ CharacterClusterRigidity A θ := by
  classical
  obtain ⟨c, hc, B, hB⟩ := hdens
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  set θ : ℝ := c / (32 * (A : ℝ) ^ 2) with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  obtain ⟨X₀, hX₀2, hX₀⟩ := exists_primeMass_ge (2 * B / c)
  refine ⟨θ, hθ, X₀, hX₀2, ?_⟩
  intro X hX q hq hqA χ β hβ hclust
  have hX2 : 2 ≤ X := le_trans hX₀2 hX
  have hMpos : 0 < primeMass X := primeMass_pos hX2
  have hMB : 2 * B / c ≤ primeMass X := hX₀ X hX
  have hlow : (c / 2) * primeMass X ≤ c * primeMass X - B := by
    rw [div_le_iff₀ hc] at hMB
    linarith
  have hhalf : 0 < (c / 2) * primeMass X := by positivity
  -- the uniform bound on each unit class
  have key : ∀ a : ZMod q, IsUnit a →
      ‖β - (starRingEnd ℂ) (χ a)‖ ^ 2 ≤ 4 * θ / c := by
    intro a ha
    have hS : (c / 2) * primeMass X ≤ primeClassMass q a X :=
      le_trans hlow (hB q hq hqA a ha X)
    have hcls := class_defect_le χ β hβ a X
    have hnorma : ‖(starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj, RCLike.norm_conj, hβ, one_mul]
      exact χ.norm_le_one a
    have hre1 : ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re ≤ 1 :=
      le_trans (Complex.re_le_norm _) hnorma
    have hnn : 0 ≤ 1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re := by linarith
    have hdefle : (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re) *
        ((c / 2) * primeMass X) ≤ θ * primeMass X := by
      calc (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re) * ((c / 2) * primeMass X)
          ≤ (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re) * primeClassMass q a X :=
            mul_le_mul_of_nonneg_left hS hnn
        _ ≤ twistDefect (fun p => (starRingEnd ℂ) (χ p)) β X := hcls
        _ ≤ θ * primeMass X := hclust
    have hfac : (1 - ((starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)).re) ≤ 2 * θ / c := by
      rw [le_div_iff₀ hc]
      nlinarith [hdefle, hMpos]
    have hsq := norm_one_sub_sq_le hnorma
    have hshift : ‖β - (starRingEnd ℂ) (χ a)‖ = ‖1 - (starRingEnd ℂ) β * (starRingEnd ℂ) (χ a)‖ := by
      have : β * (1 - (starRingEnd ℂ) β * (starRingEnd ℂ) (χ a))
          = β - (starRingEnd ℂ) (χ a) := by
        have hββ : β * (starRingEnd ℂ) β = ((‖β‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj]
          norm_cast
          exact Complex.normSq_eq_norm_sq β
        rw [mul_sub, mul_one, ← mul_assoc, hββ, hβ]
        norm_num
      rw [← this, norm_mul, hβ, one_mul]
    rw [hshift]
    have heq : 2 * (2 * θ / c) = 4 * θ / c := by ring
    linarith [hsq, hfac]
  -- the two classes we need
  have hone : ‖β - 1‖ ^ 2 ≤ 4 * θ / c := by
    have h1 : ((starRingEnd ℂ) (χ (1 : ZMod q))) = 1 := by
      rw [MulChar.map_one]; simp
    have := key 1 isUnit_one
    rwa [h1] at this
  intro p₀ hp₀ hp₀q
  have hcop : Nat.Coprime p₀ q := (Nat.Prime.coprime_iff_not_dvd hp₀).mpr hp₀q
  have hunit : IsUnit ((p₀ : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime p₀ q).2 hcop
  have hp := key ((p₀ : ℕ) : ZMod q) hunit
  -- combine
  set G : ℝ := Real.sqrt (4 * θ / c) with hG
  have hGnn : 0 ≤ G := Real.sqrt_nonneg _
  have hGsq : G ^ 2 = 4 * θ / c := Real.sq_sqrt (by positivity)
  have hb1 : ‖β - 1‖ ≤ G := by
    have := Real.sqrt_le_sqrt hone
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hb2 : ‖β - (starRingEnd ℂ) (χ p₀)‖ ≤ G := by
    have := Real.sqrt_le_sqrt hp
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have htri : ‖1 - (starRingEnd ℂ) (χ p₀)‖ ≤ 2 * G := by
    calc ‖1 - (starRingEnd ℂ) (χ p₀)‖
        ≤ ‖1 - β‖ + ‖β - (starRingEnd ℂ) (χ p₀)‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) β ((starRingEnd ℂ) (χ p₀))
      _ ≤ G + G := by rw [norm_sub_rev] at hb1; linarith
      _ = 2 * G := by ring
  have hconj : ‖1 - χ p₀‖ = ‖1 - (starRingEnd ℂ) (χ p₀)‖ := by
    rw [← RCLike.norm_conj (1 - χ p₀), map_sub, map_one]
  set k : ℕ := q.totient with hk
  have hk0 : 0 < k := Nat.totient_pos.mpr hq
  have hkA : (k : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast le_trans (Nat.totient_le q) hqA
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hgap : 2 * G < 1 / (k : ℝ) := by
    have hsq : (2 * G) ^ 2 < (1 / (k : ℝ)) ^ 2 := by
      have h1 : (2 * G) ^ 2 = 4 * (4 * θ / c) := by rw [mul_pow, hGsq]; ring
      have h2 : 4 * (4 * θ / c) = 1 / (2 * (A : ℝ) ^ 2) := by
        rw [hθdef]
        field_simp
        ring
      have h3 : 1 / (2 * (A : ℝ) ^ 2) < 1 / (k : ℝ) ^ 2 := by
        have : (k : ℝ) ^ 2 < 2 * (A : ℝ) ^ 2 := by nlinarith
        exact one_div_lt_one_div_of_lt (by positivity) this
      rw [h1, h2, div_pow, one_pow]
      exact h3
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  refine eq_one_of_pow_eq_one_of_norm_lt hk0
    (dirichletChar_pow_totient χ hq hp₀ hp₀q) ?_
  rw [hconj]
  linarith

/-- Rigidity at every level, `A = 0` included (where the statement is vacuous). -/
theorem exists_characterClusterRigidity_all (hdens : ∀ A : ℕ, PrimeDensityAP A) (A : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ CharacterClusterRigidity A θ := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · exact ⟨1, one_pos, 2, le_rfl, by intro X _ q hq hqA; omega⟩
  · exact exists_characterClusterRigidity hA (hdens A)

/-- **THE PAYOFF, on two classical statements.**  C1's two-point leaf in logarithmic average, for
every `ζ = e(t/b) ≠ 1`, granted only

* (c) the Archimedean prime correlation bound `ArchimedeanCorrelationBound`, and
* (d1) Mertens for arithmetic progressions `PrimeDensityAP`.

Everything else in the chain — Tao's Theorem 1.3 for merely multiplicative `gᵢ`, its application
to `ζ^ω`, the power bootstrap, the de-twisting, the character rigidity — is machine-checked. -/
theorem twoPointElliottLog_of_archimedean_and_density {b p q : ℕ} {t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (phase (t / b)).re < 1) {η : ℝ} (hη : 0 < η)
    (harch : ∀ A : ℕ, ArchimedeanCorrelationBound A η)
    (hdens : ∀ A : ℕ, PrimeDensityAP A) :
    TwoPointElliottLog b p q t :=
  twoPointElliottLog_of_classical_inputs hp hq hpq hu hη harch
    (exists_characterClusterRigidity_all hdens)

end

end NormalNumbers.ElliottCharRigidity
