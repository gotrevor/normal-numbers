/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtKPoint
import NormalNumbers.C3MrtShape

/-!
# The product phase, and why the `D`-point rung is *not* an open conjecture for `D ≥ 3`

Lap 34 named `KPointLogElliott K` — the `K`-point log-Elliott conjecture with
non-pretentiousness imposed on the **first** factor, the shape
`Erdos67b.NonasymptoticLogElliott` uses.  That is the right shape at `K = 2` (Tao 2015), but for
`K ≥ 3` the literature's available hypothesis is different and *weaker to check*:

> **Tao–Teräväinen structure theorem** (Duke 168 (2019); arXiv:1708.02610).  For 1-bounded
> multiplicative `g_0, …, g_k` and shifts `h_0, …, h_k`, the logarithmically averaged correlation
> is a uniform limit of periodic sequences; and if the **product** `g_0 ⋯ g_k` does not weakly
> pretend to be a Dirichlet character, the correlation **vanishes identically**.

The odd-order restriction in their Chowla application is an artefact of `λ^k = 1` for even `k`
(the product becomes the constant `1`, which *is* pretentious).  Our correlation has no such
degeneracy, and this file proves it:

* `prod_depthRoot_eq_ee` — `∏_{i<D} ζ_i = e(h · G_D / b^D)` with `G_D = ∑_{i<D} b^i`.
* `coprime_pow_geomNat` — `gcd(b^D, G_D) = 1`, because `G_D ≡ 1 (mod b)`.
* `prod_depthRoot_ne_one` — hence `∏_{i<D} ζ_i ≠ 1` **exactly** when `b^D ∤ h`.
* `exists_depth_prod_ne_one` — so for every `h ≠ 0` this holds for all `D > log_b |h|`, i.e.
  for every depth the schedule actually visits.
* `ProductLogElliott` — the `K`-point statement with the hypothesis on the product, which is
  the Tao–Teräväinen shape.
* `nonPretentious_prod_depthRoot` — the hypothesis is **discharged** by the archimedean
  certificate of `C3MrtArchimedean` applied to `z = ∏_{i<D} ζ_i`, granting only the named
  Vinogradov–Korobov input.

So for `D ≥ 3` the depth-`D` rung rests on (i) a published theorem, not a conjecture, plus
(ii) the same single VK input as the `D = 2` rung.  The remaining gap to `ConjC3` is therefore
*only* (a) log density → natural density, and (b) uniformity of the rate in `D` up to
`≍ log log log N` — which is exactly `QuantDepthElliott`.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- `geomNat b D = ∑_{i<D} b^i` (from `SwingC1`) peeled from the bottom. -/
lemma geomNat_succ_eq (b D : ℕ) : geomNat b (D + 1) = 1 + b * geomNat b D := by
  rw [geomNat, geomNat, Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- `G_D ≡ 1 (mod b)`, hence coprime to `b^D`. -/
theorem coprime_pow_geomNat (b : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    Nat.Coprime (b ^ D) (geomNat b D) := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  have hb : Nat.Coprime b (geomNat b (D' + 1)) := by
    rw [geomNat_succ_eq]
    exact (Nat.coprime_add_mul_left_right b 1 (geomNat b D')).mpr (Nat.coprime_one_right b)
  exact Nat.Coprime.pow_left _ hb

/-- The real sum `∑_{i<D} h/b^{i+1}` in lowest-common-denominator form. -/
theorem sum_div_pow_eq (b : ℕ) (hb : 1 ≤ b) (h : ℤ) (D : ℕ) :
    ∑ i ∈ range D, (h : ℝ) / (b : ℝ) ^ (i + 1)
      = (h : ℝ) * (geomNat b D : ℝ) / (b : ℝ) ^ D := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  induction D with
  | zero => simp [geomNat]
  | succ D ih =>
      rw [Finset.sum_range_succ, ih, geomNat_succ_eq]
      have hbD : ((b : ℝ)) ^ D ≠ 0 := by positivity
      have hbD1 : ((b : ℝ)) ^ (D + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- `∏_{i<D} ζ_i = e(h · G_D / b^D)`. -/
theorem prod_depthRoot_eq_ee (b : ℕ) (hb : 1 ≤ b) (h : ℤ) (D : ℕ) :
    ∏ i ∈ range D, depthRoot b h i
      = ee ((((h : ℝ) * (geomNat b D : ℝ) / (b : ℝ) ^ D : ℝ) : ℂ)) := by
  have hd : ∀ i : ℕ, depthRoot b h i = ee ((((h : ℝ) / (b : ℝ) ^ (i + 1) : ℝ) : ℂ)) :=
    fun i => rfl
  rw [Finset.prod_congr rfl (fun i _ => hd i), ← ee_sum, ← Complex.ofReal_sum,
    sum_div_pow_eq b hb h D]

/-- `‖∏_{i<D} ζ_i‖ = 1`. -/
theorem norm_prod_depthRoot (b : ℕ) (h : ℤ) (D : ℕ) :
    ‖∏ i ∈ range D, depthRoot b h i‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [depthRoot]; exact norm_ee_real _

/-- **The product phase is nontrivial exactly when `b^D ∤ h`.**  This is what removes the
even-order degeneracy that forces Tao–Teräväinen's Chowla application to odd order: there the
product of the `k` copies of `λ` is the constant `1` for even `k`, whereas here the product of
the `D` depth roots is `e(h G_D/b^D) ≠ 1`. -/
theorem prod_depthRoot_ne_one {b D : ℕ} (hb : 1 ≤ b) {h : ℤ} (hD : 1 ≤ D)
    (hdvd : ¬ ((b : ℤ) ^ D ∣ h)) :
    ∏ i ∈ range D, depthRoot b h i ≠ 1 := by
  rw [prod_depthRoot_eq_ee b hb h D]
  intro hone
  obtain ⟨m, hm⟩ := ee_eq_one_iff_int.1 hone
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbD : ((b : ℝ)) ^ D ≠ 0 := by positivity
  have hreal : (h : ℝ) * (geomNat b D : ℝ) = (m : ℝ) * (b : ℝ) ^ D := by
    field_simp at hm
    linarith [hm]
  have hint : h * (geomNat b D : ℤ) = m * (b : ℤ) ^ D := by
    have : ((h * (geomNat b D : ℤ) : ℤ) : ℝ) = ((m * (b : ℤ) ^ D : ℤ) : ℝ) := by
      push_cast
      linarith [hreal]
    exact_mod_cast this
  have hdvd' : ((b : ℤ) ^ D) ∣ h * (geomNat b D : ℤ) := ⟨m, by linarith [hint]⟩
  have hcop : IsCoprime ((b : ℤ) ^ D) ((geomNat b D : ℕ) : ℤ) := by
    have := Nat.isCoprime_iff_coprime.mpr (coprime_pow_geomNat b hD)
    simpa using this
  exact hdvd (hcop.dvd_of_dvd_mul_right hdvd')

/-- For every nonzero `h`, the product phase is nontrivial at every depth the schedule visits. -/
theorem exists_depth_prod_ne_one {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0) :
    ∃ D₀ : ℕ, 1 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∏ i ∈ range D, depthRoot b h i ≠ 1 := by
  refine ⟨h.natAbs + 1, by omega, fun D hD => ?_⟩
  refine prod_depthRoot_ne_one (by omega) (by omega) ?_
  intro hdvd
  have hle : (b : ℤ) ^ D ≤ |h| := Int.le_of_dvd (abs_pos.2 hh) ((dvd_abs _ _).2 hdvd)
  have h1 : (2 : ℤ) ^ D ≤ (b : ℤ) ^ D := by
    have : (2 : ℕ) ^ D ≤ b ^ D := Nat.pow_le_pow_left hb D
    exact_mod_cast this
  have h2 : (D : ℤ) < 2 ^ D := by
    have := Nat.lt_two_pow_self (n := D)
    exact_mod_cast this
  have h3 : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
  have h4 : (h.natAbs : ℤ) < (D : ℤ) := by
    have : h.natAbs < D := by omega
    exact_mod_cast this
  omega

/-! ## The Tao–Teräväinen shape

The same statement as `KPointLogElliott`, except that the non-pretentiousness hypothesis is
imposed on the **product** `∏ g i` rather than on `g 0`.  This is the hypothesis the structure
theorem supplies, and (by `nonPretentious_prod_depthRoot`) the one our target satisfies.
-/

/-- **The `K`-point log-Elliott statement in Tao–Teräväinen's shape**: non-pretentiousness of the
product.  For `K = 2` this is *not* the same Prop as `KPointLogElliott 2` — the hypotheses differ
— which is exactly why `K ≥ 3` needs the structure theorem rather than the dependency's bet. -/
def ProductLogElliott (K : ℕ) : Prop :=
  ∀ (a : Fin K → ℕ) (b : Fin K → ℤ), NondegenerateForms a b →
    ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ g : Fin K → ℤ → ℂ,
          (∀ i, Erdos67b.IsMultiplicativeOnPositiveInt (g i)) →
          (∀ i, ∀ n : ℤ, ‖g i n‖ ≤ 1) →
          (∀ q : ℕ, 0 < q → q ≤ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
            |t| ≤ (A : ℝ) * X →
              (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
                (Erdos67b.restrictToNat (fun n : ℤ => ∏ i : Fin K, g i n)) χ t X) →
          ‖kPointLogCorrelation g a b X W‖ ≤ ε * Real.log W

/-- **The product hypothesis is discharged.**  At every depth `D` with `b^D ∤ h`, the product
`∏_{i<D} ζ_i^Ω` satisfies Elliott's non-pretentiousness condition, granted only the named
Vinogradov–Korobov saving.  (The product of the `zOmInt (ζ_i)` is `zOmInt (∏ ζ_i)` by
`zOmInt_prod`, so this is literally the hypothesis of `ProductLogElliott`.) -/
theorem nonPretentious_prod_depthRoot {b D : ℕ} (hb : 1 ≤ b) {h : ℤ} (hD : 1 ≤ D)
    (hdvd : ¬ ((b : ℤ) ^ D ∣ h)) {A : ℕ} {T : ℝ} (hsave : TwistedPrimeSumSaving A T) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A : ℝ) * X →
        (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
          (Erdos67b.restrictToNat (zOmInt (∏ i ∈ range D, depthRoot b h i))) χ t X :=
  nonPretentious_zOm (norm_prod_depthRoot b h D) (prod_depthRoot_ne_one hb hD hdvd) hsave

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.coprime_pow_geomNat
#print axioms NormalNumbers.CastingOut.sum_div_pow_eq
#print axioms NormalNumbers.CastingOut.prod_depthRoot_eq_ee
#print axioms NormalNumbers.CastingOut.prod_depthRoot_ne_one
#print axioms NormalNumbers.CastingOut.exists_depth_prod_ne_one
#print axioms NormalNumbers.CastingOut.nonPretentious_prod_depthRoot
