/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffSixDFI
import Mathlib.NumberTheory.PrimeCounting

/-!
# Positive-density thinning removes the restricted-equidistribution requirement

The old `RestrictedRootFar` fixes distance 1/4.  Nonvanishing needs only SOME
positive distance.  A positive-density set of eligible primes cannot all lie
in the arbitrarily small boundary neighborhoods supplied by unrestricted DFI.

Two analytic inputs are explicit hypotheses, not proved here:
* `EligiblePositiveDensity`: a Chebotarev specialization for our eligible primes;
* `DFIBoundaryScarcity`: a weakening of unrestricted DFI 1995, pp. 423–424,
  read from the local paper.  For f = x²+64x+4096, ac-b² = 3072 > 0.
  Count bad primes by boundary ROOTS; DFI gives asymptotic 2ε π(X) for
  their number (at most two roots per prime).  Taking ε small gives the node.

The positive-density specialization is kept separate from the sourced DFI
input.  Its intended justification is Chebotarev in
Q(ζ₁₂₀, ∛2): [Q(ζ₁₂₀):Q]=32 and the relative cubic extension has degree 3.
The two nonidentity elements above identity give density 2/96=1/48.
This field-theoretic specialization is not formalized in this file.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

def EligiblePrime (p : ℕ) : Prop :=
  ∃ t : ℕ, p = 120*t+1 ∧ Nat.Prime p ∧ (2 : ZMod p)^(20*t) ≠ 1

noncomputable def eligiblePrimes (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter EligiblePrime

/-- A prime is bad if ANY root of the quadratic is close to an integer.
There is no progression or power-residue restriction in this definition. -/
noncomputable def boundaryPrimes (ε : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter fun p => Nat.Prime p ∧
    ∃ b : ℤ, (p : ℤ) ∣ b^2 + 64*b + 4096 ∧ dZ ((b : ℝ) / p) < ε

/-- Explicit arithmetic input.  Expected from the Chebotarev specialization
described above; the exact value 1/48 is unnecessary for the bridge. -/
def EligiblePositiveDensity : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    δ * (Nat.primeCounting' X : ℝ) ≤ (eligiblePrimes X).card

/-- Chebotarev specialization, retained as an explicit literature input.
The proposed specialization has density 1/48, with these arithmetic checks:
L = Q(ζ₁₂₀) is abelian of degree 32.  It cannot contain ∛2, since every
subfield of an abelian Galois extension is Galois over Q whereas Q(∛2) is not.
Thus K = L(∛2) has relative degree 3.  Both K and L are Galois over Q;
the two nonidentity elements of Gal(K/L) form a conjugacy-stable subset
of size 2 in Gal(K/Q), of order 96.  For p ≡ 1 mod 120, 2 is a square,
so the nontrivial cubic Frobenius condition is exactly 2^((p-1)/6) ≠ 1.
No Chebotarev theorem or number-field specialization is proved in this module. -/
def EligibleChebotarevDensity : Prop :=
  Filter.Tendsto
    (fun X : ℕ => ((eligiblePrimes X).card : ℝ) / Nat.primeCounting' X)
    Filter.atTop (nhds (1/48 : ℝ))

theorem eligiblePositiveDensity_of_chebotarev (h : EligibleChebotarevDensity) :
    EligiblePositiveDensity := by
  obtain ⟨X₀, hX₀⟩ := (Metric.tendsto_atTop.1 h) (1/96) (by norm_num)
  refine ⟨1/96, by norm_num, max X₀ 3, fun X hX => ?_⟩
  have hApprox := hX₀ X (le_trans (le_max_left _ _) hX)
  rw [Real.dist_eq] at hApprox
  have hLower := (abs_lt.mp hApprox).1
  have hPos : 0 < Nat.primeCounting' X := by
    have : 3 ≤ X := le_trans (le_max_right _ _) hX
    have : Nat.primeCounting' X ≠ 0 := by
      intro hz
      have := Nat.primeCounting'_eq_zero_iff.mp hz
      omega
    omega
  have hPosR : (0 : ℝ) < Nat.primeCounting' X := by exact_mod_cast hPos
  have hRatio : (1/96 : ℝ) ≤ (eligiblePrimes X).card / (Nat.primeCounting' X : ℝ) := by
    linarith
  exact (le_div_iff₀ hPosR).mp hRatio

/-- Literature consequence of UNRESTRICTED DFI (1995), Theorem, p. 424.
Every prescribed small density bound holds in some fixed positive boundary
neighborhood.  This does not assert a rate uniform in the neighborhood. -/
def DFIBoundaryScarcity : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    ((boundaryPrimes ε X).card : ℝ) ≤ η * (Nat.primeCounting' X : ℝ)

/-- Finite counting core: more than N surplus elements give one beyond N. -/
theorem exists_large_mem_not_mem (S T : Finset ℕ) (N : ℕ)
    (h : T.card + N < S.card) :
    ∃ p ∈ S, N ≤ p ∧ p ∉ T := by
  classical
  by_contra hn
  have hsub : S ⊆ Finset.range N ∪ T := by
    intro p hp
    by_cases hNp : N ≤ p
    · have hpT : p ∈ T := by
        by_contra hpT
        exact hn ⟨p, hp, hNp, hpT⟩
      exact Finset.mem_union_right _ hpT
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le (Finset.range N) T
  simp only [Finset.card_range] at hunion
  omega

@[blueprint (title := "Unrestricted DFI and positive prime density imply cutoff-six root escape")]
theorem quadraticRootEscape_of_density
    (hSupply : EligiblePositiveDensity) (hDFI : DFIBoundaryScarcity) :
    QuadraticRootEscape := by
  classical
  obtain ⟨δ, hδ, X₁, hSupply⟩ := hSupply
  obtain ⟨ε, hε, X₂, hBoundary⟩ := hDFI (δ/2) (by positivity)
  refine ⟨ε, hε, fun N => ?_⟩
  let P := 120*N+1
  obtain ⟨M, hM⟩ := exists_nat_gt ((P : ℝ) / (δ/2))
  obtain ⟨Y, hY⟩ := Nat.surjective_primeCounting' M
  let X := max Y (max X₁ X₂)
  have hCount : M ≤ Nat.primeCounting' X := by
    rw [← hY]
    exact Nat.monotone_primeCounting' (le_max_left _ _)
  have hS := hSupply X (le_trans (le_max_left _ _) (le_max_right _ _))
  have hB := hBoundary X (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMargin : (P : ℝ) < (δ/2) * (M : ℝ) := by
    have := (div_lt_iff₀ (show 0 < δ/2 by positivity)).mp hM
    nlinarith
  have hCountR : (M : ℝ) ≤ Nat.primeCounting' X := by exact_mod_cast hCount
  have hSurplusR : ((boundaryPrimes ε X).card : ℝ) + P < (eligiblePrimes X).card := by
    nlinarith
  have hSurplus : (boundaryPrimes ε X).card + P < (eligiblePrimes X).card := by
    exact_mod_cast hSurplusR
  obtain ⟨p, hpS, hpP, hpB⟩ :=
    exists_large_mem_not_mem (eligiblePrimes X) (boundaryPrimes ε X) P hSurplus
  obtain ⟨hpX, t, rfl, hp, hζ⟩ := Finset.mem_filter.mp hpS
  refine ⟨t, by dsimp [P] at hpP; omega, hp, hζ, fun b hb => ?_⟩
  by_contra hfar
  apply hpB
  exact Finset.mem_filter.mpr ⟨hpX, hp, b, hb, lt_of_not_ge hfar⟩

@[blueprint (title := "Cutoff-six exits do not vanish, conditional on unrestricted DFI and Chebotarev density")]
theorem nonvanishing_of_density
    (hSupply : EligiblePositiveDensity) (hDFI : DFIBoundaryScarcity) :
    ExitSixNonvanishing :=
  nonvanishing_of_quadraticRootEscape (quadraticRootEscape_of_density hSupply hDFI)

@[blueprint (title := "Unrestricted DFI plus the explicit Chebotarev specialization imply nonvanishing")]
theorem nonvanishing_of_dfi_chebotarev
    (hChebotarev : EligibleChebotarevDensity) (hDFI : DFIBoundaryScarcity) :
    ExitSixNonvanishing :=
  nonvanishing_of_density (eligiblePositiveDensity_of_chebotarev hChebotarev) hDFI

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
