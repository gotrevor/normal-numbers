import NormalNumbers.ElliottCharRigidity
import NormalNumbers.G4MertensAP

/-!
# T3: `ElliottCharRigidity.PrimeDensityAP` from the in-repo Mertens-in-progressions

`PrimeDensityAP A` asks for `c > 0` and `B` with
`c·primeMass X − B ≤ primeClassMass q a X` for every `0 < q ≤ A`, every unit `a : ZMod q` and
**every** `X`.

**EP-1 provenance** (searched before anything was stated):
(i) `src/PNTPort/` — nothing about progressions;
(ii) `src/NormalNumbers/G4MertensAP.lean` — **HIT**: `mertensRate_residueClass` gives
     `∃ c C, MertensRate (· ≡ a [q]) c C`, i.e. `c·log log N − C ≤ ∑_{p<N, p≡a} 1/p` for `N ≥ 2`,
     assembled from mathlib's `LSeries/PrimesInAP` + Chebyshev + two partial summations;
     `Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le` gives the matching two-sided
     bound `|primeMass X − log log X| ≤ mertensBound` for `X ≥ 2`;
(iii) mathlib — `Nat.setOf_prime_and_eq_mod_infinite` and friends are qualitative only.

**EA-1 boundary audit, done before writing any Lean.**  Both sides at every extreme:
* `X ≤ 1`: `primeMass X = primeClassMass q a X = 0`, so the claim is `−B ≤ 0`. True for `B ≥ 0`.
* `2 ≤ X < 16` (where `log log X < 0`): `primeMass` is bounded by an absolute constant, absorbed
  by `B`. True.
* `X → ∞`: LHS `≍ c·log log X`, RHS `≍ (1/φ(q))·log log X`.  Needs `c ≤ 1/φ(q)` for every `q ≤ A`
  — available since there are only finitely many such `q`, and each contributes a positive rate.
  True; **and this is the only place uniformity in `q` is used**, which is why `A` is a parameter.
* `q = 1`: `ZMod 1` is trivial, `a = 0` is a unit, and `primeClassMass 1 a X = primeMass X`, so the
  claim is `c·primeMass X − B ≤ primeMass X`. True for `c ≤ 1`.
* `A = 0`: no `q` satisfies `0 < q ≤ 0`; vacuous. True.

No exponent is load-bearing here, unlike the `Prop` lap 92 refuted.
-/

open Finset

namespace NormalNumbers.ElliottPrimeDensityAP

open NormalNumbers.ElliottCharRigidity NormalNumbers.G4.MertensAP
open Erdos67b Erdos67b.PrimeEstimates

noncomputable section

/-! ### Bridges between the three prime-set spellings -/

/-- `primesUpTo X` (primes `≤ X`, `Erdos67b.Pretentious`) is `Nat.primesLE X` (mathlib). -/
theorem primesUpTo_eq_primesLE (X : ℕ) : primesUpTo X = Nat.primesLE X := by
  ext p
  rw [mem_primesUpTo, Nat.mem_primesLE]
  exact and_comm

/-- `primesUpTo X` is `Nat.primesBelow (X+1)`. -/
theorem primesUpTo_eq_primesBelow_succ (X : ℕ) : primesUpTo X = Nat.primesBelow (X + 1) := by
  ext p
  rw [mem_primesUpTo, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, hle⟩; exact ⟨by omega, hp⟩
  · rintro ⟨hlt, hp⟩; exact ⟨hp, by omega⟩

/-- `primeMass` is `Erdos67b.PrimeEstimates.primeReciprocals`. -/
theorem primeMass_eq_primeReciprocals (X : ℕ) :
    NormalNumbers.ElliottZetaOmegaPretentious.primeMass X = primeReciprocals X := by
  rw [NormalNumbers.ElliottZetaOmegaPretentious.primeMass, primesUpTo_eq_primesLE]
  rfl

/-- `primeClassMass` is `sumInvPrimesIn` of the residue-class predicate, at `N = X + 1`. -/
theorem primeClassMass_eq_sumInvPrimesIn (q : ℕ) (a : ZMod q) (X : ℕ) :
    primeClassMass q a X
      = sumInvPrimesIn (fun p : ℕ => (p : ZMod q) = a) (X + 1) := by
  classical
  rw [primeClassMass, sumInvPrimesIn, primesUpTo_eq_primesBelow_succ]

/-! ### Uniformising finitely many `(c, B)` pairs -/

/-- Finitely many statements of the shape "`∃ c > 0, ∃ B ≥ 0, P c B`", each monotone in `c`
(downward) and `B` (upward), admit one common `(c, B)`.  Used twice: once over the units `a` of a
fixed modulus, once over the moduli `q ≤ A`. -/
theorem exists_uniform {ι : Type*} (s : Finset ι) (P : ι → ℝ → ℝ → Prop)
    (hmono : ∀ i, ∀ {c c' B B' : ℝ}, 0 < c' → c' ≤ c → B ≤ B' → P i c B → P i c' B')
    (h : ∀ i ∈ s, ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 ≤ B ∧ P i c B) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ i ∈ s, P i c B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 0, le_rfl, by simp⟩
  | insert i t hit ih =>
      obtain ⟨c₀, hc₀, B₀, hB₀, hP₀⟩ := h i (Finset.mem_insert_self i t)
      obtain ⟨c₁, hc₁, B₁, hB₁, hP₁⟩ :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      refine ⟨min c₀ c₁, lt_min hc₀ hc₁, max B₀ B₁, le_trans hB₀ (le_max_left _ _), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjt
      · exact hmono j (lt_min hc₀ hc₁) (min_le_left _ _) (le_max_left _ _) hP₀
      · exact hmono j (lt_min hc₀ hc₁) (min_le_right _ _) (le_max_right _ _) (hP₁ j hjt)

/-! ### One residue class -/

/-- **The bound for a single unit class.**  `c·primeMass X − B ≤ primeClassMass q a X` for every
`X`, with `c` the Mertens rate of that class and `B` absorbing both the Mertens constant and the
small-`X` range. -/
theorem exists_class_bound {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ,
      c * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B
        ≤ primeClassMass q a X := by
  classical
  obtain ⟨c, C, hc, hrate⟩ := mertensRate_residueClass ha
  refine ⟨c, hc, max 0 (C + c * mertensBound), le_max_left _ _, ?_⟩
  intro X
  have hmassnn : 0 ≤ NormalNumbers.ElliottZetaOmegaPretentious.primeMass X := by
    rw [NormalNumbers.ElliottZetaOmegaPretentious.primeMass]
    exact Finset.sum_nonneg fun p _ => by positivity
  have hclassnn : 0 ≤ primeClassMass q a X := by
    rw [primeClassMass]
    exact Finset.sum_nonneg fun p _ => by positivity
  rcases lt_or_ge X 2 with hsmall | hX
  · -- `X ≤ 1`: no primes at all, both masses vanish
    have hzero : NormalNumbers.ElliottZetaOmegaPretentious.primeMass X = 0 := by
      rw [NormalNumbers.ElliottZetaOmegaPretentious.primeMass]
      refine Finset.sum_eq_zero ?_
      intro p hp
      have := (mem_primesUpTo.mp hp)
      have hp2 := this.1.two_le
      omega
    rw [hzero, mul_zero, zero_sub]
    have : (0:ℝ) ≤ max 0 (C + c * mertensBound) := le_max_left _ _
    linarith
  · -- `X ≥ 2`: Mertens for the class against Mertens for all primes
    have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
    have hlogmono : Real.log (Real.log (X : ℝ)) ≤ Real.log (Real.log ((X + 1 : ℕ) : ℝ)) := by
      refine Real.log_le_log hlogX ?_
      refine Real.log_le_log (by linarith) ?_
      push_cast
      linarith
    have hclass := hrate (X + 1) (by omega)
    rw [← primeClassMass_eq_sumInvPrimesIn] at hclass
    have hmass := abs_primeReciprocals_sub_log_log_le hX
    rw [abs_le] at hmass
    have hupper : NormalNumbers.ElliottZetaOmegaPretentious.primeMass X
        ≤ Real.log (Real.log (X : ℝ)) + mertensBound := by
      rw [primeMass_eq_primeReciprocals]
      linarith [hmass.2]
    have hstep : c * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X
        ≤ c * (Real.log (Real.log (X : ℝ)) + mertensBound) :=
      mul_le_mul_of_nonneg_left hupper hc.le
    have hmax : C + c * mertensBound ≤ max 0 (C + c * mertensBound) := le_max_right _ _
    nlinarith [hclass, hlogmono, hc.le]

/-! ### Uniformly over the units of one modulus, then over the moduli -/

/-- Uniform over the unit classes of a fixed modulus `q > 0`. -/
theorem exists_modulus_bound {q : ℕ} (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ZMod q, IsUnit a → ∀ X : ℕ,
      c * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B
        ≤ primeClassMass q a X := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  have hmono : ∀ a : ZMod q, ∀ {c c' B B' : ℝ}, 0 < c' → c' ≤ c → B ≤ B' →
      (∀ X : ℕ, c * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B
          ≤ primeClassMass q a X) →
      (∀ X : ℕ, c' * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B'
          ≤ primeClassMass q a X) := by
    intro a c c' B B' _ hcc hBB hP X
    have hmassnn : 0 ≤ NormalNumbers.ElliottZetaOmegaPretentious.primeMass X := by
      rw [NormalNumbers.ElliottZetaOmegaPretentious.primeMass]
      exact Finset.sum_nonneg fun p _ => by positivity
    have := hP X
    nlinarith
  have hex : ∀ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
      ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ,
        c * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B
          ≤ primeClassMass q a X := by
    intro a ha
    exact exists_class_bound (Finset.mem_filter.mp ha).2
  obtain ⟨c, hc, B, hB, hall⟩ :=
    exists_uniform (Finset.univ.filter (fun a : ZMod q => IsUnit a)) _ hmono hex
  refine ⟨c, hc, B, hB, fun a hau X => hall a ?_ X⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hau⟩

/-- **T3: `PrimeDensityAP` IS A THEOREM.**  The last non-cited input of the Elliott consumer.

`c` is the minimum of the finitely many per-class Mertens rates for moduli `q ≤ A`, and `B` the
maximum of the corresponding constants; the minimum is over a `Finset`, so it is positive. -/
theorem exists_primeDensityAP (A : ℕ) : PrimeDensityAP A := by
  classical
  have hmono : ∀ q : ℕ, ∀ {c c' B B' : ℝ}, 0 < c' → c' ≤ c → B ≤ B' →
      (∀ a : ZMod q, IsUnit a → ∀ X : ℕ,
        c * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B ≤ primeClassMass q a X) →
      (∀ a : ZMod q, IsUnit a → ∀ X : ℕ,
        c' * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B'
          ≤ primeClassMass q a X) := by
    intro q c c' B B' _ hcc hBB hP a hau X
    have hmassnn : 0 ≤ NormalNumbers.ElliottZetaOmegaPretentious.primeMass X := by
      rw [NormalNumbers.ElliottZetaOmegaPretentious.primeMass]
      exact Finset.sum_nonneg fun p _ => by positivity
    have := hP a hau X
    nlinarith
  have hex : ∀ q ∈ Finset.Icc 1 A, ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ a : ZMod q, IsUnit a → ∀ X : ℕ,
        c * NormalNumbers.ElliottZetaOmegaPretentious.primeMass X - B
          ≤ primeClassMass q a X := by
    intro q hq
    exact exists_modulus_bound (Finset.mem_Icc.mp hq).1
  obtain ⟨c, hc, B, hB, hall⟩ := exists_uniform (Finset.Icc 1 A) _ hmono hex
  refine ⟨c, hc, B, ?_⟩
  intro q hq hqA a hau X
  exact hall q (Finset.mem_Icc.mpr ⟨hq, hqA⟩) a hau X

end

end NormalNumbers.ElliottPrimeDensityAP
