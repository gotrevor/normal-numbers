/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Progression

/-!
# G4 disjunctivity: the concrete frame, and `PropA` discharged

The wiring of `G4Wiring.lean` indexes rows by `Fin r` and atoms by `Fin H`; the grid of
`G4Grid.lean` indexes rows by `Fin K → Fin s` and atoms by `Fin K → Fin (s+1)`.  This module
builds the reindexing equivalences (`GridParams.rowEquiv`, `GridParams.atomEquiv`, with
`r = s^K` and `H = (s+1)^K` on the nose) and assembles

  `gridFrame G X sm γ η ε D : Frame`,

the frame of draft §§2–3: `A = D_s^{⊗K}` reindexed, `d = mult`, `t = offset`,
`P = {n < X : n ≡ b₀ (P₀)}`, `θ` the transport translate at the frozen residue `c = 0`, and
`S = Sval sm shiftAL` reindexed.  The translates `γ`, the resolution `η`, the tube fraction `ε`
and the Jackson degree `D` stay parameters: `PropA` does not see them (`γ` cancels between
`Ffull` and `image`) and `PropC` does not see `γ, η, ε`.

## Proved here

* **`gridFrame_propA`** — `PropA` for the concrete frame, unconditionally.  This is the first
  of the five named inputs of `G4Wiring` to be discharged: `Frame.propA_of_progression` applied
  with the frozen residue `c = 0`, whose hypothesis is exactly `GridParams.exists_mult_mul`.
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

namespace GridParams

variable (G : GridParams)

/-! ### The reindexing -/

/-- `r = s^K`, the number of rows. -/
def rDim : ℕ := G.s ^ G.K

/-- `H = (s+1)^K`, the number of atoms. -/
def hDim : ℕ := (G.s + 1) ^ G.K

lemma card_row : Fintype.card (Fin G.K → Fin G.s) = G.rDim := by
  simp [rDim]

lemma card_atom : Fintype.card G.Atom = G.hDim := by
  simp [hDim, Atom]

/-- `(Fin K → Fin s) ≃ Fin r`. -/
noncomputable def rowEquiv : (Fin G.K → Fin G.s) ≃ Fin G.rDim :=
  Fintype.equivFinOfCardEq G.card_row

/-- `Atom ≃ Fin H`. -/
noncomputable def atomEquiv : G.Atom ≃ Fin G.hDim :=
  Fintype.equivFinOfCardEq G.card_atom

/-- The reindexed tensor matrix `A = D_s^{⊗K}`. -/
noncomputable def Amat : Matrix (Fin G.rDim) (Fin G.hDim) ℤ :=
  fun ν α => kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) (G.atomEquiv.symm α)

end GridParams

/-! ### The frame -/

open GridParams in
/-- **The concrete frame** of draft §§2–3, at outer scale `X`.  `sm` is the set of small primes
kept in the vector `S`, `γ` the frozen-prime translate, `η` the resolution, `ε` the tube
fraction and `D` the Jackson degree; those four are parameters because neither `PropA` nor
`PropC` constrains them. -/
noncomputable def gridFrame (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) : Frame where
  bse := bb
  hbse := hbb
  K := G.K
  J := G.K + G.N
  r := G.rDim
  H := G.hDim
  A := G.Amat
  d := fun α => G.d (G.atomEquiv.symm α)
  t := fun α => G.t (G.atomEquiv.symm α)
  ht := fun α => G.t_lt_d _
  P := apSample X G.P₀ G.b₀
  hP := hne
  θ := fun ν => ((∑ α : Fin G.hDim, (G.Amat ν α : ℝ) *
    (omegaR (G.d (G.atomEquiv.symm α)) / ((bb : ℝ) - 1)
      - corrB bb (G.d (G.atomEquiv.symm α)) 0) : ℝ) :
      UnitAddCircle)
  γ := γ
  S := fun n ν => ((Sval bb sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν) : ℝ) :
    UnitAddCircle)
  η := η
  hη := hη
  ε := ε
  hε := hε
  D := D

@[simp] lemma gridFrame_r (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrame bb hbb G X hne sm γ hη hε D).r = G.rDim := rfl

@[simp] lemma gridFrame_H (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrame bb hbb G X hne sm γ hη hε D).H = G.hDim := rfl

/-! ### `PropA`, discharged -/

/-- **`PropA` for the concrete frame.**  The progression `n ≡ b₀ (P₀)` writes every sample point
as `t_α + d_α k_α` with `d_α ∣ k_α`, so every multiplier residue is frozen at `0`; the transport
translate of `c = 0` is the frame's `θ` by construction.  Draft (4.3). -/
theorem gridFrame_propA (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrame bb hbb G X hne sm γ hη hε D).PropA := by
  set fr := gridFrame bb hbb G X hne sm γ hη hε D with hfr
  refine fr.propA_of_progression 0 (fun α => (G.d_pos _).ne') rfl ?_
  intro n hn
  choose k hk1 hk2 using fun α : Fin fr.H => G.exists_mult_mul hn (G.atomEquiv.symm α)
  refine ⟨k, hk1, ?_⟩
  intro α p hp
  have hpd : p ∣ G.d (G.atomEquiv.symm α) := (Nat.mem_primeFactors.1 hp).2.1
  have : p ∣ k α := hpd.trans (hk2 α)
  simpa [Nat.ModEq] using (Nat.mod_eq_zero_of_dvd this)

/-! ### `PropC`: the reindexed character, and the uniform box bound -/

/-- The number of roots of a `shiftPhase` never exceeds the number of shifts — and in particular
does not depend on the coefficients, so the §4C error terms are uniform over the Fourier box. -/
lemma card_roots_shiftPhase_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℕ) (x : ι → ℝ)
    (p : ℕ) : ((shiftPhase ρ x p).roots.card : ℝ) ≤ Fintype.card ι := by
  have : (shiftPhase ρ x p).roots.card ≤ Fintype.card ι := by
    unfold shiftPhase
    split_ifs with h
    · have := Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := root p ρ)
      rw [Finset.card_univ] at this
      exact this
    · simp [LocalPhase.trivial]
  exact_mod_cast this

/-- The character of the concrete frame's small-prime vector, reindexed onto the grid rows. -/
lemma torusChar_gridFrame_S (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) (q : Fin G.rDim → ℤ) (n : ℕ) :
    torusChar q ((gridFrame bb hbb G X hne sm γ hη hε D).S n)
      = ∏ a : Fin G.K → Fin G.s, fourier (q (G.rowEquiv a))
          (((Sval bb sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n a : ℝ) : UnitAddCircle)) := by
  unfold torusChar
  rw [← Equiv.prod_comp G.rowEquiv
    (fun ν => fourier (q ν) ((gridFrame bb hbb G X hne sm γ hη hε D).S n ν))]
  exact Finset.prod_congr rfl fun a _ => by simp [gridFrame]

/-- The explicit uniform §4C bound: the good-prime contraction plus the four transfer errors,
with every occurrence of the root count replaced by the uniform `T = |ι| = (s+1)^K N`.  Nothing
here depends on the frequency `q`, which is what makes `PropC` a bound on the whole box. -/
noncomputable def smallPrimeBound (sm : Finset ℕ) (T R M Psz : ℕ) (lam' lam θ₀ : ℝ) : ℝ :=
  Real.exp (-∑ p ∈ sm, 4 * θ₀ / p)
    + (((sm.powerset.filter (fun T' => T'.Nonempty ∧ T'.card ≤ M)).card
          * (2 ^ M * (2 * (R : ℝ) ^ M / Psz))
        + (∏ p ∈ sm, (1 + lam' * (2 * (T : ℝ) / p))) / lam' ^ M
        + 2 * (2 * Real.exp 1 / lam) ^ M * ∏ p ∈ sm, (1 + Real.exp lam * ((T : ℝ) / p))
        + 2 * (2 * Real.exp 1 / M) ^ M * (sm.card : ℝ) ^ M
            * (2 * (R : ℝ) ^ M / Psz)))

/-- **`PropC` for the concrete frame, in base `bb`** (draft (8.1), brief §4C).  The second of
the five named inputs, discharged outright modulo the frequency-separation seed: uniformly
over every nonzero frequency in the box `‖q‖∞ ≤ D`, the sample average of the character of the
small-prime vector is at most `smallPrimeBound`, whose main term is the good-prime contraction
`exp(−4θ₀ ∑_{p ∈ sm} 1/p)`.

The small primes `sm` must be prime, at most `R`, and prime to the progression modulus `P₀`;
being prime to `P₀` is exactly what makes them good for the shifts
(`goodPrime_of_not_dvd_P₀`) and larger than `2T` (`two_mul_card_le_of_not_dvd`).  The seed
`hsep` says the retained depth reaches every frequency-depth layer of the box; base four
supplies it from `1 + ⌈log₄(2^K D)⌉ ≤ N` (`gridFrame_propC_four`). -/
theorem gridFrame_propC (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) {D : ℕ}
    (hs : ∀ p ∈ sm, p.Prime) (hsP : ∀ p ∈ sm, ¬ p ∣ G.P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ sm, p ≤ R)
    {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀)
    (hsep : ∀ q : (Fin G.K → Fin G.s) → ℤ, q ≠ 0 → (∀ a, |q a| ≤ (D : ℤ)) →
      θ₀ ≤ ∑ i : G.Idx, distZ (coeffAL bb q i) ^ 2)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    (gridFrame bb hbb G X hne sm γ hη hε D).PropC
      (smallPrimeBound sm (Fintype.card G.Idx) R M (apSample X G.P₀ G.b₀).card lam' lam θ₀) := by
  classical
  intro q hq hq0
  set ρ := shiftAL G.B G.Q G.D₀ (N := G.N) with hρ
  set q' : (Fin G.K → Fin G.s) → ℤ := fun a => q (G.rowEquiv a) with hq'
  -- the frequency is nonzero after reindexing
  have hq'0 : q' ≠ 0 := by
    intro h
    refine hq0 (funext fun ν => ?_)
    obtain ⟨a, rfl⟩ := G.rowEquiv.surjective ν
    exact congrFun h a
  have hq'D : ∀ a, |q' a| ≤ (D : ℤ) := fun a => (mem_fourierBox.1 hq) _
  -- the small primes are coprime to `P₀`, good, and larger than `2T`
  have hsP' : ∀ p ∈ sm, Nat.Coprime p G.P₀ := fun p hp =>
    ((hs p hp).coprime_iff_not_dvd).2 (hsP p hp)
  have hgood : ∀ p ∈ sm, GoodPrime ρ p := fun p hp => G.goodPrime_of_not_dvd_P₀ (hs p hp) (hsP p hp)
  have hk : ∀ p ∈ sm, 2 * Fintype.card G.Idx ≤ p := fun p hp =>
    G.two_mul_card_le_of_not_dvd (hs p hp) (hsP p hp)
  -- §4C for the concrete vector
  have key := norm_sampleAvg_torusChar_Sval_le bb X G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ hne sm hs hsP'
    hR1 hR ρ hk hgood hθ0 (hsep q' hq'0 hq'D) hM hlam' hlam
  -- the two sample averages agree termwise
  have hsame : sampleAvg (gridFrame bb hbb G X hne sm γ hη hε D).P
      (gridFrame bb hbb G X hne sm γ hη hε D).S (torusChar q)
      = sampleAvg (apSample X G.P₀ G.b₀) (fun n a => ((Sval bb sm ρ n a : ℝ) : UnitAddCircle))
          (fun y => ∏ a, fourier (q' a) (y a)) := by
    unfold sampleAvg
    congr 1
    exact Finset.sum_congr rfl fun n _ => torusChar_gridFrame_S bb hbb G X hne sm γ hη hε D q n
  rw [hsame]
  refine key.trans ?_
  -- replace the root counts by the uniform bound `T`
  unfold smallPrimeBound
  have hp0 : ∀ p ∈ sm, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hs p hp).pos
  have hprod1 : (∏ p ∈ sm, (1 + lam' * (2 * ((shiftPhase ρ (coeffAL bb q') p).roots.card : ℝ) / p)))
      ≤ ∏ p ∈ sm, (1 + lam' * (2 * (Fintype.card G.Idx : ℝ) / p)) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := hp0 p hp
      positivity
    · have hpp := hp0 p hp
      have := card_roots_shiftPhase_le ρ (coeffAL bb q') p
      have hlam'0 : (0 : ℝ) ≤ lam' := by linarith
      gcongr
  have hprod2 : (∏ p ∈ sm, (1 + Real.exp lam * (((shiftPhase ρ (coeffAL bb q') p).roots.card : ℝ) / p)))
      ≤ ∏ p ∈ sm, (1 + Real.exp lam * ((Fintype.card G.Idx : ℝ) / p)) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := hp0 p hp
      positivity
    · have hpp := hp0 p hp
      have := card_roots_shiftPhase_le ρ (coeffAL bb q') p
      gcongr
  have hlam'pos : (0 : ℝ) < lam' ^ M := by positivity
  have hc : (0 : ℝ) ≤ 2 * (2 * Real.exp 1 / lam) ^ M := by positivity
  gcongr

/-- **`PropC` in base four**: the seed `θ₀ = 4^{−4}8^{−K}` from `sum_sq_distZ_coeff_ge`, under
`1 + ⌈log₄(2^K D)⌉ ≤ N`. -/
theorem gridFrame_propC_four (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) {D : ℕ}
    (hs : ∀ p ∈ sm, p.Prime) (hsP : ∀ p ∈ sm, ¬ p ∣ G.P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ sm, p ≤ R)
    (hN : 1 + Nat.clog 4 (2 ^ G.K * D) ≤ G.N)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    (gridFrame 4 (by norm_num) G X hne sm γ hη hε D).PropC
      (smallPrimeBound sm (Fintype.card G.Idx) R M (apSample X G.P₀ G.b₀).card lam' lam
        (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ G.K)) :=
  gridFrame_propC 4 (by norm_num) G X hne sm γ hη hε hs hsP hR1 hR (by positivity)
    (fun q hq hqD => sum_sq_distZ_coeff_ge hN hq hqD) hM hlam' hlam

end NormalNumbers.G4
