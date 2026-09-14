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
noncomputable def gridFrame (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) : Frame where
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
    (omegaR (G.d (G.atomEquiv.symm α)) / 3 - corrB 4 (G.d (G.atomEquiv.symm α)) 0) : ℝ) :
      UnitAddCircle)
  γ := γ
  S := fun n ν => ((Sval sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν) : ℝ) :
    UnitAddCircle)
  η := η
  hη := hη
  ε := ε
  hε := hε
  D := D

@[simp] lemma gridFrame_r (G : GridParams) (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrame G X hne sm γ hη hε D).r = G.rDim := rfl

@[simp] lemma gridFrame_H (G : GridParams) (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrame G X hne sm γ hη hε D).H = G.hDim := rfl

/-! ### `PropA`, discharged -/

/-- **`PropA` for the concrete frame.**  The progression `n ≡ b₀ (P₀)` writes every sample point
as `t_α + d_α k_α` with `d_α ∣ k_α`, so every multiplier residue is frozen at `0`; the transport
translate of `c = 0` is the frame's `θ` by construction.  Draft (4.3). -/
theorem gridFrame_propA (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrame G X hne sm γ hη hε D).PropA := by
  set fr := gridFrame G X hne sm γ hη hε D with hfr
  refine fr.propA_of_progression 0 (fun α => (G.d_pos _).ne') rfl ?_
  intro n hn
  choose k hk1 hk2 using fun α : Fin fr.H => G.exists_mult_mul hn (G.atomEquiv.symm α)
  refine ⟨k, hk1, ?_⟩
  intro α p hp
  have hpd : p ∣ G.d (G.atomEquiv.symm α) := (Nat.mem_primeFactors.1 hp).2.1
  have : p ∣ k α := hpd.trans (hk2 α)
  simpa [Nat.ModEq] using (Nat.mod_eq_zero_of_dvd this)

end NormalNumbers.G4
