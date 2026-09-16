/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Frame
import NormalNumbers.G4TransportW

/-!
# The concrete frame for a general additive weight, and `PropA`

`G4Frame.gridFrame` hard-codes the weight `ω` and the constant `primeLambertAtBase bb`.  This
module repeats the same construction over a `TWeight` `W` (`G4TransportW`), giving

  `gridFrameW W bb hbb G X hne sm γ hη hε D : Frame`

with `w = W.wN`, `x = W.lambert bb`, and the transport translate `θ` built from `W.corrB` at the
frozen residue `c = 0`.  Two facts:

* `gridFrameW_omega` — with `W = TWeight.omega` this is *definitionally* the old `gridFrame`, so
  nothing downstream of `gridFrame` has to move;
* `gridFrameW_propA` — `PropA` for the general frame, by `Frame.propA_of_progressionW`.

For campaign A the instance is `W = TWeight.subset S` and `x = subsetLambert S bb`
(`gridFrameW_subset_x`).  Note the small-prime vector field `S` of the frame is *already*
parametrized by the finset `sm` of active primes, and `ω_S` restricted to a finset of primes is
`omegaOn (sm.filter S)`: the `S`-restriction of the local layer costs no new machinery, only a
different `sm`.
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **The concrete frame with a general weight.** -/
noncomputable def gridFrameW (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) : Frame where
  bse := bb
  hbse := hbb
  w := fun m => (W.wN m : ℝ)
  x := W.lambert bb
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
    ((W.wN (G.d (G.atomEquiv.symm α)) : ℝ) / ((bb : ℝ) - 1)
      - W.corrB bb (G.d (G.atomEquiv.symm α)) 0) : ℝ) :
      UnitAddCircle)
  γ := γ
  S := fun n ν => ((Sval bb sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν) : ℝ) :
    UnitAddCircle)
  η := η
  hη := hη
  ε := ε
  hε := hε
  D := D

/-- With the weight `ω`, the general frame *is* `gridFrame`. -/
theorem gridFrameW_omega (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    gridFrameW TWeight.omega bb hbb G X hne sm γ hη hε D
      = gridFrame bb hbb G X hne sm γ hη hε D := rfl

@[simp] lemma gridFrameW_r (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ) (hne)
    (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).r = G.rDim := rfl

@[simp] lemma gridFrameW_H (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ) (hne)
    (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).H = G.hDim := rfl

/-- For the prime-subset weight the constant under test is `c_S(bb) = ∑_n ω_S(n)/bbⁿ`. -/
lemma gridFrameW_subset_x (S : ℕ → Prop) [DecidablePred S] (bb : ℕ) (hbb : 2 ≤ bb)
    (G : GridParams) (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW (TWeight.subset S) bb hbb G X hne sm γ hη hε D).x = subsetLambert S bb :=
  TWeight.lambert_subset S

/-- **`PropA` for the general-weight frame.**  Same proof as `gridFrame_propA`: the progression
`n ≡ b₀ (P₀)` freezes every multiplier residue at `0`, and the frame's `θ` is the transport
translate of `c = 0` by construction. -/
theorem gridFrameW_propA (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).PropA := by
  set fr := gridFrameW W bb hbb G X hne sm γ hη hε D with hfr
  refine fr.propA_of_progressionW W rfl rfl 0 (fun α => (G.d_pos _).ne') rfl ?_
  intro n hn
  choose k hk1 hk2 using fun α : Fin fr.H => G.exists_mult_mul hn (G.atomEquiv.symm α)
  refine ⟨k, hk1, ?_⟩
  intro α p hp
  have hpd : p ∣ G.d (G.atomEquiv.symm α) := (Nat.mem_primeFactors.1 hp).2.1
  have : p ∣ k α := hpd.trans (hk2 α)
  simpa [Nat.ModEq] using (Nat.mod_eq_zero_of_dvd this)

end NormalNumbers.G4
