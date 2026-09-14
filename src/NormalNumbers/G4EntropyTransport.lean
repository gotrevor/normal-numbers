/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Frame
import NormalNumbers.G4EntropyCover

/-!
# Entropy expedition §3A: keep the **exact** transported sample

`gridFrame_propA` concludes `Ffull n ∈ image`, i.e. *some* atom vector in the orbit closure
transports to `Ffull n`.  That is all disjunctivity needs, and it is exactly what an entropy
argument cannot use: the whole point is *which* orbit point sits at each atom.

The existing proof already produces the witness explicitly — it is
`x α = orbit bse (G_bse) (k α)` for the frozen orbit indices `k α` — inside
`Frame.propA_of_progression`, immediately before the `∃` weakens it.  This module exposes that
as an **equation** (`Ffull_eq_of_progression`), leaving `G4Transport.lean` and `G4Frame.lean`
untouched and recovering `PropA` from it (`propA_of_Ffull_eq`).

Then the chain to the joint boxes is closed:

* `uSample_eq_orbit`   : the entropy sample `u^x_{K,α}(n) = {4^{k} x}` *is* `orbit 4 x k`;
* `orbit_mem_dyadicArc`: `ZSample = j` pins `orbit` to the closed dyadic arc `[j·2^{-m},
  (j+1)·2^{-m}]` — closed, so endpoint-safe;
* `Ffull_mem_imageOfSet_boxUnion` : if the joint quantized vector of `n` is one of the members
  of a collection `ℬ`, then `Ffull n` lies in `imageOfSet (boxUnion 𝓑 2^{-m})`, where `𝓑` is
  the centre collection of `ℬ`, of the same cardinality.

That is precisely the hypothesis `∀ n ∈ Good, Ffull n ∈ E` of `Frame.capture_le`, with the `E`
whose tube volume `volume_tube_le_joint` bounds by `|ℬ|·η^{|G|}·vol(pieceCube)`.  The three
pieces (C), (G), §3A therefore compose.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4
open NormalNumbers.PrimeLambert

/-! ### §3A: the exact transported vector -/

variable (fr : NormalNumbers.G4.Frame)

/-- **The exact transported sample** (brief §3A).  On the progression, `Ffull n` is not merely
*in* the image: it is the transport of the explicit atom vector `α ↦ orbit bse x (k α)`.  This
is the identity inside `coe_sum_dilatedTailB`/`propA_of_progression`, exposed. -/
theorem Ffull_eq_of_progression (hw : fr.w = omegaR) (hx : fr.x = primeLambertAtBase fr.bse)
    (c k : Fin fr.H → ℕ) (hd : ∀ α, fr.d α ≠ 0) (hθ : fr.θ = fr.transportTheta c)
    {n : ℕ} (hnk : ∀ α, n = fr.t α + fr.d α * k α)
    (hk : ∀ α, ∀ p ∈ (fr.d α).primeFactors, k α ≡ c α [MOD p]) :
    fr.Ffull n
      = mulVecT fr.A
          (fun α => ((orbit fr.bse (primeLambertAtBase fr.bse) (k α) : ℝ) : UnitAddCircle))
        + fr.θ - fr.γ := by
  funext ν
  unfold NormalNumbers.G4.Frame.Ffull
  rw [hw]
  have hsum : (∑ α, (fr.A ν α : ℝ)
        * ∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (fr.bse : ℝ) ^ (j + 1))
      = ∑ α, (fr.A ν α : ℝ) * dilatedTailB fr.bse (fr.d α) (k α) :=
    Finset.sum_congr rfl fun α _ => by rw [hnk α, fr.tsum_eq_dilatedTailB]
  rw [hsum, fr.coe_sum_dilatedTailB c k hd hk ν, hθ]
  simp only [Pi.add_apply, Pi.sub_apply]

/-- `PropA` recovered from the exact identity: the old endpoint is an instance. -/
theorem propA_of_Ffull_eq (hw : fr.w = omegaR) (hx : fr.x = primeLambertAtBase fr.bse)
    (c : Fin fr.H → ℕ) (hd : ∀ α, fr.d α ≠ 0) (hθ : fr.θ = fr.transportTheta c)
    (hP : ∀ n ∈ fr.P, ∃ k : Fin fr.H → ℕ, (∀ α, n = fr.t α + fr.d α * k α) ∧
      ∀ α, ∀ p ∈ (fr.d α).primeFactors, k α ≡ c α [MOD p]) :
    fr.PropA := by
  intro n hn
  obtain ⟨k, hnk, hk⟩ := hP n hn
  refine ⟨fun α => ((orbit fr.bse (primeLambertAtBase fr.bse) (k α) : ℝ) : UnitAddCircle),
    fun α => by rw [hx]; exact subset_closure (Set.mem_range_self _), ?_⟩
  exact Ffull_eq_of_progression fr hw hx c k hd hθ hnk hk


/-! ### The quantized sample pins a closed dyadic arc -/

/-- The entropy sample is the base-four orbit point at the frozen index. -/
lemma uSample_eq_orbit (G : NormalNumbers.G4.GridParams) (x : ℝ) (n : ℕ) (α : G.Atom) :
    uSample G x n α = orbit 4 x (kIdx G n α) := by
  unfold uSample orbit
  rw [mul_comm]
  norm_num

/-- **Quantization pins a closed arc.**  `ZSample = j` forces the orbit point into
`[j·2^{-m}, (j+1)·2^{-m}]`.  The arc is closed, which is what keeps dyadic endpoints safe. -/
lemma orbit_mem_dyadicArc (G : NormalNumbers.G4.GridParams) (m : ℕ) (x : ℝ) (n : ℕ)
    (α : G.Atom) :
    orbit 4 x (kIdx G n α) ∈
      Set.Icc ((ZSample G m x n α : ℝ) / 2 ^ m)
        ((ZSample G m x n α : ℝ) / 2 ^ m + (2 : ℝ)⁻¹ ^ m) := by
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have hu0 : (0 : ℝ) ≤ uSample G x n α := Int.fract_nonneg _
  have hfl : (ZSample G m x n α : ℝ) ≤ 2 ^ m * uSample G x n α := by
    have := Nat.floor_le (a := (2 : ℝ) ^ m * uSample G x n α) (by positivity)
    simpa [ZSample] using this
  have hfl2 : (2 : ℝ) ^ m * uSample G x n α < (ZSample G m x n α : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (a := (2 : ℝ) ^ m * uSample G x n α)
    simpa [ZSample] using this
  rw [← uSample_eq_orbit]
  constructor
  · rw [div_le_iff₀ hpos]
    linarith [hfl]
  · have hrw : (ZSample G m x n α : ℝ) / 2 ^ m + (2 : ℝ)⁻¹ ^ m
        = ((ZSample G m x n α : ℝ) + 1) / 2 ^ m := by
      rw [inv_pow]
      field_simp
    rw [hrw, le_div_iff₀ hpos]
    linarith [hfl2]

/-! ### The bridge: quantized sample ⟹ membership in the transported joint box -/

/-- The centre of the joint box selected by the quantized sample at scale `m`. -/
noncomputable def sampleCentre (G : NormalNumbers.G4.GridParams) (m : ℕ) (x : ℝ) (n : ℕ) :
    Fin G.hDim → ℝ :=
  fun α => (ZSample G m x n (G.atomEquiv.symm α) : ℝ) / 2 ^ m

/-- **§3A ⟹ §3B, on the concrete frame.**  If the joint quantized sample of `n` selects a centre
belonging to `𝓑`, then the exact transported vector `Ffull n` lies in the transported union of
the joint boxes of `𝓑` — the set whose tube volume `volume_tube_le_joint` bounds by `|𝓑|`.

This is the hypothesis `∀ n ∈ Good, Ffull n ∈ E` of `Frame.capture_le`. -/
theorem gridFrame_Ffull_mem_boxUnion (G : NormalNumbers.G4.GridParams) (X : ℕ)
    (hbb : (2 : ℕ) ≤ 4)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D m : ℕ) (𝓑 : Finset (Fin G.hDim → ℝ))
    {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (hmem : sampleCentre G m (primeLambertAtBase 4) n ∈ 𝓑) :
    (gridFrame 4 hbb G X hne sm γ hη hε D).Ffull n
      ∈ imageOfSet (gridFrame 4 hbb G X hne sm γ hη hε D)
          (boxUnion (gridFrame 4 hbb G X hne sm γ hη hε D) 𝓑 ((2 : ℝ)⁻¹ ^ m)) := by
  set fr := gridFrame 4 hbb G X hne sm γ hη hε D with hfr
  set k : Fin G.hDim → ℕ := fun α => kIdx G n (G.atomEquiv.symm α) with hkdef
  have hspec : ∀ α : Fin G.hDim,
      n = G.t (G.atomEquiv.symm α) + G.d (G.atomEquiv.symm α) * k α
        ∧ G.d (G.atomEquiv.symm α) ∣ k α :=
    fun α => kIdx_spec G hn (G.atomEquiv.symm α)
  have hnk : ∀ α, n = fr.t α + fr.d α * k α := fun α => (hspec α).1
  have hd : ∀ α, fr.d α ≠ 0 := fun α => (G.d_pos _).ne'
  have hk : ∀ α, ∀ p ∈ (fr.d α).primeFactors, k α ≡ (0 : Fin G.hDim → ℕ) α [MOD p] := by
    intro α p hp
    have hpd : p ∣ G.d (G.atomEquiv.symm α) := (Nat.mem_primeFactors.1 hp).2.1
    have hdvd : p ∣ k α := hpd.trans (hspec α).2
    show k α ≡ 0 [MOD p]
    simpa [Nat.ModEq] using (Nat.mod_eq_zero_of_dvd hdvd)
  have heq := Ffull_eq_of_progression fr rfl rfl 0 k hd rfl hnk hk
  rw [heq]
  refine mem_imageOfSet fr ?_
  refine Set.mem_biUnion hmem ?_
  intro α _
  refine ⟨orbit 4 (primeLambertAtBase 4) (k α), ?_, rfl⟩
  have := orbit_mem_dyadicArc G m (primeLambertAtBase 4) n (G.atomEquiv.symm α)
  exact this

end NormalNumbers.G4Entropy
