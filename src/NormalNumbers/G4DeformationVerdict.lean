/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4TensorRigidity

/-!
# After the extraction, F: **the verdict on T(K′) at the implemented schedule**

`DESIGN-2026-09-15-deformation.md` §4, in the kernel.  At scale `i` of the implemented
schedule (`K = KK i`, `s = K²`, `H = (K²+1)^K` atoms, `m = kk i = K/4`, multipliers in
`[dmin i, dmax i]` with `dmax i ≤ 2·dmin i`):

* `deformation_coeff_le` — the density coefficient of the **union over any family of members
  of T(K′) with `K′ ≥ 2`**,
  `(4 dmax+1)^{3(s+1)^{K−1}} · m H dmax / (2 dmin^H)`, is at most `1/dmin^{H/2}`.
* `deformation_union_le` — hence for any such family (ℕ-valued multipliers/offsets, pairwise
  coprime, exact identities on each member's sample, cancellation of the first `K′ ≥ 2` layers),
  the positions the union reads below `L` number at most
  `L / dmin^{H/2} + (4 dmax+1)^{3(s+1)^{K−1}} · H · m`: upper density `≤ dmin^{−H/2}`.

At `i = 0`: `H > 10^1665000`, `dmin > 10^6`, so the density is below `10^{−3·10^1665000}`.
The analytic side of the verdict — that the rough-error budget forces `K′ ≥ 3K/8 ≥ 2` — is the
design's (E), documented there; this module needs only `K′ ≥ 2`.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Confine NormalNumbers.G4.Rigidity

/-- The schedule's upper bound for the multipliers at scale `i`. -/
def dmax (i : ℕ) : ℕ := gridDm (KK i) (N (KK i))

lemma d_le_dmax (i : ℕ) (α : (gridAt i).Atom) : (gridAt i).d α ≤ dmax i :=
  gridOf.d_le (KK_one_le i) α

/-- `dmax ≤ 2·dmin`, because `D₀ = K·U ≥ U`. -/
lemma dmax_le (i : ℕ) : dmax i ≤ 2 * dmin i := by
  unfold dmax gridDm dmin gridD₀
  have hK := KK_one_le i
  have : gridUmax (KK i) (N (KK i)) ≤ KK i * gridUmax (KK i) (N (KK i)) :=
    Nat.le_mul_of_pos_left _ hK
  nlinarith

lemma nine_le_dmin (i : ℕ) : 9 ≤ dmin i := by
  unfold dmin
  have hQ := gridQ_gt (KK i) (N (KK i))
  have hK := KK_ge i
  have hD : 1 ≤ gridD₀ (KK i) (N (KK i)) := by
    unfold gridD₀ gridUmax
    have h1 := pow_le_gridSum (gridB (KK i) (N (KK i))) (KK_one_le i)
    have h2 : 1 ≤ gridB (KK i) (N (KK i)) ^ KK i := Nat.one_le_pow _ _ (by unfold gridB; omega)
    have hS : 1 ≤ gridSum (KK i) (gridB (KK i) (N (KK i))) := le_trans h2 h1
    show 0 < KK i * (KK i ^ 2 * gridSum (KK i) (gridB (KK i) (N (KK i))))
    exact Nat.mul_pos (by omega) (Nat.mul_pos (by positivity) (by omega))
  nlinarith

/-- The exponent inequality behind the verdict: `6E + 2 + H/2 ≤ H` with `H = (s+1)·E`. -/
lemma exponent_ineq (i : ℕ) :
    6 * (KK i ^ 2 + 1) ^ (KK i - 1) + 2 + (KK i ^ 2 + 1) ^ KK i / 2 ≤ (KK i ^ 2 + 1) ^ KK i := by
  have hK := KK_ge i
  set E := (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  have hH : (KK i ^ 2 + 1) ^ KK i = (KK i ^ 2 + 1) * E := by
    rw [hE, ← pow_succ']; congr 1; omega
  have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by positivity)
  have hs : 24 ≤ KK i ^ 2 + 1 := by nlinarith
  rw [hH]
  have : 24 * E ≤ (KK i ^ 2 + 1) * E := Nat.mul_le_mul_right _ hs
  omega

/-- **The density coefficient of the union over T(K′), `K′ ≥ 2`, is below `dmin^{−H/2}`.** -/
theorem deformation_coeff_le (i : ℕ) :
    ((4 * dmax i + 1 : ℕ) : ℝ) ^ (3 * (KK i ^ 2 + 1) ^ (KK i - 1))
        * ((kk i : ℝ) * ((KK i ^ 2 + 1) ^ KK i : ℕ) * dmax i)
        / (2 * (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i))
      ≤ 1 / (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i / 2) := by
  set E := (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set D := dmin i with hD
  set Dm := dmax i with hDm
  have h9 : 9 ≤ D := nine_le_dmin i
  have hDm2 : Dm ≤ 2 * D := dmax_le i
  have hkey : 8 * (H * kk i) ≤ 2 * D := by
    have := key_size i
    have h8 : (8 : ℕ) ≤ 2 ^ (i + 3) := by
      have : (2 : ℕ) ^ 3 ≤ 2 ^ (i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    calc 8 * (H * kk i) ≤ 2 ^ (i + 3) * (H * kk i) := Nat.mul_le_mul_right _ h8
      _ ≤ 2 * D := this
  -- (a) `4 Dm + 1 ≤ D²`
  have ha : ((4 * Dm + 1 : ℕ) : ℝ) ≤ (D : ℝ) ^ 2 := by
    have : 4 * Dm + 1 ≤ D ^ 2 := by nlinarith
    exact_mod_cast this
  -- (b) `m H Dm ≤ D²`
  have hb : (kk i : ℝ) * (H : ℕ) * Dm ≤ (D : ℝ) ^ 2 := by
    have : kk i * H * Dm ≤ D ^ 2 := by nlinarith
    exact_mod_cast this
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hpowH : (0 : ℝ) < (D : ℝ) ^ H := by positivity
  have hpowH2 : (0 : ℝ) < (D : ℝ) ^ (H / 2) := by positivity
  have hDm0 : (0 : ℝ) ≤ ((4 * Dm + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- numerator bound
  have hnum : ((4 * Dm + 1 : ℕ) : ℝ) ^ (3 * E) * ((kk i : ℝ) * (H : ℕ) * Dm)
      ≤ (D : ℝ) ^ (6 * E + 2) := by
    calc ((4 * Dm + 1 : ℕ) : ℝ) ^ (3 * E) * ((kk i : ℝ) * (H : ℕ) * Dm)
        ≤ ((D : ℝ) ^ 2) ^ (3 * E) * (D : ℝ) ^ 2 := by
          gcongr
      _ = (D : ℝ) ^ (6 * E + 2) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  -- exponent comparison
  have hexp : (D : ℝ) ^ (6 * E + 2) * (D : ℝ) ^ (H / 2) ≤ (D : ℝ) ^ H := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hD1 (by have := exponent_ineq i; omega)
  rw [div_le_div_iff₀ (by positivity) hpowH2]
  calc ((4 * Dm + 1 : ℕ) : ℝ) ^ (3 * E) * ((kk i : ℝ) * (H : ℕ) * Dm) * (D : ℝ) ^ (H / 2)
      ≤ (D : ℝ) ^ (6 * E + 2) * (D : ℝ) ^ (H / 2) := by gcongr
    _ ≤ (D : ℝ) ^ H := hexp
    _ ≤ 1 * (2 * (D : ℝ) ^ H) := by linarith

/-- **The verdict on T(K′) at the schedule.**  Any family of members of the deformation with
`K′ ≥ 2` cancelled layers — ℕ-valued multipliers in `[dmin, dmax]` and offsets `≤ dmax`,
pairwise coprime, each member with its own sample satisfying the exact identities — reads,
below `L`, at most `L / dmin^{H/2} + (4 dmax+1)^{3(s+1)^{K−1}} · H · m` positions. -/
theorem deformation_union_le (i : ℕ) {K' : ℕ} (h2 : 2 ≤ K') (hK' : K' ≤ KK i)
    {κ : Type*} [DecidableEq κ] (𝓕 : Finset κ)
    (d t : κ → (gridAt i).Atom → ℕ) (P : κ → Finset ℕ)
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (hcancel : ∀ ν ∈ 𝓕, CoordCancelUpTo K' (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ)))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin i ≤ d ν α ∧ d ν α ≤ dmax i)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax i)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ n ∈ P ν, ∀ α, n % d ν α = t ν α)
    (U : ℕ → Prop) [DecidablePred U] {L : ℕ}
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ n ∈ P ν, ∃ α, ∃ h < kk i,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i / 2)
        + ((4 * dmax i + 1 : ℕ) : ℝ) ^ (3 * (KK i ^ 2 + 1) ^ (KK i - 1))
            * (((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i) := by
  classical
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set E := (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  -- the family size, via the image in the ℤ-valued pairs
  have hcardF : 𝓕.card ≤ (4 * dmax i + 1) ^ (3 * E) := by
    set 𝓕' := 𝓕.image (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) with h𝓕'
    have hc : 𝓕.card = 𝓕'.card := (Finset.card_image_of_injOn hinj).symm
    rw [hc]
    have h1 := card_family_le (K := KK i) (s := KK i ^ 2) (K' := K') (M := dmax i) hK' 𝓕'
      (by
        intro p hp
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        exact hcancel ν hν)
      (by
        intro p hp α
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        constructor
        · show |((d ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast (hd ν hν α).2
        · show |((t ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast ht ν hν α)
    refine le_trans h1 (Nat.pow_le_pow_right (by omega) ?_)
    have := family_exponent_le (K := KK i) (s := KK i ^ 2) hK' h2
      (by have := KK_ge i; nlinarith)
    exact this
  -- the union bound
  have hU := union_card_le (ι := (gridAt i).Atom) 𝓕 d t P (dmin_pos i) hd hcop hP U hcov
  rw [card_Atom_gridAt] at hU
  have hcoef := deformation_coeff_le i
  set F : ℝ := ((4 * dmax i + 1 : ℕ) : ℝ) ^ (3 * E) with hF
  have hF' : (𝓕.card : ℝ) ≤ F := by rw [hF]; exact_mod_cast hcardF
  have hF0 : (0 : ℝ) ≤ F := by positivity
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hHm : (0 : ℝ) ≤ ((H : ℕ) : ℝ) * kk i := by positivity
  have hpos : (0 : ℝ) ≤ (L : ℝ) * kk i * (H : ℕ) * dmax i / (2 * (dmin i : ℝ) ^ H)
      + (H : ℕ) * kk i := by positivity
  calc (((Finset.range L).filter U).card : ℝ)
      ≤ 𝓕.card * ((L : ℝ) * kk i * (H : ℕ) * dmax i / (2 * (dmin i : ℝ) ^ H) + (H : ℕ) * kk i) :=
        hU
    _ ≤ F * ((L : ℝ) * kk i * (H : ℕ) * dmax i / (2 * (dmin i : ℝ) ^ H) + (H : ℕ) * kk i) :=
        mul_le_mul_of_nonneg_right hF' hpos
    _ = (L : ℝ) * (F * ((kk i : ℝ) * (H : ℕ) * dmax i) / (2 * (dmin i : ℝ) ^ H))
          + F * ((H : ℕ) * kk i) := by ring
    _ ≤ (L : ℝ) * (1 / (dmin i : ℝ) ^ (H / 2)) + F * ((H : ℕ) * kk i) := by
        gcongr
    _ = (L : ℝ) / (dmin i : ℝ) ^ (H / 2) + F * ((H : ℕ) * kk i) := by ring

end NormalNumbers.G4.Sched
