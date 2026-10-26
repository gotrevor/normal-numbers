/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffSixQuadratic

/-!
# Cutoff six: from one far root to `QuadraticRootEscape`, and the DFI gap

`QuadraticRootEscape` quantifies over *all* roots.  Since the two roots of
`x² + 64x + 4096` mod `p` are `ν` and `-64-ν`, one far root suffices
(`quadraticRootEscape_of_rootFar`).  That reduces nonvanishing to
`RestrictedRootFar`: infinitely many `p = 120t+1` with `2^(20t) ≠ 1` having a
root `ν` with `‖ν/p‖ℤ ≥ 1/4`.

`DFIWeak` is a weaker consequence of Duke–Friedlander–Iwaniec, *Equidistribution
of roots of a quadratic congruence to prime moduli*, Ann. of Math. 141 (1995),
specialised to our polynomial (discriminant `-3·64² < 0`): roots `ν/p` are
equidistributed, so in particular infinitely many primes have a root in
`‖ν/p‖ℤ ≥ 1/4`.  Transcription: faithful-or-weaker (we keep only "infinitely often
in a set of measure 1/2").  The gap to `RestrictedRootFar` is the restriction to
the Chebotarev set `{p ≡ 1 mod 120, 2 not a sixth power mod p}`; DFI's method runs
over ideals of `ℚ(√-3)` and a ray-class restriction is plausibly within it, but we
have not checked a source.  `DFIWeak` is stated, not used.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

/-- Literature (weaker form of DFI 1995), stated only. -/
def DFIWeak : Prop :=
  ∀ N, ∃ p ≥ N, Nat.Prime p ∧ ∃ b : ℤ, (p : ℤ) ∣ b^2 + 64*b + 4096 ∧
    (1/4 : ℝ) ≤ dZ ((b : ℝ) / p)

/-- DFI restricted to the Chebotarev set: the exact missing statement. -/
def RestrictedRootFar : Prop :=
  ∀ N, ∃ t ≥ N, Nat.Prime (120*t+1) ∧ (2 : ZMod (120*t+1))^(20*t) ≠ 1 ∧
    ∃ b : ℤ, ((120*t+1 : ℕ) : ℤ) ∣ b^2 + 64*b + 4096 ∧
      (1/4 : ℝ) ≤ dZ ((b : ℝ) / (120*t+1 : ℕ))

lemma dZ_le_sub (x y : ℝ) : dZ x ≤ |x - y| + dZ y := by
  unfold dZ
  calc |x - round x| ≤ |x - (round y : ℤ)| := round_le x _
    _ ≤ |x - y| + |y - round y| := by
      have := abs_sub_le x y (round y : ℝ); linarith

lemma dZ_neg (x : ℝ) : dZ (-x) = dZ x := by
  have h1 : ∀ z : ℝ, dZ (-z) ≤ dZ z := fun z => by
    unfold dZ
    calc |-z - round (-z)| ≤ |-z - ((-round z : ℤ) : ℝ)| := round_le _ _
      _ = |z - round z| := by push_cast; rw [← abs_neg]; ring_nf
  exact le_antisymm (h1 x) (by simpa using h1 (-x))

theorem quadraticRootEscape_of_rootFar (h : RestrictedRootFar) :
    QuadraticRootEscape := by
  refine ⟨1/8, by norm_num, fun N => ?_⟩
  obtain ⟨t, ht, hp, hζ, b0, hb0, hfar⟩ := h (N + 5)
  refine ⟨t, by omega, hp, hζ, fun b hb => ?_⟩
  have := Fact.mk hp
  set p := 120*t+1
  have hpR : (512 : ℝ) ≤ (p : ℕ) := by
    have : 512 ≤ p := by omega
    exact_mod_cast this
  have hp0 : (0:ℝ) < (p : ℕ) := by linarith
  have e1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb
  have e2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb0
  push_cast at e1 e2
  have hfac : ((b : ZMod p) - b0) * ((b : ZMod p) + b0 + 64) = 0 := by
    linear_combination e1 - e2
  rcases mul_eq_zero.1 hfac with h1 | h1
  · obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1
      (by rw [sub_eq_zero.1 h1] : (b0 : ZMod p) = b)
    have : (b : ℝ) / (p : ℕ) = (b0 : ℝ) / (p : ℕ) + k := by
      have hk' : (b : ℝ) = b0 + (p : ℕ) * k := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hk; push_cast at this ⊢; linarith
      rw [hk']; field_simp
    rw [this, dZ_add_int]; linarith
  · obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1
      (by push_cast; linear_combination -h1 : ((-b0 - 64 : ℤ) : ZMod p) = b)
    have : (b : ℝ) / (p : ℕ) = -((b0 : ℝ) / (p : ℕ) + 64 / (p : ℕ)) + k := by
      have hk' : (b : ℝ) = -b0 - 64 + (p : ℕ) * k := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hk; push_cast at this ⊢; linarith
      rw [hk']; field_simp; ring
    rw [this, dZ_add_int, dZ_neg]
    have hs := dZ_le_sub ((b0 : ℝ) / (p : ℕ)) ((b0 : ℝ) / (p : ℕ) + 64 / (p : ℕ))
    have h64 : 64 / ((p : ℕ) : ℝ) ≤ 1/8 := by
      rw [div_le_iff₀ hp0]; linarith
    have h64' : (0:ℝ) ≤ 64 / ((p:ℕ):ℝ) := by positivity
    rw [show (b0 : ℝ) / (p : ℕ) - ((b0 : ℝ) / (p : ℕ) + 64 / (p : ℕ)) = -(64 / (p:ℕ)) by ring,
      abs_neg, abs_of_nonneg h64'] at hs
    linarith

theorem nonvanishing_of_restrictedRootFar (h : RestrictedRootFar) :
    ExitSixNonvanishing :=
  nonvanishing_of_quadraticRootEscape (quadraticRootEscape_of_rootFar h)

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
