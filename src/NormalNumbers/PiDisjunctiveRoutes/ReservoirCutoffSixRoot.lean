/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffSixVanishing

/-!
# Cutoff six: the escape node is a pure cube-root distribution statement

`CubicRootEscape` mentions the specific residue `2^(20m+18)` mod `p = 120m+89`.
Since `p ≡ 2 (mod 3)`, cubing is a bijection of `ZMod p`, so this residue is
the *unique* cube root of `1024 = 8³·2` mod `p`.  We prove
`cubicRootEscape_iff`: the node is equivalent to `CubeRootEscape`, which only
asks that the cube roots of `1024` modulo infinitely many primes `p ≡ 89 (mod 120)`
stay `ε·p` away from `0`.  This is a statement of Hooley type (distribution of
roots of the irreducible cubic `x³ − 2` to prime moduli), open as far as we know:
equidistribution is proved for quadratics (Duke–Friedlander–Iwaniec, Tóth) but
not for cubics to prime moduli.  Reformulation, not a proof.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

/-- Cube roots of `1024` mod `p = 120m+89` stay away from `0` infinitely often. -/
def CubeRootEscape : Prop :=
  ∃ ε > 0, ∀ N, ∃ m ≥ N, Nat.Prime (120*m+89) ∧
    ∀ b : ℤ, ((120*m+89 : ℕ) : ℤ) ∣ b^3 - 1024 →
      ε ≤ dZ ((b : ℝ) / (120*m+89 : ℕ))

lemma dZ_add_int (x : ℝ) (k : ℤ) : dZ (x + k) = dZ x := by
  unfold dZ; rw [round_add_intCast]; push_cast; ring_nf

/-- Cubing is injective mod `p = 120m+89`: `x = (x³)^(80m+59)`. -/
lemma cube_inj (m : ℕ) (hp : Nat.Prime (120*m+89)) (x y : ZMod (120*m+89))
    (h : x^3 = y^3) : x = y := by
  have := Fact.mk hp
  have key : ∀ z : ZMod (120*m+89), z = (z^3)^(80*m+59) := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp
    · have hf := ZMod.pow_card_sub_one_eq_one hz
      rw [show 120*m+89-1 = 120*m+88 by omega] at hf
      rw [← pow_mul, show 3*(80*m+59) = 1 + (120*m+88)*2 by ring, pow_add, pow_mul,
        hf]; simp
  rw [key x, key y, h]

theorem cubicRootEscape_iff : CubicRootEscape ↔ CubeRootEscape := by
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun N => ?_⟩
    obtain ⟨m, hm, hp, hle⟩ := h N
    refine ⟨m, hm, hp, fun b hb => ?_⟩
    have hA := dvd_cube_sub m hp (2^(20*m+18)) (by push_cast; rfl)
    have hc : (b : ZMod (120*m+89)) = ((2:ℤ)^(20*m+18) : ℤ) := by
      apply cube_inj m hp
      have e1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb
      have e2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hA
      push_cast at e1 e2 ⊢
      rw [sub_eq_zero.1 e1, sub_eq_zero.1 e2]
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hc.symm
    have hp0 : ((120*m+89 : ℕ) : ℝ) ≠ 0 := by positivity
    have : (b : ℝ) / (120*m+89 : ℕ) = ((2:ℚ)^(20*m+18) / (120*m+89) : ℚ) + k := by
      have : (b : ℝ) = (2:ℝ)^(20*m+18) + ((120*m+89 : ℕ) : ℝ) * k := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hk; push_cast at this ⊢; linarith
      rw [this]; push_cast; field_simp
    rw [this, dZ_add_int]; exact hle
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun N => ?_⟩
    obtain ⟨m, hm, hp, hle⟩ := h N
    refine ⟨m, hm, hp, ?_⟩
    have := hle (2^(20*m+18)) (dvd_cube_sub m hp _ (by push_cast; rfl))
    convert this using 2; push_cast; ring

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
