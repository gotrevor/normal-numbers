/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffSixRoot

/-!
# Cutoff six, the `p ≡ 1 (mod 120)` class: a quadratic lever

For `p = 120t+1` prime and `n = 20t`, the full exit has exactly one term,
`2^(20t+6)/p` (`rationalExit_six_eq_one`; the other candidate `120t+5` is a
multiple of 5).  Its numerator is `64·ζ` with `ζ = 2^((p-1)/6)` a cube root of
unity mod `p`.  When `ζ ≠ 1` (equivalently `2` is not a sixth-power residue —
a Chebotarev condition, density `> 0`, not in mathlib), `ζ² + ζ + 1 = 0`, so the
numerator is a root of the *quadratic* `x² + 64x + 4096` (discriminant `-3·64²`).

`QuadraticRootEscape` asks that roots of that quadratic mod such primes stay
`ε·p` from `0` infinitely often.  Equidistribution of roots of a quadratic
congruence of negative discriminant to prime moduli is a theorem of
Duke–Friedlander–Iwaniec (Annals 1995); our node is NOT literally that theorem:
it needs the restriction to `p ≡ 1 (mod 120)` with `2^((p-1)/6) ≠ 1`, a
Chebotarev-type subset (restricted versions: Tóth 2000 for congruence classes;
the sixth-power condition is a further splitting condition).  It is however only a
liminf statement, much weaker than equidistribution.  Proved here:
`nonvanishing_of_quadraticRootEscape`.  Contrast `cubicRootEscape_iff`: the
`p ≡ 89` class needs the (open) cubic analogue.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

open CutoffReview

/-- Exact one-term identification of the exit at `n = 20t`, `p = 120t+1`. -/
theorem rationalExit_six_eq_one (t : ℕ) (hp : Nat.Prime (120*t+1)) :
    rationalExit 6 (20*t) = (2:ℚ)^(20*t+6) / (120*t+1) := by
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exact absurd hp (by norm_num)
    · exact h
  unfold rationalExit
  rw [Finset.sum_eq_single (15*t)]
  · rw [if_pos ⟨by convert hp using 1; ring, by omega, by omega⟩, if_neg]
    · rw [show 20*t+1-(15*t) = 5*t+1 by omega]
      push_cast
      rw [show (8*((15*t:ℚ))+1) = 120*t+1 by ring,
        show (16:ℚ) = 2^4 by norm_num, ← pow_mul,
        show (2:ℚ)^(20*t+6) = 2^(4*(5*t+1)) * 4 by
          rw [show 20*t+6 = 4*(5*t+1)+2 by ring, pow_add]; norm_num]
      ring
    · rintro ⟨hpr, -, -⟩
      rw [show 8*(15*t)+5 = 5*(24*t+1) by ring] at hpr
      exact Nat.not_prime_mul (by norm_num) (by omega) hpr
  · intro j _ hj
    rw [if_neg (by omega), if_neg]
    · simp
    rintro ⟨hpr, h1, h2⟩
    have : 8*j+5 = 5*(24*t+1) := by omega
    rw [this] at hpr
    exact Nat.not_prime_mul (by norm_num) (by omega) hpr
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- When `ζ = 2^(20t) ≠ 1`, the numerator `2^(20t+6)` is a root of `x²+64x+4096`. -/
theorem dvd_quadratic (t : ℕ) (hp : Nat.Prime (120*t+1))
    (hζ : (2 : ZMod (120*t+1))^(20*t) ≠ 1) :
    ((120*t+1 : ℕ) : ℤ) ∣ (2^(20*t+6))^2 + 64*2^(20*t+6) + 4096 := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have he := two_pow_half_eq (p := 120*t+1) (by omega)
  rw [if_pos (by omega), show (120*t+1)/2 = 60*t by omega] at he
  set z : ZMod (120*t+1) := 2^(20*t)
  have h3 : z^3 = 1 := by
    simp only [z]; rw [← pow_mul, show 20*t*3 = 60*t by ring, he]
  have hq : z^2 + z + 1 = 0 := by
    have : (z - 1) * (z^2 + z + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hζ
    · exact h
  push_cast
  rw [pow_add]
  linear_combination (2^6:ZMod (120*t+1))^2 * hq

/-- Roots of `x² + 64x + 4096` mod `p = 120t+1` (with `2^(20t) ≠ 1`) stay away
from `0` for infinitely many such `p`.  Open in this restricted form; see module doc. -/
def QuadraticRootEscape : Prop :=
  ∃ ε > 0, ∀ N, ∃ t ≥ N, Nat.Prime (120*t+1) ∧
    (2 : ZMod (120*t+1))^(20*t) ≠ 1 ∧
    ∀ b : ℤ, ((120*t+1 : ℕ) : ℤ) ∣ b^2 + 64*b + 4096 →
      ε ≤ dZ ((b : ℝ) / (120*t+1 : ℕ))

theorem nonvanishing_of_quadraticRootEscape (h : QuadraticRootEscape) :
    ExitSixNonvanishing := by
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun N => ?_⟩
  obtain ⟨t, ht, hp, hζ, hle⟩ := h N
  refine ⟨20*t, by omega, ?_⟩
  rw [rationalExit_six_eq_one t hp]
  convert hle _ (dvd_quadratic t hp hζ) using 2
  push_cast; ring

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
