/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyE0Down
import NormalNumbers.G4EntropyXCeiling

/-!
# The **certified outer scales leave a gap**, and the gap is what blocks prefix control

Two modules bracket the outer scale `X` at a fixed rung `K` of the base-four ladder:

* `G4EntropyXCeiling` (objective A0) — the `hbig` field of every `ScheduleWitness` caps
  `log Mx / log Y ≤ 3·2^K δbig ε η`, so at the implemented allowances
  `W.X ≤ 2^{2^{m K + 3k₄}} + X K =: Xhi K`.  **E0 cannot be raised past `Xhi K`.**
* `G4EntropyE0Down` — E0 survives shrinking `X` down to `Xlo K = Y K ^ 50 = √(X K)`, and no
  further: `hbig`'s `2Y²·rowL2²/|P'|` and `smallPrimeBound`'s `2R^{Mc}/Psz` both need the sample
  to have `≳ Y²` points.  **E0 cannot be lowered past `Xlo K`.**

So rung `K` certifies exactly the outer scales in `[Xlo K, Xhi K]`.  This module proves that
**consecutive rungs' certified ranges do not meet**:

> `Sched.Xhi_lt_Xlo_step` — `Xhi K < Xlo (K + 4)` for every `K = 4k₄ ≥ 100`.

and packages the consequence as a named `Prop`, `Sched.ScaleGap K`, with a witness.

## Why this is the obstruction, and not a curiosity

A band-`i` window start is `2·kIdx(n, α)`, increasing in `n`, so a position cutoff inside band
`i` selects the truncated sample `n ≤ X'` — and `entropy_E0_down` certifies the prefix of band
`i` at every `X' ∈ [Xlo K, X K]`.  Prefix control inside a band is therefore *not* the problem.
The problem is the **head**: the cutoffs with `X' < Xlo K_i`, which `entropy_E0_down` cannot
certify, and which cannot be certified by the previous rung either — because everything rung
`K − 4` can reach, `Xhi (K−4)`, is strictly below `Xlo K`.

Those head cutoffs are not negligible against the history: the digits read before band `i` are
governed by the outer scale `X (K−4) ≤ Xhi (K−4) < Xlo K`, while the head itself is the sample
up to `Xlo K`.  This is `certified_granule_exceeds_previous_scale`'s size comparison seen from
the *downward* side, and it says precisely that **the downward route does not close prefix
control at a band transition** — the interval `(Xhi (K−4), Xlo K)` of outer scales is certified
by no rung at all.

This is a statement about the *schedule's ladder*, `m₁(K+4) ≥ 4096·m₁ K`, not about the quality
of any entropy estimate: the two floors are separated by a tower, so no constant, no deficit
improvement and no change of residue class (objective B) can bridge it.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

/-- **A0's ceiling on the outer scale at rung `K`**: `2^{2^{m K + 3k₄}} + X K`, the bound
`ScheduleWitness.X_lt_X_step` derives from `hbig`.  Every schedule witness at rung `K` with the
implemented allowances has `W.X ≤ Xhi K k₄`. -/
def Xhi (K k₄ : ℕ) : ℕ := 2 ^ 2 ^ (m K + 3 * k₄) + X K

lemma Xlo_le_Xhi (K k₄ : ℕ) : Xlo K ≤ Xhi K k₄ := by
  have h := Xlo_le_X K
  have h2 : X K ≤ Xhi K k₄ := Nat.le_add_left _ _
  omega

/-- **The certified ranges of consecutive rungs are separated, and not by one.**  Everything
rung `K` can certify — A0's ceiling `Xhi K k₄`, which already includes the whole of `X K` — stays
strictly below `Xlo (K+4) − 1`, one less than the *floor* at which rung `K+4`'s certificate first
becomes non-vacuous.

The proof is the ladder arithmetic of `m_add_lt` (`m K + 3k₄ < m (K+4)`), and nothing else. -/
theorem Xhi_succ_lt_Xlo_step {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    Xhi K k₄ + 1 < Xlo (K + 4) := by
  have hk : 25 ≤ k₄ := by omega
  have hmlt := m_add_lt hK4 hK
  set a := m K + 3 * k₄ with ha
  set b := m (K + 4) with hb
  have hXhi : Xhi K k₄ = 2 ^ 2 ^ a + X K := by rw [ha]; rfl
  have hXlo : Xlo (K + 4) = 2 ^ (2 ^ b * 50) := by
    rw [hb]; unfold Xlo Y; rw [← pow_mul]
  -- `X K ≤ 2^{2^a}`: the exponent `100·2^{m K}` fits under `2^a`
  have h100 : 100 * 2 ^ m K ≤ 2 ^ a := by
    have h7 : (100 : ℕ) ≤ 2 ^ (3 * k₄) := by
      calc (100 : ℕ) ≤ 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (3 * k₄) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 100 * 2 ^ m K ≤ 2 ^ (3 * k₄) * 2 ^ m K := Nat.mul_le_mul_right _ h7
      _ = 2 ^ a := by rw [ha, pow_add]; ring
  have hXK : X K ≤ 2 ^ 2 ^ a := by
    unfold X
    exact Nat.pow_le_pow_right (by norm_num) h100
  -- so `Xhi + 1 ≤ 2^{2^a + 2}`
  have hpa : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have hsum : Xhi K k₄ + 1 ≤ 2 ^ (2 ^ a + 2) := by
    have h1 : 2 ^ (2 ^ a + 2) = 2 ^ 2 ^ a + 2 ^ 2 ^ a + (2 ^ 2 ^ a + 2 ^ 2 ^ a) := by
      rw [pow_succ, pow_succ]; ring
    have h2 : 1 ≤ 2 ^ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
    omega
  -- and `2^a + 2 < 2^b · 50`
  have hab2 : 2 ^ a + 2 ≤ 2 ^ b := by
    have h1 : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by rw [pow_succ]; ring
    have h3 : 2 ≤ 2 ^ a := by
      have h4 : (2 : ℕ) ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using h4
    omega
  have hbpos : 0 < 2 ^ b := Nat.two_pow_pos b
  have hfin : 2 ^ (2 ^ a + 2) < Xlo (K + 4) := by
    rw [hXlo]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- The certified ranges of consecutive rungs do not meet. -/
theorem Xhi_lt_Xlo_step {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    Xhi K k₄ < Xlo (K + 4) := by
  have := Xhi_succ_lt_Xlo_step hK4 hK
  omega

/-- **The gap is inhabited**: an outer scale certified by no rung of the ladder.  `ScaleGap K k₄`
says there is an `X'` strictly above everything rung `K` can certify and strictly below the
floor at which rung `K+4` becomes non-vacuous. -/
def ScaleGap (K k₄ : ℕ) : Prop := ∃ X' : ℕ, Xhi K k₄ < X' ∧ X' < Xlo (K + 4)

/-- The gap of `Xhi_lt_Xlo_step` is nonempty. -/
theorem scaleGap {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) : ScaleGap K k₄ :=
  ⟨Xhi K k₄ + 1, by omega, Xhi_succ_lt_Xlo_step hK4 hK⟩

end Sched

/-- **A0's ceiling, restated against the next rung's floor.**  Any schedule witness at rung `K`
with the implemented allowances has outer scale strictly below `Xlo (K+4)`, the smallest scale at
which `entropy_E0_down` certifies rung `K+4`.

`ScheduleWitness.X_lt_X_step` says a witness cannot reach the *next band's own scale*; this says
it cannot even reach the point where the next band's certificate switches on.  That interval —
the head of band `i+1` — is therefore certified by no rung, which is exactly what stops the
downward route from closing prefix control at a band transition. -/
theorem ScheduleWitness.X_lt_Xlo_step {ℓ w K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (W : ScheduleWitness ℓ w) (hWK : W.G.K = K) (hWY : W.Y = Sched.Y K)
    (_hδ0 : 0 ≤ W.δbig) (hδ : W.δbig ≤ 1 / 8) (hε : W.ε ≤ 1 / (K : ℝ))
    (hη : W.η ≤ (1 / 2 : ℝ) ^ k₄) (hP₀ : 2 * W.G.P₀ ≤ Sched.X K) (i : W.G.Idx) :
    W.X < Sched.Xlo (K + 4) := by
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hA : (0 : ℝ) < (2 : ℝ) ^ (3 * k₄) := by positivity
  have hB : (0 : ℝ) < (2 : ℝ) ^ k₄ := by positivity
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hbe : W.bigExp ≤ (2 : ℝ) ^ (3 * k₄) := by
    have hεη : W.ε * W.η ≤ (1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄ :=
      mul_le_mul hε hη W.hη.le (by positivity)
    have hεη0 : (0 : ℝ) ≤ W.ε * W.η := mul_nonneg W.hε.le W.hη.le
    have hprod : W.δbig * (W.ε * W.η) ≤ (1 / 8 : ℝ) * ((1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄) :=
      mul_le_mul hδ hεη hεη0 (by norm_num)
    have he : (2 : ℝ) ^ K = (2 : ℝ) ^ (3 * k₄) * (2 : ℝ) ^ k₄ := by
      rw [← pow_add]; congr 1; omega
    have h2 : ((1 : ℝ) / 2) ^ k₄ = 1 / (2 : ℝ) ^ k₄ := by rw [div_pow, one_pow]
    have h38 : (3 : ℝ) / (8 * (K : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    rw [ScheduleWitness.bigExp, hWK]
    calc 3 * (2 : ℝ) ^ K * (W.δbig * (W.ε * W.η))
        ≤ 3 * (2 : ℝ) ^ K * ((1 / 8 : ℝ) * ((1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 3 / (8 * (K : ℝ)) * (2 : ℝ) ^ (3 * k₄) := by
          rw [he, h2]; field_simp
      _ ≤ 1 * (2 : ℝ) ^ (3 * k₄) := mul_le_mul_of_nonneg_right h38 hA.le
      _ = (2 : ℝ) ^ (3 * k₄) := one_mul _
  have hY2 : Sched.Y K = 2 ^ 2 ^ Sched.m K := rfl
  have hYgt : 1 < W.Y := by
    rw [hWY, hY2]
    exact Nat.one_lt_two_pow (by positivity)
  have hXle := W.X_le_rpow hYgt i
  have hYcast : ((W.Y : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ Sched.m K : ℕ) : ℝ) := by
    rw [hWY, hY2, Real.rpow_natCast]
    push_cast
    ring
  have hmul : ((2 ^ Sched.m K : ℕ) : ℝ) * W.bigExp ≤ ((2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < ((2 ^ Sched.m K : ℕ) : ℝ) := by positivity
    calc ((2 ^ Sched.m K : ℕ) : ℝ) * W.bigExp
        ≤ ((2 ^ Sched.m K : ℕ) : ℝ) * (2 : ℝ) ^ (3 * k₄) :=
          mul_le_mul_of_nonneg_left hbe hp.le
      _ = ((2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by push_cast [pow_add]; ring
  have hrpow : (W.Y : ℝ) ^ W.bigExp ≤ ((2 ^ 2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by
    rw [hYcast, ← Real.rpow_mul (by norm_num)]
    have : ((2 ^ 2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ)
        = (2 : ℝ) ^ ((2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hmul
  have hP₀r : ((W.G.P₀ : ℕ) : ℝ) ≤ ((Sched.X K : ℕ) : ℝ) := by
    have : W.G.P₀ ≤ Sched.X K := by omega
    exact_mod_cast this
  have hfinal : ((W.X : ℕ) : ℝ) ≤ ((2 ^ 2 ^ (Sched.m K + 3 * k₄) + Sched.X K : ℕ) : ℝ) := by
    push_cast
    push_cast at hXle hrpow hP₀r
    linarith
  have hnat : W.X ≤ Sched.Xhi K k₄ := by
    have : W.X ≤ 2 ^ 2 ^ (Sched.m K + 3 * k₄) + Sched.X K := by exact_mod_cast hfinal
    simpa [Sched.Xhi] using this
  exact lt_of_le_of_lt hnat (Sched.Xhi_lt_Xlo_step hK4 hK)

end NormalNumbers.G4
