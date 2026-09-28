import NormalNumbers.TwoPointPairing

/-!
# The elementary pairing route is rigid — and therefore dead

Lap 21 reduced the per-pair saving to a construction: an injection `σ` of a positive-density set
of `m` with

    ζ^{ω(p·σ(m)+1)} conj ζ^{ω(q·σ(m)+1)} W(σ m)  =  z · ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W(m),

`z ≠ 1` fixed.  The only elementary way to move `ω` by a *known* amount is to multiply the
argument by a fixed prime: `p·σ(m)+1 = r·(pm+1)` raises `ω` of the `p`-dilate by exactly one
whenever `r ∤ (pm+1)`.  This file shows that such a `σ` cannot leave the `q`-dilate under
control, for a purely algebraic reason.

* `pairing_shift` — the forced shape.  If `r = p·k+1` and `σ(m) = r·m + k`, then

      p·σ(m) + 1 = r·(p·m + 1)     and     q·σ(m) + 1 = r·(q·m + 1) + (q − p)·k .

  So the `q`-dilate is the corresponding multiple **plus a nonzero additive defect** `(q−p)k`,
  and `ω` of `r·(qm+1) + (q−p)k` bears no relation to `ω(qm+1)`.

* **`no_elementary_pairing`** — the rigidity, with no `ω` anywhere.  If a map `σ` satisfies
  `p·σ(m)+1 = r·(pm+1)` *and* `q·σ(m)+1 = s·(qm+1)` at two consecutive `m`, with `p ≠ q` and
  `p, q ≠ 0`, then `r = s = 1`, i.e. `σ` is the identity and the rotation is trivial.

**Verdict.**  No multiplicative move can raise `ω` on one dilate by a known amount while keeping
the other dilate a fixed multiple.  This is the same rigidity that makes two-point Chowla/Elliott
hard: the two dilates cannot be decoupled by an elementary substitution.  The pairing route of
lap 21 is therefore refuted *for multiplicative `σ`*, which is the only class for which the
`ω`-shift is computable.  Lap 21's tool (`norm_sum_le_of_rotation`) remains correct and available
for any future non-elementary construction; what is refuted is the construction sketched there.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The forced shape of a multiplicative pairing, and the `q`-side defect. -/
theorem pairing_shift (p q k m : ℤ) :
    p * ((p * k + 1) * m + k) + 1 = (p * k + 1) * (p * m + 1)
      ∧ q * ((p * k + 1) * m + k) + 1 = (p * k + 1) * (q * m + 1) + (q - p) * k := by
  constructor <;> ring

/-- **RIGIDITY.**  A substitution cannot make both dilates fixed multiples unless it is
the identity. -/
theorem no_elementary_pairing (p q r s m σ₀ σ₁ : ℤ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (h0p : p * σ₀ + 1 = r * (p * m + 1))
    (h0q : q * σ₀ + 1 = s * (q * m + 1))
    (h1p : p * σ₁ + 1 = r * (p * (m + 1) + 1))
    (h1q : q * σ₁ + 1 = s * (q * (m + 1) + 1)) :
    r = 1 ∧ s = 1 := by
  -- the step of `σ` is `r`, and also `s`
  have hstepr : p * (σ₁ - σ₀) = p * r := by linarith [h1p, h0p]
  have hsteps : q * (σ₁ - σ₀) = q * s := by linarith [h1q, h0q]
  have hr : σ₁ - σ₀ = r := by
    have := mul_left_cancel₀ hp hstepr
    exact this
  have hs : σ₁ - σ₀ = s := mul_left_cancel₀ hq hsteps
  have hrs : r = s := by rw [← hr, hs]
  subst hrs
  -- with `r = s`, subtracting the two relations forces `σ₀ = r·m`
  have hsub : (p - q) * σ₀ = r * m * (p - q) := by
    have h := h0p
    have h' := h0q
    nlinarith [h, h']
  have hpq' : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hσ : σ₀ = r * m := by
    have := mul_right_cancel₀ hpq' (by linarith [hsub] : σ₀ * (p - q) = (r * m) * (p - q))
    exact this
  rw [hσ] at h0p
  have : r = 1 := by nlinarith [h0p]
  exact ⟨this, this⟩

end NormalNumbers.CastingOut
