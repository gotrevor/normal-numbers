import NormalNumbers.DelangeSlotAnalytic
import NormalNumbers.DelangeSlotTwist

/-!
# The Leaf-B slot: twisted means of `z^{ω_{>P}}` vanish (Delange type)

The one-slot piece of `TailLargeDecouple` (C3 swing, `SwingC3Rotation.lean`).  For fixed `P`, `Q`,
a unimodular `z ≠ 1` and any additive twist `e(jm/Q)`, the mean of `e(jm/Q)·z^{ω_{>P}(m)}` tends
to `0`.  `ω_{>P}` counts distinct prime factors above `P`.

Why it is true: split `m = s·t`, with `s` `P`-smooth and `t` `P`-rough.  `Q` is a free parameter,
but the twist only sees `m mod Q`; expand in Dirichlet characters mod `Q/gcd`.  Each piece is a
mean of the multiplicative `t ↦ χ(t) z^{ω(t)} 1_{t rough}`, with value `zχ(p)` at primes `p > P`.
That never pretends to be `χ'(p) p^{it}`.  For the untwisted piece the mean is
`≍ Π_{P<p≤N}(1 + (z−1)/p) → 0`, since `Re z < 1`.  Full Halász is NOT the intended route
(Trevor, 2026-09-24).  Use the constant-on-primes structure: Selberg–Delange-lite via
`L(s,χ)^z` with mathlib's `LFunction_ne_zero_of_one_le_re`, or an elementary Kubilius-model /
sieve route.
-/

open Finset Filter Topology Complex Real

namespace NormalNumbers.DelangeSlot

/-- **Untwisted Delange.**  `Q = 1` case, the first rung. -/
theorem omegaLarge_mean_tendsto_zero (P : ℕ) (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ => (∑ m ∈ Icc 1 N, z ^ omegaLarge P m) / (N : ℂ)) atTop (𝓝 0) := by
  have hEq : ∀ N : ℕ, (∑ m ∈ Icc 1 N, z ^ omegaLarge P m) / (N : ℂ) = sigmaMean z P N := by
    intro N
    rw [sigmaMean, Ssum]
    congr 1
  simpa only [hEq] using sigmaMean_tendsto_zero hz hz1 P

/-- **The Leaf-B slot.**  Twisted by an additive character mod `Q`. -/
theorem twisted_omegaLarge_mean_tendsto_zero (P Q : ℕ) (hQ : 0 < Q) (j : ℤ) (z : ℂ)
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ =>
        (∑ m ∈ Icc 1 N, exp (2 * π * I * j * m / Q) * z ^ omegaLarge P m) / (N : ℂ))
      atTop (𝓝 0) := by
  have hEq : ∀ N : ℕ,
      (∑ m ∈ Icc 1 N, exp (2 * π * I * j * m / Q) * z ^ omegaLarge P m) / (N : ℂ)
        = (∑ m ∈ Ioc 0 N, Complex.exp (2 * Real.pi * Complex.I * j * m / Q) * hfun z P m)
            / (N : ℂ) := by
    intro N
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N from Finset.ext fun x => by simp [Nat.succ_le_iff]]
    rfl
  simpa only [hEq] using twisted_tendsto_zero hQ j hz hz1 P

end NormalNumbers.DelangeSlot
