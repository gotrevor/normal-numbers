/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtPhaseForm

/-!
# The depth phase is a PERTURBED ×b ORBIT

Lap 100 showed the crux is the equidistribution of `n ↦ h'·depthPhase b K n`, where
`depthPhase b K n = ∑_{i<K} ω(n+i+1)/b^{i+1}`.  This file identifies the exact dynamics of that
sequence, and the identity is sharper than expected.

`depthPhase_succ` — an EXACT recursion, valid for every `K` including `K = 0`:

    depthPhase b K (n+1) = b · depthPhase b K n − ω(n+1) + ω(n+K+1)/b^K .

The mechanism is that `depthPhase` reads the string `ω(n+1), ω(n+2), …, ω(n+K)` as a base-`1/b`
expansion, so advancing `n` by one is the base-`b` SHIFT on that string: multiply by `b`, drop the
leading digit `ω(n+1)`, and feed in the new deep digit `ω(n+K+1)` at weight `b^{-K}`.

Since `h'` and `ω(n+1)` are integers, the dropped digit is invisible to the additive character:

    ee_depthPhase_succ :  e(h'·depthPhase b K (n+1))
        = e(b·h'·depthPhase b K n + h'·ω(n+K+1)/b^K) .

**What this says about the crux.**  Modulo 1, the phase sequence is the orbit of the expanding map
`x ↦ b·x` perturbed, at each step, by at most `|h'|·ω(n+K+1)/b^K`.  So the C3 crux is not an
arbitrary equidistribution question: it asks that a perturbed `×b` orbit equidistribute, with the
perturbation controlled by the deep `ω` values.  This is exactly the "casting out" dynamics this
namespace is named for, arriving from the correlation side — and it explains structurally why the
depth schedule must be tied to `b^K ≍ log log N`: the per-step perturbation is `≍ ω/b^K`, and the
whole route lives or dies on whether that is small against the target saving.

Note the perturbation is NOT negligible in the sense lap 99 refuted: `ω(n+K+1)/b^K` summed over a
window of length `N` is `≍ N·log log N/b^K`, which at the diagonal is `≍ N`, not `o(N)`.  The
recursion is therefore a structural identity to exploit, not an approximation to discard.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- **The depth phase is the base-`b` shift on the `ω`-string.**  Exact, all `K ≥ 0`. -/
theorem depthPhase_succ {b : ℕ} (hb : 0 < b) (K n : ℕ) :
    depthPhase b K (n + 1)
      = (b : ℝ) * depthPhase b K n - (omegaNat (n + 1) : ℝ)
        + (omegaNat (n + K + 1) : ℝ) / (b : ℝ) ^ K := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  induction K with
  | zero =>
    simp only [depthPhase, Finset.range_zero, Finset.sum_empty, pow_zero, mul_zero, div_one]
    ring
  | succ K ih =>
    have e1 : n + 1 + K + 1 = n + (K + 1) + 1 := by omega
    simp only [depthPhase, Finset.sum_range_succ] at ih ⊢
    rw [e1] at *
    have hpow : (0 : ℝ) < (b : ℝ) ^ (K + 1) := by positivity
    have hpowK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
    rw [ih]
    field_simp
    ring

/-- **The character form of the shift recursion.**  The dropped leading digit is an integer, so
it is invisible to `e(·)`: the phase is a `×b` orbit perturbed only by the incoming deep digit. -/
theorem ee_depthPhase_succ {b : ℕ} (hb : 0 < b) (K n : ℕ) (h : ℤ) :
    ee ((((h : ℝ) * depthPhase b K (n + 1) : ℝ) : ℂ))
      = ee ((((b : ℝ) * ((h : ℝ) * depthPhase b K n)
          + (h : ℝ) * (omegaNat (n + K + 1) : ℝ) / (b : ℝ) ^ K : ℝ) : ℂ)) := by
  have hrec := depthPhase_succ hb K n
  have hsplit : (h : ℝ) * depthPhase b K (n + 1)
      = ((b : ℝ) * ((h : ℝ) * depthPhase b K n)
          + (h : ℝ) * (omegaNat (n + K + 1) : ℝ) / (b : ℝ) ^ K)
        + (-((h * (omegaNat (n + 1) : ℤ) : ℤ) : ℝ)) := by
    rw [hrec]
    push_cast
    ring
  rw [hsplit]
  have hpush : ((((b : ℝ) * ((h : ℝ) * depthPhase b K n)
        + (h : ℝ) * (omegaNat (n + K + 1) : ℝ) / (b : ℝ) ^ K)
      + (-((h * (omegaNat (n + 1) : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ)
      = ((((b : ℝ) * ((h : ℝ) * depthPhase b K n)
        + (h : ℝ) * (omegaNat (n + K + 1) : ℝ) / (b : ℝ) ^ K : ℝ) : ℂ))
        + (((-(h * (omegaNat (n + 1) : ℤ)) : ℤ) : ℂ)) := by
    push_cast
    ring
  rw [hpush, ee_add, ee_int, mul_one]

#print axioms NormalNumbers.CastingOut.depthPhase_succ
#print axioms NormalNumbers.CastingOut.ee_depthPhase_succ

end CastingOut

end NormalNumbers
