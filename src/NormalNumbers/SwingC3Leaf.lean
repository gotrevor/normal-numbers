/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Mean

/-!
# The crux of the swing, as a single named leaf

Laps 5–10 reduced `ConjC3` to one statement about one explicit real constant per `P`:

    L_P = ∑_{p > P prime} 1/(b^p − 1)              (`largeLambert_eq_tsum`)

    WeylLambertTwist b :
      (1/N) ∑_{n<N} e(jn/Q) · e(h · L_P · b^n)  →  0    for 0 < j < Q.

`CastingOut.conjC3_of_weylLambertTwist` derives `ConjC3` from it, axiom-clean.  This file pins
the remaining obligation as a single named `sorry` in `src/`, per the kickoff's rule that a leaf
which resists stays a named sorry in `src/`.

## What is proved around it

* `sum_addChar_tailTrunc_eq_zero` — over a COMPLETE period the sum is **exactly zero**; there is
  no structural obstruction (lap 6).
* `addCharTailTrunc_tendsto` — for every FIXED truncation `K` the statement already holds, with
  the explicit rate `‖∑_{n<N}‖ ≤ (∏_{P<p≤K} p)·Q` (lap 7).
* `tailLarge_sub_truncate_mem_Icc` — truncating at `K ≥ 2N` costs `≤ 2 b^{n−K}` pointwise, i.e.
  nothing (lap 5b).
* `sum_inv_le_of_prod_le` — **refutation**: no choice of prime SUBSET as the period escapes the
  gap, since `∏_{p∈S} p ≤ N` forces `∑_{p∈S} 1/p ≤ log N/(min S · log min S)` (lap 8).
* `sum_range_tailTrunc_sub_le` — the discarded mass in the window is exactly
  `∑_{K<p≤K'}(N/p + 1)/(b−1)`: the budget any attack must beat (lap 10).

## What is missing

Exactly the window `log N ≪ K ≪ N`.  The proved rate needs the period `∏_{P<p≤K} p ≈ e^K` to be
`≤ N`, forcing `K ≲ log N`; freeness of the truncation needs `K ≳ N`.  The only structurally
untried handle is **partial cancellation inside an incomplete period** — beating the trivial
`‖∑_{n<N}‖ ≤ L` of `norm_sum_range_le_of_period` when `L ≫ N`.

## Numerical evidence

`probes/swingc3_weyl_lambert_twist.py` evaluates the twisted sum directly from the digit stream
`ω_{>P}` for `(b,P,Q,j,h)` ranging over seven parameter sets up to `N = 4·10^5`.  It decays as
`(log N)^{−a}` with `a ≈ 1.3–3.7` — never plateauing.  For `h = 1` the fitted `a ≈ 1.9–2.0`,
which independently reproduces the 2026-09-24 B4 measurement (`a ≈ a₀ + 1`, `a₀ ≈ 0.84`) by a
completely different computational route, and so cross-checks `ee_tailLarge_eq_ee_orbit`.
-/

namespace NormalNumbers

namespace CastingOut

/-- **THE CRUX.**  The `×b` orbit of the large-prime Lambert constant
`L_P = ∑_{p>P} 1/(b^p − 1)` does not correlate with any nontrivial additive character modulo a
small-prime modulus `Q`.

Open.  See the module docstring for the five machine-checked facts surrounding it, the exact
window `log N ≪ K ≪ N` where it is missing, and the numerical evidence (decay `(log N)^{−a}`,
`a ≈ 1.3–3.7`). -/
theorem weylLambertTwist_holds (b : ℕ) (hb : 3 ≤ b) : WeylLambertTwist b := by
  sorry

/-- `ConjC3` via the sharpest route: everything except `weylLambertTwist_holds` is proved. -/
theorem conjC3_via_weylLambert : ConjC3 :=
  conjC3_of_weylLambertTwist weylLambertTwist_holds

end CastingOut

end NormalNumbers
