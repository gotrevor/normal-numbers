/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Leaf

/-!
# The audit surface for the swing's conditional

`CastingOut.conjC3_of_weylLambertTwist` is restated here with **every** abbreviation unwound: no
`ConjC3`, no `IsRich`, no `OccursAt`, no `digitOf`, no `primeLambertAtBase`, no
`WeylLambertTwist`, no `largeLambert`, no `ee`.  An auditor reads only `Nat.primeFactors`,
`Complex.exp`, two `tsum`s, `⌊·⌋`, `Int.fract` and a `Finset.card` density.

In words:

> Suppose that for every base `b ≥ 3`, every `P`, every modulus `Q > 0`, every `j` with
> `0 < j < Q` and every integer `h`, the twisted Weyl averages
>
>     (1/N) ∑_{n<N} exp(2πi·jn/Q) · exp(2πi·h·b^n·∑_{p>P prime} 1/(b^p − 1))
>
> tend to `0`.  Then for every `b ≥ 3` the prime Lambert number `G_b = ∑_n ω(n) b^{−n}` is
> RICH in base `b`: every finite word over the digits `{0,…,b−1}` occurs in its base-`b`
> expansion at a set of positions of positive lower density.

The hypothesis is a statement about **one explicit real constant per `(b,P)`** — the tail
`∑_{p>P} 1/(b^p − 1)` of the base-`b` prime-characteristic constant — and nothing else.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

open Classical in
/-- **Audit form of the swing's conditional.**  Definitionally the same statement as
`conjC3_of_weylLambertTwist`, with every definition of the chain unfolded. -/
theorem audit_conjC3_of_weylLambertTwist
    (H : ∀ b : ℕ, 3 ≤ b → ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N,
          Complex.exp (2 * Real.pi * Complex.I * (((j : ℝ) * n / Q : ℝ) : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I *
                ((((h : ℝ) * ((∑' p : ℕ,
                    (if P < p ∧ p.Prime then 1 / ((b : ℝ) ^ p - 1) else 0)) * (b : ℝ) ^ n)
                  : ℝ)) : ℂ))) / N) atTop (𝓝 0)) :
    ∀ b : ℕ, 3 ≤ b → ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N in atTop, c * N ≤ (((range N).filter (fun n =>
        ∀ j (hj : j < w.length),
          (⌊Int.fract (∑' m : ℕ,
              (ArithmeticFunction.cardDistinctFactors m : ℝ) / (b : ℝ) ^ m)
            * (b : ℝ) ^ (n + j + 1)⌋).toNat % b = w[j])).card : ℝ) := by
  have key : ConjC3 := by
    refine conjC3_of_weylLambertTwist (fun b hb => ?_)
    intro P Q j h hQ hj0 hjQ
    have hb2 : 2 ≤ b := by omega
    refine (H b hb P Q j h hQ hj0 hjQ).congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ee, ee, largeLambert_eq_tsum hb2 P]
  intro b hb w hw
  obtain ⟨c, hc, hN⟩ := key b hb w hw
  refine ⟨c, hc, hN.mono fun N hle => ?_⟩
  refine le_trans hle (le_of_eq ?_)
  congr 2
  exact Finset.filter_congr (fun n _ => Iff.rfl)

end NormalNumbers.CastingOut
