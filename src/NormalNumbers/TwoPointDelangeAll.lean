import NormalNumbers.TwoPointDelangeLevin

/-!
# The 🟡 removed from the `ConjC1` chain

`TwoPointDelangeLevin.lean` proves `delangeMean_of_phase_ne_one : phase t ≠ 1 → DelangeMean t`
unconditionally.  This file feeds that into the narrowed consumers of `TwoPointDelangeWire.lean`,
which until now still carried a `hD` hypothesis on `‖phase (m/b) − 1‖ ≥ 1`.

After this file, `ConjC1` rests on exactly ONE input — the arithmetic leaf (`MultiElliott` /
`PairDecorr` / `TwoPointWeightedAvg`), which SESSION WRAP 4 pinned as an equivalence with a named
open problem, and which the paper itself states conditionally.  **No cited-but-unproved theorem
remains anywhere under `ConjC1`.**
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **Delange's theorem, hypothesis-free, in the exact shape the `ConjC1` reductions consume.** -/
theorem delangeMean_all :
    ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b) :=
  fun b hb m _ hdvd =>
    delangeMean_of_phase_ne_one _ (phase_div_ne_one (by omega) hdvd)

/-- **`ConjC1` from `MultiElliott` alone.** -/
theorem conjC1_of_multiElliott
    (hME : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliott b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_multiElliott delangeMean_all hME

/-- **`ConjC1` from `PairDecorr` alone.** -/
theorem conjC1_of_pairDecorr
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      PairDecorr b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_pairDecorr delangeMean_all hP

end NormalNumbers.CastingOut
