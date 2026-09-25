import NormalNumbers.TwoPointDelangeLevin
import NormalNumbers.DelangeSlotMaster

/-!
# The 🟡 removed from the `ConjC1` chain

`TwoPointDelangeLevin.lean` proves `delangeMean_of_phase_ne_one : phase t ≠ 1 → DelangeMean t`
unconditionally.  This file feeds that into the narrowed consumers of `TwoPointDelangeWire.lean`,
which until now still carried a `hD` hypothesis on `‖phase (m/b) − 1‖ ≥ 1`.

After this file, `ConjC1` rests on exactly ONE input — the arithmetic leaf (`MultiElliott` /
`PairDecorr` / `TwoPointWeightedAvg`), which SESSION WRAP 4 pinned as an equivalence with a named
open problem, and which the paper itself states conditionally.  **No cited-but-unproved theorem
remains anywhere under `ConjC1`.**

## The independent cross-check (found lap 60, AFTER the elementary proof)

`DelangeSlot.charSum_tendsto_zero` — the master dichotomy of the `DelangeSlot` rung-2 programme,
proved and axiom-clean in this tree — specialises at `M = 1`, `κ ≡ 1`, `P = 0` to exactly
`∑_{n≤N} z^{ω(n)} = o(N)`, because `omegaLarge 0 = ω`.  **So the 🟡 was already discharged in this
repo and the connection had simply never been made.**  `delangeMean_via_delangeSlot` below records
that derivation, so the two routes are both in kernel and visibly agree.  They are genuinely
independent: `charSum_tendsto_zero` runs through Dirichlet `L`-functions, `ψ(x,χ) = o(x)` and
Wiener–Ikehara, whereas `TwoPointDelangeLevin.lean` uses only the hyperbola-averaged quantitative
PNT and elementary summation — no `L`-function, no character, no contour.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **The cross-check.**  The same statement out of the `DelangeSlot` rung-2 machinery, by a
completely different route (Dirichlet `L`-functions + Wiener–Ikehara).  Kernel-level agreement
between the two proofs. -/
theorem delangeMean_via_delangeSlot {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ => mOm z N / (N : ℂ)) atTop (𝓝 0) := by
  have h : NormalNumbers.DelangeSlot.IsCharLike 1 (fun _ => (1:ℂ)) := by
    refine ⟨by norm_num, by intro a b; simp, by intro a b _; rfl, ?_, by intro n; simp⟩
    intro n hn; exact absurd (Nat.coprime_one_right n) hn
  have key := NormalNumbers.DelangeSlot.charSum_tendsto_zero h hz hz1 0
  refine key.congr fun N => ?_
  congr 1
  rw [NormalNumbers.DelangeSlot.Sgsum, mOm]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Ioc] at hn
  rw [NormalNumbers.DelangeSlot.gfun, NormalNumbers.DelangeSlot.hfun, one_mul,
    fOm_of_pos (by omega : n ≠ 0)]
  congr 1
  rw [NormalNumbers.DelangeSlot.omegaLarge, omegaNat]
  congr 1
  refine Finset.filter_true_of_mem fun p hp => ?_
  exact (Nat.prime_of_mem_primeFactors hp).pos

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
