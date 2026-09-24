import NormalNumbers.TwoPointGramDiagonal
import NormalNumbers.PairDecoupleElliott

/-!
# The C1 chain with the cited Kátai hypothesis DELETED, end to end

`TwoPointGramDiagonal.lean` proved `conjC1_of_delange_pairDecorr`: `ConjC1` from Delange's theorem
plus the canonical node `PairDecorr`, with the Daboussi–Kátai orthogonality criterion no longer a
hypothesis (it is `katai_mean_sq`, applied along the diagonal cutoff `exists_slow_cutoff`).

This file pushes that all the way down the repo's existing proof direction

```
PairDecorr  ⟸ PairDecouple   (SwingC1Decouple.pairDecorr_of_decouple)
PairDecouple ⟸ LargeDecay    (PairDecoupleSplit.pairDecouple_of_largeDecay)
LargeDecay  ⟸ ShiftCorrSmall (PairDecoupleVdC.largeDecay_of_shiftCorr)
ShiftCorrSmall ⟺ MultiElliott (PairDecoupleElliott.shiftCorrSmall_iff_multiElliott)
```

so every headline of the swing loses its `KataiOrthogonality` hypothesis:

| this file | supersedes | remaining hypotheses |
|---|---|---|
| `conjC1_of_delange_decouple` | `conjC1_of_delange_katai_decouple` | Delange + `PairDecouple` |
| `conjC1_of_delange_largeDecay` | — | Delange + `LargeDecay` |
| `conjC1_of_delange_shiftCorr` | — | Delange + `ShiftCorrSmall` |
| `conjC1_of_delange_multiElliott` | `conjC1_of_delange_katai_multiElliott` | Delange + `MultiElliott` |

**What the ledger now says.**  `ConjC1` rests on exactly two inputs, and no others:

* `DelangeMean` — 🟡 PROVEN (Delange 1969 / Selberg–Delange), project-scale to formalise;
* `MultiElliott` — 🔴 OPEN (Elliott's conjecture for `4K(R)` linear forms, `K(R) → ∞`; open even
  in logarithmic average), and by `shiftCorrSmall_iff_multiElliott` it is *equivalent* to the leaf
  this route must clear, so it is not merely sufficient.

That 🔴 is honest rather than straying: C1 is a *conjecture* in the source, so measuring its depth
as one named open problem is the deliverable, not a defect.  `TwoPointGramDiagonal.lean` records
the shorter equivalent form of the same crux: `PairDecorr b t ↔ ∀ p ≠ q, TwoPointWeighted b p q t`
(`pairDecorr_iff_twoPointWeighted`), a **two**-point weighted Elliott correlation at natural
density whose unweighted shadow is Tao 2016 in logarithmic average.  So the two routes bracket the
crux: `MultiElliott` (`4K` forms, no weight) and `TwoPointWeighted` (2 forms, weighted) are both
equivalent to it.
-/

namespace NormalNumbers.CastingOut

/-- **`conjC1_of_delange_katai_decouple` WITH THE CITED KÁTAI HYPOTHESIS DELETED.**  `ConjC1` from
Delange's theorem plus `PairDecouple` — the assertion that the large-prime remainder of the pair
difference equidistributes in progressions to the small-prime modulus (leaf (D)).  Every other
ingredient, including the periodic model `Π_{r≤P} pairLocalFactor → 0` and now the Kátai/BSZ
step, is a theorem of this development. -/
theorem conjC1_of_delange_decouple
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hDc : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecouple b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 := by
  refine conjC1_of_delange_pairDecorr hD (fun b hb m hm hdvd => ?_)
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hmR : ((m : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  exact pairDecorr_of_decouple b (by omega) (((m : ℤ) : ℝ) / b)
    (div_ne_zero hmR (ne_of_gt hbpos)) (hDc b hb m hm hdvd)

/-- `ConjC1` from Delange plus `LargeDecay`, Kátai-free. -/
theorem conjC1_of_delange_largeDecay
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hL : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → LargeDecay b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_decouple hD fun b hb m hm hdvd p q hp hq hpq =>
    pairDecouple_of_largeDecay b p q _ (hL b hb m hm hdvd p q hp hq hpq)

/-- `ConjC1` from Delange plus `ShiftCorrSmall`, Kátai-free. -/
theorem conjC1_of_delange_shiftCorr
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hS : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ShiftCorrSmall b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_largeDecay hD fun b hb m hm hdvd p q hp hq hpq =>
    largeDecay_of_shiftCorr b p q _ (hS b hb m hm hdvd p q hp hq hpq)

/-- **THE SWING, KÁTAI-FREE, WITH THE OPEN LEAF NAMED.**  `ConjC1` follows from ONE known theorem
(Delange) and ONE open conjecture (`MultiElliott`), and by `shiftCorrSmall_iff_multiElliott` the
conjecture is equivalent to the leaf, not merely sufficient for it.  This supersedes
`conjC1_of_delange_katai_multiElliott`, which additionally cited `KataiOrthogonality`. -/
theorem conjC1_of_delange_multiElliott
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hME : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliott b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_shiftCorr hD fun b hb m hm hdvd p q hp hq hpq =>
    shiftCorrSmall_of_multiElliott b (by omega) p q _ (hME b hb m hm hdvd p q hp hq hpq)

end NormalNumbers.CastingOut
