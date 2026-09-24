import NormalNumbers.PairDecoupleElliott

/-!
# PairDecouple — the PROOF direction

The only open input of `conjC1_of_delange_katai_decouple` (C1 swing).  Exactly the hypothesis
`hDc` there.  A sibling worktree (`wip/pd-refute`) attacks the negation.

## The chain, as it now stands

```
pairDecouple_all   ⟸ largeDecay_all        (PairDecoupleSplit.lean, van der Corput)
largeDecay_all     ⟸ shiftCorr_all         (PairDecoupleVdC.lean)
shiftCorr_all      ⟺ multiElliott_all      (PairDecoupleElliott.lean)   ← THE SINGLE OPEN LEAF
```

The last step is an **equivalence** (`shiftCorrSmall_iff_multiElliott`), so nothing has been
weakened or given away: the crux of the ratified target *is* Elliott's conjecture for a growing
number of linear forms.  `MultiElliott` is stated in `PairDecoupleElliott.lean`; `phase_digitTrunc`
(`PairDecoupleDigits.lean`) exhibits it as a `4K`-point correlation of the non-pretentious
multiplicative functions `ζ_k^ω = e(t·b^{−(k+1)})^ω`.
-/

namespace NormalNumbers.CastingOut

/-- **THE OPEN LEAF, NAMED.**  Elliott's conjecture for `4K(R)` linear forms, `K(R) → ∞`.

For the frequency `t = m/b` the phase of the pair difference factors (`phase_digitTrunc`) into
`∏_{k<K} ζ_k^{ω(·+1+k)}·conj ζ_k^{ω(·+1+k)}` with `ζ_k = e(m/b^{k+2})` a nontrivial root of
unity, so each factor is the multiplicative function `ζ_k^ω`, which is non-pretentious
(`Re ζ_k < 1`, so `Σ_r (1 − Re(ζ_k χ̄(r) r^{−iθ}))/r = ∞` for every `χ`, `θ`).

State of the art for this correlation:

* **one form** — `Σ_{n ≤ x} ζ^{ω(n)} ≪ x (log x)^{Re ζ − 1} = o(x)`: Selberg–Delange, classical.
* **two forms** — `Σ_{n ≤ x} g₁(a₁n+b₁) g₂(a₂n+b₂) = o(x)` in *logarithmic* average for
  non-pretentious `g_i`: Tao, *The logarithmically averaged Chowla and Elliott conjectures for
  two-point correlations*, Forum of Mathematics Pi **4** (2016).
* **`K ≥ 2` forms with `K → ∞`** — OPEN, even in logarithmic average.  This is what the swing
  needs, because `ω` is unbounded: the digits beyond `K` carry mass `≍ b^{−K}·√(log log R)`, so
  `K` must grow (`K(R) ≍ log_b log log R` suffices with the sharp mean of `ω`).

⚠️ Deliberately a `sorry`, not an `axiom`: house style, and this is a *conjecture*, not a cited
theorem.  `shiftCorrSmall_iff_multiElliott` certifies that discharging it is necessary as well as
sufficient — there is no cheaper route through this leaf. -/
theorem multiElliott_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliott b p q (((m : ℤ) : ℝ) / b) := by
  sorry

/-- **THE SUCCESSOR CRUX.**  The large-prime remainder of the pair difference `θ_{pn} − θ_{qn}`
decorrelates from its own shifts along every progression to the small-prime modulus
`Q = Π_{r ≤ P} r`.  Equivalent to `multiElliott_all` by `shiftCorrSmall_iff_multiElliott`. -/
theorem shiftCorr_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ShiftCorrSmall b p q (((m : ℤ) : ℝ) / b) := by
  intro b hb m hm hdvd p q hp hq hpq
  exact shiftCorrSmall_of_multiElliott b (by omega) p q _
    (multiElliott_all b hb m hm hdvd p q hp hq hpq)

theorem largeDecay_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → LargeDecay b p q (((m : ℤ) : ℝ) / b) := by
  intro b hb m hm hdvd p q hp hq hpq
  exact largeDecay_of_shiftCorr b p q _ (shiftCorr_all b hb m hm hdvd p q hp hq hpq)

theorem pairDecouple_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecouple b p q (((m : ℤ) : ℝ) / b) := by
  intro b hb m hm hdvd p q hp hq hpq
  exact pairDecouple_of_largeDecay b p q _ (largeDecay_all b hb m hm hdvd p q hp hq hpq)

end NormalNumbers.CastingOut
