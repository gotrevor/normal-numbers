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

/-! ### The swing, recomposed: `ConjC1 ⟸ Kátai + Delange + MultiElliott`

This is the kickoff's item 3.  All three inputs are now precise, literature-checkable statements:

* `KataiOrthogonality` — the Daboussi–Kátai / Bourgain–Sarnak–Ziegler orthogonality criterion
  (a known theorem; a mathlib-scale formalization of its own).
* `DelangeMean` — `(1/N) Σ_{n ≤ N} e(t·ω(n)) → 0` for `t = m/b`, `b ∤ m`: Delange /
  Selberg–Delange (a known theorem).
* `MultiElliott` — Elliott's conjecture for a growing number of linear forms: OPEN.
-/

/-- **The C1 swing, with the open leaf named.**  `ConjC1` follows from two known theorems and
one open conjecture, and by `shiftCorrSmall_iff_multiElliott` the third input is not merely
sufficient but *equivalent* to the leaf this route must clear. -/
theorem conjC1_of_delange_katai_multiElliott (hDK : KataiOrthogonality)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hME : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliott b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_katai_decouple hDK hD fun b hb m hm hdvd p q hp hq hpq =>
    pairDecouple_of_largeDecay b p q _ (largeDecay_of_shiftCorr b p q _
      (shiftCorrSmall_of_multiElliott b (by omega) p q _ (hME b hb m hm hdvd p q hp hq hpq)))

/-! ### The shorter route: no prime cut at all -/

/-- `PairShiftCorr` is `ShiftCorrSmall` at the empty cut: the van der Corput route needs no
prime cut, no periodic model and no primorial. -/
lemma pairShiftCorr_of_shiftCorrSmall (b p q : ℕ) (t : ℝ) (h : ShiftCorrSmall b p q t) :
    PairShiftCorr b p q t := by
  intro j j' hjj
  have h0 := h 0 0 j j' hjj
  rwa [largeProg_zero] at h0

/-- **`PairDecorr` from `MultiElliott` with no prime cut.** -/
theorem pairDecorr_of_multiElliott (b : ℕ) (hb : 2 ≤ b) (t : ℝ)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliott b p q t) : PairDecorr b t :=
  pairDecorr_of_pairShiftCorr b t fun p q hp hq hpq =>
    pairShiftCorr_of_shiftCorrSmall b p q t
      (shiftCorrSmall_of_multiElliott b hb p q t (h p q hp hq hpq))

/-- **`PairDecorr` from the MINIMAL leaf.**  `PairMultiElliott` asks for the `4K`-point
correlation only along `ℤ` itself — no small-prime modulus, no residue class. -/
theorem pairDecorr_of_pairMultiElliott (b : ℕ) (hb : 2 ≤ b) (t : ℝ)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairMultiElliott b p q t) : PairDecorr b t :=
  pairDecorr_of_pairShiftCorr b t fun p q hp hq hpq =>
    pairShiftCorr_of_pairMultiElliott b hb p q t (h p q hp hq hpq)

/-- **The C1 swing on the MINIMAL leaf.**  The weakest form of the conditional theorem this
development reaches: `ConjC1` from two known theorems plus a `4K`-point Elliott correlation in
ONE variable.  Strictly weaker hypothesis than `conjC1_of_delange_katai_multiElliott`, which in
turn is strictly weaker than the `PairDecouple` route
(`pairMultiElliott_of_multiElliott`). -/
theorem conjC1_of_delange_katai_pairMultiElliott (hDK : KataiOrthogonality)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hME : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairMultiElliott b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_katai hDK hD fun b hb m hm hdvd =>
    pairDecorr_of_pairMultiElliott b (by omega) _ (hME b hb m hm hdvd)

end NormalNumbers.CastingOut
