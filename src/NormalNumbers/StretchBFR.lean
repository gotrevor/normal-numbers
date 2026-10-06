/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentStretch
import Architect

/-!
# The BFR bet: does the stretch count say anything about rationals near `K`?

Ren, 2026-10-05 (`KICKOFF-2026-10-05-stretch-poke-ADDENDUM-bfr.md`).  Four findings, each a
declaration here, so the stretch lane can grind them:

1. **The exact residue count is the covering bound.**  `card_lowResidue_le` (≤ `2^{k+1}` Cantor
   numerators per `q`) is the classical count `card_near_cantor_le`: `K` at scale `1/q` has `2ⁿ`
   pieces, each holding ≤ 4 fractions `p/q`, so `N_K(Q, 1/Q) ≲ Q^{1 + dim K}`, the known trivial
   bound.  The count transfers nothing new to Broderick–Fishman–Reich (Maze, `vacuous`).
2. **`RunEnteringCount` and a Bugeaud–Durand count are siblings.**  BD-type counts see rationals
   near `K` at resolution ≥ the cylinder; `RunEnteringCount` counts rationals within
   `q^{−τ} < 3^{−b}` of the `2^b` discrete endpoints, a measure-zero set.  Neither implies the
   other as stated (Maze, `vacuous`, prose tier).
3. **Inverse Cantor sums cancel numerically.**  `invSumShift` at `A = 0`, `b' = b`: `max_{3∤n}
   |S|/|C|` falls from 0.276 (`b = 6`) to 0.036 (`b = 14`), about `√(log 3^b / |C|)`, while the
   direct Riesz sum stays at 0.466 (`experiments/cantor_inverse_sums.py`).  Frozen as
   `InverseCantorSumBound` for the shifted sets the window count uses; the probe has not tested
   `A ≠ 0`.
4. **Single-sum cancellation is not enough.**  `windowCount_of_inverseSum` gives the window count
   only when `m > b − δ b'`, and `singleSum_insufficient` shows that even square-root saving
   misses every window with `m ≤ b/2`, which is where the binding windows sit (`m ≈ b/τ`).  So
   single-sum cancellation is the wrong tool (Maze, `refuted`).
   ⚠️ **Corrected 2026-10-06:** Ren's conclusion here, "so `RunEnteringCount` needs a bilinear
   estimate", was wrong.  It treated the window as an incidence count (pairs `(P, q)`, which would
   need Kloosterman-type cancellation), but `windowCount` and Borel–Cantelli only need the
   *union* of hitting numerators.  The union is small for an elementary reason: 3-adic Farey
   separation (`CantorExactExponentStretch.padic_sep`, `hit_mass_padic`) pins each hitting
   numerator by about `log₃(|r| q)` low digits plus `v₃(q)` top digits, which proved the stretch
   node for every `μ₀ > 2` (lap 3 of the stretch lane).

**BFR bet, 2026-10-06 (BFR directive lap 1): confidence < 1%.**  Candidate 2 is proved
(`card_cantor_hyperbola_le`, `≲ (RQ)^{log₃ 2}`) and candidate 4 with it (`eq_of_hyperbola_low`,
any base, `q` prime to the base); both are the 3-adic covering bound.  Candidates 1 and 3 reduce,
through `R = δQ3^b`, to the archimedean covering count; a saving (`NKPowerSaving`) needs a Fourier
input, which is Chow–Varjú–Yu (arXiv:2402.18395).  Every route has a Maze row.
-/

open MeasureTheory Filter

namespace NormalNumbers.StretchBFR

open CantorExactExponentStretch

/-- Exponential sum over the inverses mod `3^b` of `A·3^{b'} + P`, `P` a depth-`b'` Cantor
numerator, over the terms prime to 3. -/
noncomputable def invSumShift (b b' A n : ℕ) : ℂ :=
  ∑ P ∈ (cantorInts b').filter (fun P => ¬ 3 ∣ A * 3 ^ b' + P),
    Complex.exp (2 * Real.pi * Complex.I *
      ((((n * (((A * 3 ^ b' + P : ℕ) : ZMod (3 ^ b))⁻¹).val : ℕ) : ℝ) / (3 : ℝ) ^ b : ℝ) : ℂ))

/-- **Inverse Cantor sums have a power saving**, uniformly over prefixes.  Confidence 60% (probe:
`A = 0`, `b' = b ≤ 14` only, consistent with square-root cancellation). -/
def InverseCantorSumBound (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ C : ℝ, ∀ b b' A n : ℕ, b' ≤ b → ¬ 3 ∣ n →
    ‖invSumShift b b' A n‖ ≤ C * 2 ^ b' * (3 : ℝ) ^ (-(δ * b'))

open Classical in
/-- The run-entering window count of `RunEnteringCountAt`, as a function. -/
noncomputable def windowCount (τ : ℝ) (A b b' m : ℕ) : ℕ :=
  ((cantorInts b').filter fun P => ∃ q : ℕ, 3 ^ m ≤ q ∧ q < 3 ^ (m + 1) ∧ ∃ r : ℤ, r ≠ 0 ∧
      |(r : ℝ)| < 3 ^ b * (q : ℝ) ^ (1 - τ) ∧
      ((A * 3 ^ b' + P : ℕ) * q : ℤ) ≡ r [ZMOD 3 ^ b]).card

/-- **From inverse-sum cancellation to the window count.**  Confidence 80%.

English proof.  `P q ≡ r` iff `q ≡ r · P̄`.  Count pairs `(P, r)` with `r P̄ mod 3^b` in the
`q`-interval `I` (length `2·3ᵐ`), expand `1_I` in additive characters mod `3^b`
(`Σ_h |Î(h)| ≲ 3^b log 3^b`), and group `n = h r`: the `h = 0` term is the main term
`2^{b'} · #r · |I| / 3^b ≲ 2^{b'} 3^{(2−τ)m}`, and every other term is an `invSumShift`, bounded
by the hypothesis.  Error `≲ #r · 2^{b'} 3^{−δ b'} · (b + 1)` with `#r ≤ 2·3^{b−(τ−1)m}`. -/
theorem windowCount_of_inverseSum (δ : ℝ) (hS : InverseCantorSumBound δ) (τ : ℝ) (hτ : 2 < τ) :
    ∃ C : ℝ, ∀ A b b' m : ℕ, b' ≤ b → ((τ - 1) * m : ℝ) ≤ b →
      (windowCount τ A b b' m : ℝ) ≤
        C * (2 ^ b' * (3 : ℝ) ^ ((2 - τ) * m) +
          (3 : ℝ) ^ (b - (τ - 1) * m) * 2 ^ b' * (3 : ℝ) ^ (-(δ * b')) * (b + 1)) := by
  sorry

/-- **Single-sum cancellation cannot reach the bottom windows.**  The error term of
`windowCount_of_inverseSum` beats the main term only when `m > b − δ b'`.  With at most
square-root saving (`δ ≤ ½ log₃ 2 < ½`) and `m ≤ b/2`, that fails: `m ≤ b − δ b'`. -/
theorem singleSum_insufficient (δ b b' m : ℝ) (hδ : δ ≤ Real.logb 3 2 / 2)
    (hb' : b' ≤ b) (hb'0 : 0 ≤ b') (hm : m ≤ b / 2) : m ≤ b - δ * b' := by
  have hlog : Real.logb 3 2 < 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    norm_num
  have hδ1 : δ ≤ 1 / 2 := by linarith
  have : δ * b' ≤ b / 2 := by nlinarith
  linarith

open Classical in
/-- **The covering bound.**  For `q ≤ 3ⁿ`, at most `4 · 2ⁿ` fractions `p/q ∈ [0, 1]` lie within
`1/q` of the Cantor set.  Confidence 95%.  English proof: `K` is covered by the `2ⁿ` depth-`n`
intervals of length `3^{−n} ≤ 1/q`; the `1/q`-neighbourhood of each has length `< 3/q`, so holds
at most 4 points of `(1/q)ℤ`.  This is what `card_lowResidue_le` is, in BFR terms. -/
theorem card_near_cantor_le (q n : ℕ) (hq : 0 < q) (hn : q ≤ 3 ^ n) :
    ((Finset.range (q + 1)).filter fun p : ℕ =>
        ∃ x ∈ cantorSet, |x - (p : ℝ) / q| < 1 / q).card ≤ 4 * 2 ^ n := by
  sorry

/-! ### BFR directive (2026-10-06): candidates 2 and 4 -/

/-- **`B`-adic Farey separation for numerators** (candidate 4: any base).  If `P q ≡ r` and
`P' q' ≡ r'` mod `B^b` with `q, q'` prime to `B`, `|r|, |r'| ≤ R`, `q, q' ≤ Q`, and `P, P'` share
their low `j` base-`B` digits where `2RQ < B^j`, then `P = P'`.  No primality of `B` is used:
only `gcd(q q', B) = 1`.  What a composite base loses is the reduction of a general `q` to its
`B`-free part (`q = 3^v q₀` in `hit_mass_padic`), which needs `B` prime (or `q` restricted). -/
theorem eq_of_hyperbola_low (B b j R Q P P' q q' : ℕ) (r r' : ℤ) (hj : j ≤ b)
    (hq : Nat.Coprime q B) (hq' : Nat.Coprime q' B) (hqQ : q ≤ Q) (hq'Q : q' ≤ Q)
    (hr : |r| ≤ R) (hr' : |r'| ≤ R) (hRQ : 2 * R * Q < B ^ j)
    (hP : P < B ^ b) (hP' : P' < B ^ b)
    (h : (P * q : ℤ) ≡ r [ZMOD (B : ℤ) ^ b]) (h' : (P' * q' : ℤ) ≡ r' [ZMOD (B : ℤ) ^ b])
    (hlow : P % B ^ j = P' % B ^ j) : P = P' := by
  have hdj : ((B : ℤ) ^ j) ∣ (P' : ℤ) - P := by
    have := Nat.modEq_iff_dvd.mp hlow; exact_mod_cast this
  have hjb : ((B : ℤ) ^ j) ∣ (B : ℤ) ^ b := pow_dvd_pow _ hj
  set X : ℤ := r * q' - r' * q with hX
  have hXc : (B : ℤ) ^ b ∣ ((P : ℤ) - P') * q * q' - X := by
    have e1 := (Int.ModEq.mul_right (q' : ℤ) h).symm.dvd
    have e2 := (Int.ModEq.mul_right (q : ℤ) h').symm.dvd
    have key : ((P : ℤ) - P') * q * q' - X =
        (P * q * q' - r * q') - (P' * q' * q - r' * q) := by rw [hX]; ring
    rw [key]; exact dvd_sub e1 e2
  have hXd : (B : ℤ) ^ j ∣ X := by
    have h1 : (B : ℤ) ^ j ∣ ((P : ℤ) - P') * q * q' := by
      rw [← dvd_neg] at hdj
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by simpa using hdj) _) _
    have := dvd_sub h1 (hjb.trans hXc)
    simpa using this
  have hXb : |X| < (B : ℤ) ^ j := by
    have hq0 : (0 : ℤ) ≤ q := by positivity
    have hq0' : (0 : ℤ) ≤ q' := by positivity
    have hQ : (q : ℤ) ≤ Q := by exact_mod_cast hqQ
    have hQ' : (q' : ℤ) ≤ Q := by exact_mod_cast hq'Q
    have hR0 : (0 : ℤ) ≤ R := by positivity
    calc |X| ≤ |r| * q' + |r'| * q := by
          rw [hX]; refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hq0']
      _ ≤ R * Q + R * Q := by gcongr
      _ = ((2 * R * Q : ℕ) : ℤ) := by push_cast; ring
      _ < (B : ℤ) ^ j := by exact_mod_cast hRQ
  have hX0 : X = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := hXd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hne hc
    have : (B : ℤ) ^ j ≤ |X| := by
      rw [hc, abs_mul]
      have hBj : (0 : ℤ) ≤ (B : ℤ) ^ j := by positivity
      rw [abs_of_nonneg hBj]
      exact le_mul_of_one_le_right hBj (Int.one_le_abs hc0)
    linarith
  rw [hX0, sub_zero] at hXc
  have hcop : IsCoprime ((B : ℤ) ^ b) ((q : ℤ) * q') := by
    apply IsCoprime.pow_left
    apply IsCoprime.mul_right
    · exact (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hq.symm))
    · exact (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hq'.symm))
  have hd : (B : ℤ) ^ b ∣ (P : ℤ) - P' := by
    rw [mul_assoc] at hXc; exact hcop.dvd_of_dvd_mul_right hXc
  obtain ⟨c, hc⟩ := hd
  have hPr : ((P : ℤ)) < (B : ℤ) ^ b := by exact_mod_cast hP
  have hPr' : ((P' : ℤ)) < (B : ℤ) ^ b := by exact_mod_cast hP'
  have hBpos : (0 : ℤ) < (B : ℤ) ^ b := by
    have : 0 < B ^ b := lt_of_le_of_lt (Nat.zero_le _) hP
    exact_mod_cast this
  have hc0 : c = 0 := by
    by_contra hne
    have : (B : ℤ) ^ b ≤ |(P : ℤ) - P'| := by
      rw [hc, abs_mul, abs_of_pos hBpos]
      exact le_mul_of_one_le_right hBpos.le (Int.one_le_abs hne)
    rw [abs_le] at *; rcases abs_cases ((P : ℤ) - P') with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  rw [hc0, mul_zero, sub_eq_zero] at hc; exact_mod_cast hc

open Classical in
/-- **Restricted-digit modular hyperbola count** (candidate 2, proved).  The Cantor numerators
`P ∈ C_b` with `P q ≡ r (mod 3^b)` for some `q ≤ Q` prime to 3 and `|r| ≤ R` number at most
`2^j` whenever `2RQ < 3^j ≤ 3^b`; that is, `≲ (RQ)^{log₃ 2}`, independent of `b`.

Verdict: this is the 3-adic covering bound.  As 3-adic numbers, the fractions `r/q` with `|r| ≤ R`,
`q ≤ Q` are `(2RQ)^{-1}`-separated, and `C_b` meets each 3-adic ball of radius `3^{-j}` in at most
one point near such a fraction; the archimedean twin is `card_near_cantor_le`.  The lower bound
`R^{log₃ 2}` (take `q = 1`) shows the exponent of `R` is sharp. -/
@[blueprint (title := "Restricted-digit modular hyperbola count")]
theorem card_cantor_hyperbola_le (b j R Q : ℕ) (hj : j ≤ b) (hRQ : 2 * R * Q < 3 ^ j) :
    ((cantorInts b).filter fun P : ℕ => ∃ q : ℕ, q ≤ Q ∧ Nat.Coprime q 3 ∧ ∃ r : ℤ, |r| ≤ R ∧
        (((P : ℤ) * q) ≡ r [ZMOD 3 ^ b])).card ≤ 2 ^ j := by
  set S := (cantorInts b).filter fun P : ℕ => ∃ q : ℕ, q ≤ Q ∧ Nat.Coprime q 3 ∧ ∃ r : ℤ, |r| ≤ R ∧
        (((P : ℤ) * q) ≡ r [ZMOD 3 ^ b])
  have hinj : Set.InjOn (· % 3 ^ j) (S : Set ℕ) := by
    intro P hP P' hP' heq
    simp only [S, Finset.coe_filter, Set.mem_ofPred_eq, cantorInts, Finset.mem_filter,
      Finset.mem_range] at hP hP'
    obtain ⟨⟨hPb, -⟩, q, hqQ, hq, r, hr, h⟩ := hP
    obtain ⟨⟨hPb', -⟩, q', hqQ', hq', r', hr', h'⟩ := hP'
    exact eq_of_hyperbola_low 3 b j R Q P P' q q' r r' hj hq hq' hqQ hqQ' hr hr' hRQ hPb hPb'
      (by exact_mod_cast h) (by exact_mod_cast h') heq
  calc S.card = (S.image (· % 3 ^ j)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (cantorInts j).card := Finset.card_le_card (by
        intro x hx; obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hx
        exact mod_mem_cantorInts hj (Finset.mem_filter.1 hP).1)
    _ ≤ 2 ^ j := card_cantorInts_le j

open Classical in
/-- **Candidate 3 (open node, prior art dominates).**  A power saving over the trivial covering
bound `N_K(Q, δ) ≲ Q δ^{-dim K}` in the regime `Q^{-2} < δ < Q^{-1}`, for rationals `p/q`,
`q ≤ Q`, within `δ` of the middle-third Cantor set.  The 3-adic route gives nothing here: through
`P q ≡ r (mod 3^b)` with `R = δ Q 3^b`, `card_cantor_hyperbola_le` returns `(δ Q² 3^b)^{dim K}`
endpoints, the archimedean covering count again.  Upper bounds of this kind for missing-digit
sets are the subject of Chow–Varjú–Yu, *Counting rationals and diophantine approximation in
missing-digit Cantor sets* (arXiv:2402.18395), via Fourier `ℓ¹` dimension, a mechanism the
separation argument does not contain. -/
def NKPowerSaving : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ Q : ℕ, ∀ δ : ℝ, (Q : ℝ) ^ (-(2 : ℝ)) ≤ δ → δ ≤ (Q : ℝ) ^ (-(1 : ℝ)) →
    (((Finset.Icc 1 Q ×ˢ Finset.range (Q + 1)).filter fun x : ℕ × ℕ =>
        x.2 ≤ x.1 ∧ ∃ y ∈ cantorSet, |y - (x.2 : ℝ) / x.1| < δ).card : ℝ) ≤
      C * Q * δ ^ (-Real.logb 3 2) * (Q : ℝ) ^ (-ε)

end NormalNumbers.StretchBFR
