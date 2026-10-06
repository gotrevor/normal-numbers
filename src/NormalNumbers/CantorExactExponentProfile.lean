/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentStretch

/-!
# The exponent sets the normal profile: `x` is normal to `3ˢt` iff `t > 3^{s(μ₀−1)}`

Ren, 2026-10-06 (`/create`, after the stretch referee).  The stretch points
`x = cantorExpReal μ₀ ω` are normal to every base prime to 3 and to no power of 3; for bases
`b = 3ˢ t` with `s ≥ 1`, `t > 1`, `3 ∤ t`, nothing was claimed
(`CantorExactExponent.not_isNormal_of_three_dvd_of_small` covers only `2 log₃ b < μ₀`).

**Conjecture (frozen here).**  For rational `μ₀ > 2` and almost every `ω`, `x` is normal to base
`b = 3ˢ t` exactly when `t > 3^{s(μ₀−1)}` (`ProfileOK`).  One formula covers all bases: `s = 0`
gives every base prime to 3, and `t = 1` gives no power of 3.  The threshold is power-invariant
(`b ↦ bᵏ` scales `s` and `log t` alike), as normality must be.  It is never attained, because
`3^{s(μ₀−1)}` is an integer prime to 3 only when it is 1.  Examples at `μ₀ ∈ (2, 2.26)`: normal
to 12, 15 and 21, not normal to 6, 18 or 36.  Base 12 switches off at `μ₀ = 1 + log₃ 4 ≈ 2.26`.

**Mechanism: one window, two sides.**  Let the run be `[a, E)`, `E = ⌈μ₀ a⌉`, and write `L = log₃ t`.
* *Not normal* when `μ₀ > 1 + L/s`.  For `j ≥ a/s`, `bʲ P/3^a ∈ ℤ`, so base-`b` digits
  `j ∈ (a/s, E/log₃ b)` are `0`: a zero run of length `≍ a`.  Its block frequency beats
  `b^{−ℓ}` for every `ℓ` (`not_isNormal_of_not_profileOK`, elementary).
* *Normal* when `μ₀ < 1 + L/s`.  The Fourier coefficient of the coin law at `h·bⁿ` sees only the
  ternary places `[sn, (s+L)n]`, where the digits of `h tⁿ` sit.  A run covers that window iff
  `sn ≥ a` and `(s+L)n ≤ μ₀ a`, which is possible iff `μ₀ > 1 + L/s`.  Below the threshold every
  window keeps `≥ a(1 − μ₀ s/(s+L))` free places, linear in `n`, so the Cassels–Schmidt second moment
  (`CantorLiouvilleAll.secondMoment_le_b`, with the orbit of `t` mod `3ᵏ` in place of `b`)
  should go through.  This is `ae_isNormal_of_profileOK` (open node).

So the threshold where the Fourier side breaks is the same threshold where the explicit zero
runs appear.  Known-false sibling: `t = 1` (powers of 3).  There the frequencies' digits are a fixed
word shifted, with no orbit to average over, and the mechanism correctly gives nothing.

Prior art (one search, 2026-10-06): Schmidt (1960) gives sets of normal bases closed under
multiplicative dependence; Becher–Slaman give prescribed simple-normality profiles outside `K`.
We found no profile for points of `K` that depends on the exponent.
-/

open MeasureTheory Filter

namespace NormalNumbers.CantorExactExponentProfile

open CantorLiouville CantorExactExponent CantorExpGeneric Derandomize CantorExactExponentStretch

/-- The profile condition for `b = 3ˢ t` (`s = v₃ b`, `t = b / 3ˢ`): `3^{s(μ₀−1)} < t`. -/
def ProfileOK (μ₀ : ℚ) (b : ℕ) : Prop :=
  (3 : ℝ) ^ ((padicValNat 3 b : ℝ) * ((μ₀ : ℝ) - 1)) < ((b / 3 ^ padicValNat 3 b : ℕ) : ℝ)

/-- Bases prime to 3 always pass. -/
theorem profileOK_of_not_dvd (μ₀ : ℚ) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : ProfileOK μ₀ b := by
  unfold ProfileOK
  rw [padicValNat.eq_zero_of_not_dvd h3]
  simp only [CharP.cast_eq_zero, zero_mul, Real.rpow_zero, pow_zero, Nat.div_one]
  exact_mod_cast hb

/-- Powers of 3 never pass (for `μ₀ ≥ 1`). -/
theorem not_profileOK_three_pow (μ₀ : ℚ) (hμ : 1 ≤ μ₀) (s : ℕ) : ¬ ProfileOK μ₀ (3 ^ s) := by
  unfold ProfileOK
  rw [padicValNat.prime_pow (p := 3) s, Nat.div_self (by positivity)]
  push Not
  have : (0 : ℝ) ≤ (s : ℝ) * ((μ₀ : ℝ) - 1) := by
    have : (1 : ℝ) ≤ μ₀ := by exact_mod_cast hμ
    positivity
  simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) this

/-- **Not normal past the threshold, for every `ω`.**  Confidence 90%.

English proof.  Let `s = v₃ b ≥ 1` (if `s = 0` then `ProfileOK` holds), `b = 3ˢt`, and
`θ = log₃ b / s`; `¬ ProfileOK` with `t ≠ 3^{s(μ₀−1)}` gives `θ < μ₀`.  Along run `k`
(`a = a_k`, `E = ⌈μ₀ a⌉`), `x = P/3^a + ε` with `0 ≤ ε < 3^{−E}`.  For `j ≥ ⌈a/s⌉`,
`bʲP/3^a ∈ ℤ`, so `{bʲx} = bʲε < b^{j}3^{−E}`, and the base-`b` digit `j + 1` is `0` whenever
`b^{j+1} ≤ 3^E`.  So the digits on `(⌈a/s⌉, ⌊E/log₃ b⌋)` vanish, a run of length
`≥ a(μ₀/log₃ b − 1/s) − 2 = c·N`, `c = 1 − θ/μ₀ > 0`, ending at `N = E/log₃ b`.  For any `ℓ`
with `b^{−ℓ} < c/2`, the block `0^ℓ` then has frequency `≥ c/2` at `N`, infinitely often,
contradicting normality.  The `ℓ = 1` case of this argument is `not_isNormal_of_three_dvd_of_small`. -/
theorem not_isNormal_of_not_profileOK (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool) {b : ℕ}
    (hb : 2 ≤ b) (hP : ¬ ProfileOK μ₀ b) : ¬ IsNormal b (cantorExpReal μ₀ ω) := by
  sorry

/-- **Normal below the threshold, a.e.**  Open node; confidence 70% (true), Lean cost a few laps.

English proof (sketch).  For `3 ∤ b` this is `ae_isNormal_of_coprime_three`.  Let `b = 3ˢt` with
`s ≥ 1`, `t > 3^{s(μ₀−1)}`, `L = log₃ t`.
1. *Window.*  In the coin law, the Fourier coefficient at `ξ = h·bᵐ·(bᵈ − 1)` (the pair terms
   of the second moment; `bᵈ − 1` is prime to 3) is a product of `|cos(2πξ/3^{p+1})|` over
   the free places `p`.  Factors with `p + 1 ≤ sm` are 1, and so are factors with `p` beyond the
   top digit of `ξ`.  The window is `[sm, (s+L)m + d log₃ b + O(log |h|)]`.
2. *Free count.*  A run `[a, μ₀a)` covers `[sm, (s+L)m]` only if `μ₀ > 1 + L/s`.  Below the
   threshold, the free places in the window number at least `a(1 − μ₀ s/(s+L)) − O(1)` for the
   worst run, which is linear in `m`.  Earlier runs are negligible because `a_{k+1}/a_k → ∞`.
3. *Digit changes.*  The ternary digits of `ξ` on the window are those of `h(bᵈ−1)tᵐ` shifted
   by `sm`.  As `m` varies, `tᵐ mod 3ᵏ` runs through a subgroup of index `≤ 3^{v₃(t²−1)}`
   (`padicValNat_pow_sub_one_le` for `t`), so the counting of
   `CantorLiouvilleAll.sum_Hf_le_b` applies with `t` in place of `b`.  This gives a summable
   second moment along `CantorLiouville.sched`, and `ae_isNormal_of_secondMoment` concludes.

Sibling check: for `t = 1` step 3 has a trivial orbit, and the frequencies' digits are one word
shifted.  The argument stops there, as it must, since `x` is never normal to a power of 3. -/
theorem ae_isNormal_of_profileOK (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
  sorry

/-- **Headline: the exponent sets the normal profile.**  For every rational `μ₀ > 2` there is a
computable `x ∈ K` with irrationality exponent exactly `μ₀` such that, for every base `b ≥ 2`,
`x` is normal to `b` iff `b = 3ˢt` with `t > 3^{s(μ₀−1)}`.  Confidence 65% (the node above, plus
the derandomizer taking the extra bases: `exists_computable_normal_avoid`'s test family must
include the `3 ∣ b` second moments). -/
theorem exists_computable_mem_cantorSet_irrExponent_normalProfile (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorExpReal μ₀ e) ↔ ProfileOK μ₀ b) := by
  sorry

end NormalNumbers.CantorExactExponentProfile
