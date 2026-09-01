/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickedOrbit

/-!
# `e` enters the kick machine: the factorial-threshold dichotomy (N3) 🌿

Companion to `docs/new-conjectures-2026-08-29.md` §N3 and the probe
`experiments/e_binary_runs.py` (200 000 bits, ran green 2026-08-29).  The ln-2 and π
instances of the kicked-orbit dichotomy (`LnTwoRuns.lean`, `PiBBP.lean`) are BBP-locked:
their surrogates come from a base-aligned geometric series.  `e` has no BBP formula, but
its series `e = Σ 1/k!` has **factorial thresholds**, and splitting at

  `M = eSplit b n := min {m : bⁿ < (m+1)!}`

gives, in EVERY base `b`, a rational surrogate and a trapped scaled tail:

* **surrogate** `eSurrogate b n = fract (bⁿ · A(M)/M!)` with the integer numerator
  `A(M) = eNum M = Σ_{i ≤ M} M!/i!` (OEIS A000522; `eNum_succ`: `A(M+1) = (M+1)A(M) + 1`,
  so the numerators are rigid — periodic modulo every prime — where ln 2's harmonic
  numerators are the acknowledged wall);
* **tail bracket** `eLo b n ≤ bⁿ·(e − A(M)/M!) ≤ eHi b n` with
  `eLo = bⁿ/(M+1)! ∈ [1/(M+1), 1)` and `eHi = eLo·(M+2)/(M+1) < (M+2)/(M+1)`
  (`eTail_ge`, `eTail_le` from mathlib's `Real.exp_bound'`; the split makes the bracket
  ratio `1 + 1/(M+1)`, i.e. the tail is known to relative precision `1/M`).

Because the scaled tail can exceed `1`, the sliver is a MOVING one: the dichotomy cores
`window_of_fract_small` / `window_of_fract_large` (generalising `KickedOrbit`'s
`top_sliver_of_fract_*` to `hi < 2`) place the surrogate in a window of width
`< 1/(M+1) + b⁻ᵏ` around `1 − τ` or in a top sliver of width `< 1/(M+1)`.

**The dichotomy** (`eSurrogate_window_of_zeroRun` / `_of_maxRun`, unconditional): a run of
`k` zeros (or `k` top digits `b − 1`) of `e` at position `n` in base `b` with
`bᵏ > eSplit b n + 1` — threshold `≈ log_b n − log_b log n`, BELOW ln 2's `log₂(2(n+1))` —
pins `eSurrogate b n` to one of those two explicit thin windows.  All-base, elementary,
sorry-free; trust triple.

**The Diophantine cap** (`eRun_le_of_irrExpLe`, `eRun_le_of_exponentTwo`): the frozen
CITED-class node `EIrrationalityExponentTwo` (`μ(e) = 2`, Euler's continued fraction) caps
every such run at `(1 + ε)·n` from some position on — the e-gap is `(1+ε)n` vs
`log_b n`, the same wall shape as ln 2 with both sides tighter (`μ(ln 2)` is only known
`≤ 3.57`).  Hypothesis-not-axiom discipline throughout.

Odds (from the N3 note): structure theorems new as stated ~75% (no BBP ⇒ no
Bailey–Crandall-descendant coverage; a sweep of the "binary digits of e" literature is
owed before any outward claim).  Not done here: the rigidity `A(M) ≡ A(M mod p) (mod p)`,
the exclusion node `EDerangementMiss`, and the factorial-kick class (`e^{1/q}`, `cosh 1`, …).
-/

namespace NormalNumbers

open Finset Nat

/-! ### The factorial split -/

theorem exists_factorial_gt (N : ℕ) : ∃ m : ℕ, N < (m + 1).factorial :=
  ⟨N, lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.self_le_factorial (N + 1))⟩

/-- `eSplit b n = min {m : bⁿ < (m+1)!}` — the factorial threshold at which the tail of the
series for `e`, scaled by `bⁿ`, first drops below `1`. -/
noncomputable def eSplit (b n : ℕ) : ℕ := Nat.find (exists_factorial_gt (b ^ n))

theorem pow_lt_factorial_eSplit (b n : ℕ) : b ^ n < (eSplit b n + 1).factorial :=
  Nat.find_spec (exists_factorial_gt (b ^ n))

theorem factorial_eSplit_le_pow (b n : ℕ) (hb : 1 ≤ b) : (eSplit b n).factorial ≤ b ^ n := by
  rcases Nat.eq_zero_or_pos (eSplit b n) with h | h
  · rw [h, Nat.factorial_zero]; exact Nat.one_le_pow _ _ hb
  · have hmin := Nat.find_min (exists_factorial_gt (b ^ n))
      (show eSplit b n - 1 < eSplit b n by omega)
    push Not at hmin
    have : eSplit b n - 1 + 1 = eSplit b n := by omega
    rwa [this] at hmin

/-! ### The series for `e`, its partial sums and tails -/

/-- Partial sum of the series for `e` through `1/M!`. -/
noncomputable def ePartial (M : ℕ) : ℝ := ∑ i ∈ range (M + 1), 1 / (i.factorial : ℝ)

/-- The tail `e − Σ_{i ≤ M} 1/i!`. -/
noncomputable def eTail (M : ℕ) : ℝ := Real.exp 1 - ePartial M

/-- The integer numerator `A(M) = Σ_{i ≤ M} M!/i!` (OEIS A000522): `ePartial M = A(M)/M!`. -/
def eNum (M : ℕ) : ℕ := ∑ i ∈ range (M + 1), M.factorial / i.factorial

theorem ePartial_eq_eNum_div (M : ℕ) : ePartial M = (eNum M : ℝ) / (M.factorial : ℝ) := by
  unfold ePartial eNum
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
  have hM : (M.factorial : ℝ) ≠ 0 := by positivity
  have hi' : (i.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `A(M+1) = (M+1)·A(M) + 1`. -/
theorem eNum_succ (M : ℕ) : eNum (M + 1) = (M + 1) * eNum M + 1 := by
  unfold eNum
  rw [Finset.sum_range_succ _ (M + 1), Nat.div_self (Nat.factorial_pos _), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (by omega))]

/-- **Tail floor**: `eTail M ≥ 1/(M+1)!` (the next term; all terms positive). -/
theorem eTail_ge (M : ℕ) : 1 / ((M + 1).factorial : ℝ) ≤ eTail M := by
  have h := Real.sum_le_exp_of_nonneg (zero_le_one) (M + 2)
  rw [Finset.sum_range_succ] at h
  simp only [one_pow] at h
  unfold eTail ePartial
  linarith

/-- **Tail cap**: `eTail M ≤ (M+2)/((M+1)!·(M+1))` (mathlib's `Real.exp_bound'`). -/
theorem eTail_le (M : ℕ) :
    eTail M ≤ ((M : ℝ) + 2) / (((M + 1).factorial : ℝ) * ((M : ℝ) + 1)) := by
  have h := Real.exp_bound' (zero_le_one) (le_refl (1 : ℝ)) (n := M + 1) (by omega)
  simp only [one_pow, one_mul] at h
  unfold eTail ePartial
  push_cast at h
  have e : ((M : ℝ) + 1 + 1) / (((M + 1).factorial : ℝ) * ((M : ℝ) + 1))
      = ((M : ℝ) + 2) / (((M + 1).factorial : ℝ) * ((M : ℝ) + 1)) := by ring
  linarith

theorem eTail_pos (M : ℕ) : 0 < eTail M :=
  lt_of_lt_of_le (by positivity) (eTail_ge M)

/-! ### The scaled tail bracket at the factorial split -/

/-- The lower bracket of the scaled tail: `bⁿ/(M+1)!` with `M = eSplit b n`. -/
noncomputable def eLo (b n : ℕ) : ℝ := (b : ℝ) ^ n / ((eSplit b n + 1).factorial : ℝ)

/-- The upper bracket of the scaled tail: `eLo · (M+2)/(M+1)`. -/
noncomputable def eHi (b n : ℕ) : ℝ :=
  eLo b n * (((eSplit b n : ℝ) + 2) / ((eSplit b n : ℝ) + 1))

/-- The rational surrogate `fract (bⁿ · A(M)/M!)`, `M = eSplit b n`. -/
noncomputable def eSurrogate (b n : ℕ) : ℝ :=
  Int.fract ((b : ℝ) ^ n * ePartial (eSplit b n))

theorem eSurrogate_eq (b n : ℕ) :
    eSurrogate b n
      = Int.fract ((b : ℝ) ^ n * ((eNum (eSplit b n) : ℝ) / ((eSplit b n).factorial : ℝ))) := by
  rw [eSurrogate, ePartial_eq_eNum_div]

theorem eLo_le_scaled_tail (b n : ℕ) : eLo b n ≤ (b : ℝ) ^ n * eTail (eSplit b n) := by
  unfold eLo
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (eTail_ge _) (by positivity)

theorem scaled_tail_le_eHi (b n : ℕ) : (b : ℝ) ^ n * eTail (eSplit b n) ≤ eHi b n := by
  unfold eHi eLo
  set M := eSplit b n
  have h := eTail_le M
  have hb : (0 : ℝ) ≤ (b : ℝ) ^ n := by positivity
  calc (b : ℝ) ^ n * eTail M
      ≤ (b : ℝ) ^ n * (((M : ℝ) + 2) / (((M + 1).factorial : ℝ) * ((M : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h hb
    _ = (b : ℝ) ^ n / ((M + 1).factorial : ℝ) * (((M : ℝ) + 2) / ((M : ℝ) + 1)) := by
        field_simp

theorem one_le_eSplit (b n : ℕ) (hb : 1 ≤ b) : 1 ≤ eSplit b n := by
  by_contra h
  push Not at h
  have h0 : eSplit b n = 0 := by omega
  have := pow_lt_factorial_eSplit b n
  rw [h0] at this
  simp at this
  have := Nat.one_le_pow n b hb
  omega

/-- `eLo ≥ 1/(M+1)`: since `M! ≤ bⁿ`. -/
theorem eLo_ge (b n : ℕ) (hb : 1 ≤ b) : 1 / ((eSplit b n : ℝ) + 1) ≤ eLo b n := by
  unfold eLo
  set M := eSplit b n
  have hM : ((M).factorial : ℝ) ≤ (b : ℝ) ^ n := by
    exact_mod_cast factorial_eSplit_le_pow b n hb
  have hfac : ((M + 1).factorial : ℝ) = ((M : ℝ) + 1) * (M.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [(by positivity : (0 : ℝ) < (M.factorial : ℝ)).le, hM,
    (Nat.cast_nonneg M : (0:ℝ) ≤ M)]

/-- `eLo < 1`: since `bⁿ < (M+1)!`. -/
theorem eLo_lt_one (b n : ℕ) : eLo b n < 1 := by
  unfold eLo
  rw [div_lt_one (by positivity)]
  exact_mod_cast pow_lt_factorial_eSplit b n

theorem eLo_pos (b n : ℕ) (hb : 1 ≤ b) : 0 < eLo b n :=
  lt_of_lt_of_le (by positivity) (eLo_ge b n hb)

/-- `eHi < (M+2)/(M+1)`. -/
theorem eHi_lt (b n : ℕ) (hb : 1 ≤ b) :
    eHi b n < ((eSplit b n : ℝ) + 2) / ((eSplit b n : ℝ) + 1) := by
  unfold eHi
  have h1 := eLo_lt_one b n
  have h0 := eLo_pos b n hb
  have hq : 0 < ((eSplit b n : ℝ) + 2) / ((eSplit b n : ℝ) + 1) := by positivity
  nlinarith

theorem eHi_lt_two (b n : ℕ) (hb : 1 ≤ b) : eHi b n < 2 := by
  refine lt_of_lt_of_le (eHi_lt b n hb) ?_
  rw [div_le_iff₀ (by positivity)]
  have := (Nat.cast_nonneg (eSplit b n) : (0:ℝ) ≤ _)
  linarith

/-! ### The moving-sliver cores -/

/-- **Zero-side moving-sliver core.**  If `fract (u + τ) < ε` with `τ ∈ [lo, hi]`,
`ε < lo` and `hi < 2`, then `u` lies in the window `[1 − hi, 1 − lo + ε)` below the
wrap point, or in the top sliver `[2 − hi, 1)`. -/
theorem window_of_fract_small {u τ lo hi ε : ℝ}
    (hu0 : 0 ≤ u) (hlo : lo ≤ τ) (hτhi : τ ≤ hi)
    (hε : ε < lo) (hfr : Int.fract (u + τ) < ε) :
    (1 - hi ≤ u ∧ u < 1 - lo + ε) ∨ 2 - hi ≤ u := by
  have hτ0 : 0 ≤ τ := by linarith [Int.fract_nonneg (u + τ)]
  rcases lt_or_ge (u + τ) 1 with h1 | h1
  · exfalso
    rw [Int.fract_eq_self.mpr ⟨by linarith, h1⟩] at hfr
    linarith
  rcases lt_or_ge (u + τ) 2 with h2 | h2
  · left
    have hfr2 : Int.fract (u + τ) = u + τ - 1 :=
      Int.fract_eq_iff.mpr ⟨by linarith, by linarith, ⟨1, by push_cast; ring⟩⟩
    rw [hfr2] at hfr
    constructor <;> linarith
  · right
    linarith

/-- **Max-side moving-sliver core.**  If `1 − ε ≤ fract (u + τ)` with `τ ∈ [lo, hi]`,
`ε < lo` and `hi + ε ≤ 2`, then `u ∈ [1 − hi − ε, 1 − lo)` or `u ≥ 2 − hi − ε`. -/
theorem window_of_fract_large {u τ lo hi ε : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hlo : lo ≤ τ) (hτhi : τ ≤ hi) (hhi : hi + ε ≤ 2)
    (hε : ε < lo) (hfr : 1 - ε ≤ Int.fract (u + τ)) :
    (1 - hi - ε ≤ u ∧ u < 1 - lo) ∨ 2 - hi - ε ≤ u := by
  have hε0 : 0 < ε := by
    have := Int.fract_lt_one (u + τ); linarith
  have hτ0 : 0 ≤ τ := by linarith
  rcases lt_or_ge (u + τ) 1 with h1 | h1
  · left
    rw [Int.fract_eq_self.mpr ⟨by linarith, h1⟩] at hfr
    constructor <;> linarith
  rcases lt_or_ge (u + τ) 2 with h2 | h2
  · right
    have hfr2 : Int.fract (u + τ) = u + τ - 1 :=
      Int.fract_eq_iff.mpr ⟨by linarith, by linarith, ⟨1, by push_cast; ring⟩⟩
    rw [hfr2] at hfr
    linarith
  · exfalso
    have hfr3 : Int.fract (u + τ) = u + τ - 2 :=
      Int.fract_eq_iff.mpr ⟨by linarith, by linarith, ⟨2, by push_cast; ring⟩⟩
    rw [hfr3] at hfr
    linarith

/-! ### The e-dichotomy -/

/-- **Zero-run dichotomy for `e` in base `b`** (the factorial-kick machine).  A run of `k`
zeros at position `n` with `bᵏ > M + 1` (`M = eSplit b n`) forces the rational surrogate
`eSurrogate b n = fract (bⁿ·A(M)/M!)` into the moving window
`[1 − eHi, 1 − eLo + b⁻ᵏ)` — of width `< 1/(M+1) + b⁻ᵏ` — or into the top sliver
`[2 − eHi, 1)` of width `< 1/(M+1)`. -/
theorem eSurrogate_window_of_zeroRun {b : ℕ} (hb : 2 ≤ b) {n k : ℕ}
    (hk : (eSplit b n : ℝ) + 1 < (b : ℝ) ^ k)
    (h : OccursAt b (Real.exp 1) (List.replicate k 0) n) :
    (1 - eHi b n ≤ eSurrogate b n ∧ eSurrogate b n < 1 - eLo b n + 1 / (b : ℝ) ^ k) ∨
      2 - eHi b n ≤ eSurrogate b n := by
  have hb1 : 1 ≤ b := by omega
  rw [occursAt_replicate_zero_iff' b hb, orbit_eq_fract_add_tail b _ (ePartial (eSplit b n)) n] at h
  have hε : 1 / (b : ℝ) ^ k < eLo b n :=
    lt_of_lt_of_le (one_div_lt_one_div_of_lt (by positivity) hk) (eLo_ge b n hb1)
  exact window_of_fract_small (Int.fract_nonneg _)
    (eLo_le_scaled_tail b n) (scaled_tail_le_eHi b n) hε h.2

/-- **Max-run dichotomy for `e` in base `b`**: a run of `k` top digits `b − 1` at position
`n` with `bᵏ > M + 1` forces the surrogate into `[1 − eHi − b⁻ᵏ, 1 − eLo)` or
`[2 − eHi − b⁻ᵏ, 1)`. -/
theorem eSurrogate_window_of_maxRun {b : ℕ} (hb : 2 ≤ b) {n k : ℕ}
    (hk : (eSplit b n : ℝ) + 1 < (b : ℝ) ^ k)
    (h : OccursAt b (Real.exp 1) (List.replicate k (b - 1)) n) :
    (1 - eHi b n - 1 / (b : ℝ) ^ k ≤ eSurrogate b n ∧ eSurrogate b n < 1 - eLo b n) ∨
      2 - eHi b n - 1 / (b : ℝ) ^ k ≤ eSurrogate b n := by
  have hb1 : 1 ≤ b := by omega
  rw [occursAt_replicate_max_iff b hb, orbit_eq_fract_add_tail b _ (ePartial (eSplit b n)) n] at h
  have hM1 : (1 : ℝ) ≤ (eSplit b n : ℝ) := by exact_mod_cast one_le_eSplit b n hb1
  have hε : 1 / (b : ℝ) ^ k < eLo b n :=
    lt_of_lt_of_le (one_div_lt_one_div_of_lt (by positivity) hk) (eLo_ge b n hb1)
  have hε' : 1 / (b : ℝ) ^ k < 1 / ((eSplit b n : ℝ) + 1) :=
    one_div_lt_one_div_of_lt (by positivity) hk
  have hsum : eHi b n + 1 / (b : ℝ) ^ k ≤ 2 := by
    have h1 := eHi_lt b n hb1
    have h2 : ((eSplit b n : ℝ) + 2) / ((eSplit b n : ℝ) + 1) + 1 / ((eSplit b n : ℝ) + 1) ≤ 2 := by
      rw [← add_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  exact window_of_fract_large (Int.fract_nonneg _) (Int.fract_lt_one _)
    (eLo_le_scaled_tail b n) (scaled_tail_le_eHi b n) hsum hε h.1

/-! ### The Diophantine cap: runs are at most `(μ − 1 + ε)·n` -/

/-- **Irrationality-exponent interface for `e`**: `μ(e) ≤ μ`, in the effective form every
run-cap theorem consumes — for every `ε > 0`, all but finitely many denominators `q` satisfy
`|e − p/q| ≥ q^{−(μ+ε)}` for every integer `p`. -/
def EIrrExpLe (μ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
    1 / (q : ℝ) ^ (μ + ε) ≤ |Real.exp 1 - (p : ℝ) / (q : ℝ)|

/-- **Node (frozen, CITED-class): the irrationality exponent of `e` is `2`.**  Classical,
from Euler's continued fraction `e = [2; 1, 2, 1, 1, 4, 1, 1, 6, …]` whose partial quotients
grow only linearly (so `|e − p/q| ≫ 1/(q² log q)`); an explicit effective statement is in
C. S. Davis, *Rational approximations to e*, J. Austral. Math. Soc. Ser. A 25 (1978) —
tier S: cited from memory of the literature, PDF not held, reference to be verified before any
outward use.  Taken as a hypothesis (never an axiom) by the cap below. -/
def EIrrationalityExponentTwo : Prop := EIrrExpLe 2

/-- A run of `k` zeros or `k` top digits at position `n` of `e` in base `b` makes
`p/bⁿ` a `b^{−(n+k)}`-approximation of `e` for some integer `p`. -/
theorem exists_int_approx_of_run {b : ℕ} (hb : 2 ≤ b) {n k : ℕ}
    (h : OccursAt b (Real.exp 1) (List.replicate k 0) n ∨
      OccursAt b (Real.exp 1) (List.replicate k (b - 1)) n) :
    ∃ p : ℤ, |Real.exp 1 - (p : ℝ) / (b : ℝ) ^ n| ≤ 1 / (b : ℝ) ^ (n + k) := by
  have hbpos : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  set y := Real.exp 1 * (b : ℝ) ^ n with hy
  have hfr : orbit b (Real.exp 1) n = Int.fract y := rfl
  have key : ∀ p : ℤ, |y - p| ≤ 1 / (b : ℝ) ^ k →
      |Real.exp 1 - (p : ℝ) / (b : ℝ) ^ n| ≤ 1 / (b : ℝ) ^ (n + k) := by
    intro p hp
    have e1 : Real.exp 1 - (p : ℝ) / (b : ℝ) ^ n = (y - p) / (b : ℝ) ^ n := by
      rw [hy]; field_simp
    rw [e1, abs_div, abs_of_pos hbpos, div_le_iff₀ hbpos, pow_add]
    calc |y - (p : ℝ)| ≤ 1 / (b : ℝ) ^ k := hp
      _ = 1 / ((b : ℝ) ^ n * (b : ℝ) ^ k) * (b : ℝ) ^ n := by field_simp
  rcases h with h | h
  · rw [occursAt_replicate_zero_iff' b hb, hfr] at h
    refine ⟨⌊y⌋, key _ ?_⟩
    rw [Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg y)]
    exact h.2.le
  · rw [occursAt_replicate_max_iff b hb, hfr] at h
    refine ⟨⌊y⌋ + 1, key _ ?_⟩
    have e2 : y - ((⌊y⌋ + 1 : ℤ) : ℝ) = Int.fract y - 1 := by
      rw [Int.fract]; push_cast; ring
    rw [e2, abs_of_nonpos (by linarith [Int.fract_lt_one y])]
    linarith [h.1]

/-- **The Diophantine run cap** (wiring edge): `μ(e) ≤ μ` caps every zero-run and top-digit
run of `e` in base `b` at length `(μ − 1 + ε)·n` from some position on. -/
theorem eRun_le_of_irrExpLe {b : ℕ} (hb : 2 ≤ b) {μ : ℝ} (h : EIrrExpLe μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ k : ℕ,
      (OccursAt b (Real.exp 1) (List.replicate k 0) n ∨
        OccursAt b (Real.exp 1) (List.replicate k (b - 1)) n) →
      (k : ℝ) ≤ (μ - 1 + ε) * n := by
  obtain ⟨q₀, hq⟩ := h ε hε
  refine ⟨q₀, fun n hn k hrun => ?_⟩
  obtain ⟨p, hp⟩ := exists_int_approx_of_run hb hrun
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by linarith
  have hnq : q₀ ≤ b ^ n :=
    le_trans hn (Nat.lt_pow_self (by omega : 1 < b) |>.le)
  have hlow := hq p (b ^ n) hnq
  push_cast at hlow
  have hle : 1 / ((b : ℝ) ^ n) ^ (μ + ε) ≤ 1 / (b : ℝ) ^ (n + k) := hlow.trans hp
  rw [one_div_le_one_div (by positivity) (by positivity)] at hle
  -- rewrite both sides as `b ^ (real exponent)`
  have e1 : ((b : ℝ) ^ n) ^ (μ + ε) = (b : ℝ) ^ ((n : ℝ) * (μ + ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]
  have e2 : (b : ℝ) ^ (n + k) = (b : ℝ) ^ (((n + k : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
  rw [e1, e2] at hle
  have := (Real.rpow_le_rpow_left_iff hb1).mp hle
  push_cast at this
  nlinarith

/-- Closed form at `μ = 2`: every run of `e` in base `b` at position `n` has length at most
`(1 + ε)·n` from some position on — the sharpest linear run cap the exponent allows. -/
theorem eRun_le_of_exponentTwo {b : ℕ} (hb : 2 ≤ b) (h : EIrrationalityExponentTwo) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ k : ℕ,
      (OccursAt b (Real.exp 1) (List.replicate k 0) n ∨
        OccursAt b (Real.exp 1) (List.replicate k (b - 1)) n) →
      (k : ℝ) ≤ (1 + ε) * n := by
  obtain ⟨n₀, hn₀⟩ := eRun_le_of_irrExpLe hb h hε
  refine ⟨n₀, fun n hn k hrun => ?_⟩
  have := hn₀ n hn k hrun
  linarith

end NormalNumbers
