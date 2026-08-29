/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickedOrbit

/-!
# π through the kicked-orbit dichotomy (R2, the π instance)

Companion to `docs/alien-review-2026-08-29.md` (transmission 2, move R2) and
`docs/lit-sweep-2026-08-29.md`.  The BBP formula (Bailey–Borwein–Plouffe
1997) writes π as a base-16 BBP-type series, so π's hexadecimal digits ride
a kicked orbit exactly as binary `ln 2` does — with kick `~ c/n²` instead of
`~ c/n`.  Feeding the abstract dichotomy (`KickedOrbit.lean`) the elementary
kick bounds proved here yields **pointwise structure theorems on the hex
digits of π**:

* `bbpKick_ge` / `bbpKick_le`: the scaled BBP kick is trapped,
  `3/(16(j+1)²) ≤ kick_j ≤ 20/(8j+1)²` — elementary, unconditional;
* `piTail_ge` / `piTail_le`: the scaled series tail is trapped,
  `3/(16(n+1)²) ≤ 16ⁿ·(π − sₙ) ≤ 64/(3(8n+1)²)` — conditional on the BBP
  series (the frozen node `PiBBP`);
* **the headlines** `pi_top_sliver_of_zeroRun` / `pi_top_sliver_of_fRun`:
  a run of `k` hex zeros (or hex `F`s) of π at position `n` with
  `16ᵏ > 16(n+1)²/3` — i.e. any run beyond `~2·log₁₆ n` — forces the BBP
  surrogate `fract (16ⁿ·sₙ)` into the top sliver of width `~64/(3(8n+1)²)`.

Reading: super-logarithmic hex-digit runs of π are **not free** — each one
pins the explicit rational surrogate orbit to an exponentially thin window
near the wrap point, at the single position where the run starts.  This is
invisible to measure-level instruments and, per the 2026-08-29 sweep, has
no counterpart in the Bailey–Crandall descendant literature (the only
published sliver-style result is Bailey–Borwein 2012's *converse* bottom-
sliver direction for engineered Stoneham constants).  Lagarias guardrail
respected: the conclusion is forcing-level, never equidistribution-level.

## The frozen node

`PiBBP` (the BBP series itself) is classical mathematics, CITED-class:
Bailey–Borwein–Plouffe, Math. Comp. 66 (1997) 903–913, *On the rapid
computation of various polylogarithmic constants*.  It is taken as a
**hypothesis** by every π theorem here (hypothesis-not-axiom discipline);
its in-house proof — an elementary integral computation — is lane-2 work
that discharges the node.  Everything else in this file is proved outright.
-/

namespace NormalNumbers

/-! ### The BBP series and kick -/

/-- The scaled BBP kick: `4/(8j+1) − 2/(8j+4) − 1/(8j+5) − 1/(8j+6)`. -/
noncomputable def bbpKick (j : ℕ) : ℝ :=
  4 / (8 * (j : ℝ) + 1) - 2 / (8 * (j : ℝ) + 4)
    - 1 / (8 * (j : ℝ) + 5) - 1 / (8 * (j : ℝ) + 6)

/-- The BBP summand for π: `16⁻ʲ · bbpKick j`. -/
noncomputable def bbpTerm (j : ℕ) : ℝ := (1 / 16 ^ j) * bbpKick j

/-- **Node (frozen, CITED-class): the BBP formula**
(Bailey–Borwein–Plouffe 1997).  Classical; lane-2 discharge owed. -/
def PiBBP : Prop := HasSum bbpTerm Real.pi

/-! ### Elementary kick bounds (unconditional) -/

/-- **Kick floor**: `bbpKick j ≥ 3/(16(j+1)²)`. -/
theorem bbpKick_ge (j : ℕ) : 3 / (16 * ((j : ℝ) + 1) ^ 2) ≤ bbpKick j := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hA : (0 : ℝ) < 8 * (j : ℝ) + 1 := by linarith
  have hB : (0 : ℝ) < 8 * (j : ℝ) + 4 := by linarith
  have hC : (0 : ℝ) < 8 * (j : ℝ) + 5 := by linarith
  have hD : (0 : ℝ) < 8 * (j : ℝ) + 6 := by linarith
  have h5 : 1 / (8 * (j : ℝ) + 5) ≤ 1 / (8 * (j : ℝ) + 4) :=
    one_div_le_one_div_of_le hB (by linarith)
  have h6 : 1 / (8 * (j : ℝ) + 6) ≤ 1 / (8 * (j : ℝ) + 4) :=
    one_div_le_one_div_of_le hB (by linarith)
  have hsum : 2 / (8 * (j : ℝ) + 4) + 1 / (8 * (j : ℝ) + 5) + 1 / (8 * (j : ℝ) + 6)
      ≤ 4 / (8 * (j : ℝ) + 4) := by
    have e2 : (2 : ℝ) / (8 * (j : ℝ) + 4) = 2 * (1 / (8 * (j : ℝ) + 4)) := by ring
    have e4 : (4 : ℝ) / (8 * (j : ℝ) + 4) = 4 * (1 / (8 * (j : ℝ) + 4)) := by ring
    rw [e2, e4]
    linarith
  have hdiff : 4 / (8 * (j : ℝ) + 1) - 4 / (8 * (j : ℝ) + 4)
      = 12 / ((8 * (j : ℝ) + 1) * (8 * (j : ℝ) + 4)) := by
    field_simp
    ring
  have hfloor : 3 / (16 * ((j : ℝ) + 1) ^ 2)
      ≤ 12 / ((8 * (j : ℝ) + 1) * (8 * (j : ℝ) + 4)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((j : ℝ))]
  have : 4 / (8 * (j : ℝ) + 1) - 4 / (8 * (j : ℝ) + 4) ≤ bbpKick j := by
    rw [bbpKick]
    linarith
  linarith [hdiff ▸ hfloor]

/-- **Kick ceiling**: `bbpKick j ≤ 20/(8j+1)²`. -/
theorem bbpKick_le (j : ℕ) : bbpKick j ≤ 20 / (8 * (j : ℝ) + 1) ^ 2 := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hA : (0 : ℝ) < 8 * (j : ℝ) + 1 := by linarith
  have hD : (0 : ℝ) < 8 * (j : ℝ) + 6 := by linarith
  have h4 : 2 / (8 * (j : ℝ) + 6) ≤ 2 / (8 * (j : ℝ) + 4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
    linarith
  have h5 : 1 / (8 * (j : ℝ) + 6) ≤ 1 / (8 * (j : ℝ) + 5) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hsum : 4 / (8 * (j : ℝ) + 6)
      ≤ 2 / (8 * (j : ℝ) + 4) + 1 / (8 * (j : ℝ) + 5) + 1 / (8 * (j : ℝ) + 6) := by
    have e4 : (4 : ℝ) / (8 * (j : ℝ) + 6) = 2 / (8 * (j : ℝ) + 6)
        + 1 / (8 * (j : ℝ) + 6) + 1 / (8 * (j : ℝ) + 6) := by ring
    rw [e4]
    linarith
  have hdiff : 4 / (8 * (j : ℝ) + 1) - 4 / (8 * (j : ℝ) + 6)
      = 20 / ((8 * (j : ℝ) + 1) * (8 * (j : ℝ) + 6)) := by
    field_simp
    ring
  have hceil : 20 / ((8 * (j : ℝ) + 1) * (8 * (j : ℝ) + 6))
      ≤ 20 / (8 * (j : ℝ) + 1) ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have : bbpKick j ≤ 4 / (8 * (j : ℝ) + 1) - 4 / (8 * (j : ℝ) + 6) := by
    rw [bbpKick]
    linarith
  linarith [hdiff ▸ hceil]

theorem bbpKick_pos (j : ℕ) : 0 < bbpKick j :=
  lt_of_lt_of_le (by positivity) (bbpKick_ge j)

theorem bbpTerm_pos (j : ℕ) : 0 < bbpTerm j :=
  mul_pos (by positivity) (bbpKick_pos j)

/-! ### The partial sums, tail, and surrogate -/

/-- Partial sums of the BBP series. -/
noncomputable def piPartial (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, bbpTerm j

/-- The BBP series tail past the first `n` terms. -/
noncomputable def piTail (n : ℕ) : ℝ := Real.pi - piPartial n

/-- The BBP surrogate orbit for π: `fract (16ⁿ · piPartial n)` — the exact
rational shadow of `16ⁿ·π mod 1`. -/
noncomputable def piSurrogate (n : ℕ) : ℝ := Int.fract ((16 : ℝ) ^ n * piPartial n)

/-- **Tail floor** (conditional on the BBP series): the scaled tail is at
least its first term, `16ⁿ·(π − sₙ) ≥ bbpKick n ≥ 3/(16(n+1)²)`. -/
theorem piTail_ge (hπ : PiBBP) (n : ℕ) :
    3 / (16 * ((n : ℝ) + 1) ^ 2) ≤ 16 ^ n * piTail n := by
  have hsummable : Summable bbpTerm := hπ.summable
  have key := hsummable.sum_add_tsum_nat_add n
  have htail : piTail n = ∑' i : ℕ, bbpTerm (i + n) := by
    have hpi : Real.pi = ∑' i, bbpTerm i := hπ.tsum_eq.symm
    rw [piTail, piPartial, hpi, ← key]
    ring
  have hs1 : Summable fun i : ℕ => bbpTerm (i + n) :=
    (summable_nat_add_iff n).mpr hsummable
  have hterm : bbpTerm (0 + n) ≤ ∑' i, bbpTerm (i + n) :=
    hs1.le_tsum 0 (fun i _ => (bbpTerm_pos _).le)
  have hval : (16 : ℝ) ^ n * bbpTerm (0 + n) = bbpKick n := by
    rw [zero_add, bbpTerm]
    have h16 : ((16 : ℝ) ^ n) ≠ 0 := by positivity
    field_simp
  have hstep : (16 : ℝ) ^ n * piTail n = 16 ^ n * ∑' i, bbpTerm (i + n) := by
    rw [htail]
  rw [hstep]
  have hmul : (16 : ℝ) ^ n * bbpTerm (0 + n) ≤ 16 ^ n * ∑' i, bbpTerm (i + n) :=
    mul_le_mul_of_nonneg_left hterm (by positivity)
  calc 3 / (16 * ((n : ℝ) + 1) ^ 2) ≤ bbpKick n := bbpKick_ge n
  _ = (16 : ℝ) ^ n * bbpTerm (0 + n) := hval.symm
  _ ≤ _ := hmul

/-- **Tail ceiling** (conditional on the BBP series): geometric comparison
against the monotone kick ceiling, `16ⁿ·(π − sₙ) ≤ (16/15)·20/(8n+1)²
= 64/(3(8n+1)²)`. -/
theorem piTail_le (hπ : PiBBP) (n : ℕ) :
    16 ^ n * piTail n ≤ 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) := by
  have hsummable : Summable bbpTerm := hπ.summable
  have key := hsummable.sum_add_tsum_nat_add n
  have htail : piTail n = ∑' i : ℕ, bbpTerm (i + n) := by
    have hpi : Real.pi = ∑' i, bbpTerm i := hπ.tsum_eq.symm
    rw [piTail, piPartial, hpi, ← key]
    ring
  have hs1 : Summable fun i : ℕ => bbpTerm (i + n) :=
    (summable_nat_add_iff n).mpr hsummable
  set C : ℝ := 20 / (8 * (n : ℝ) + 1) ^ 2 with hC
  have hCpos : 0 < C := by positivity
  have hgeom : HasSum (fun i : ℕ => C * (1 / 16 ^ n) * (1 / 16 : ℝ) ^ i)
      (C * (1 / 16 ^ n) * ((1 : ℝ) - 1 / 16)⁻¹) :=
    (hasSum_geometric_of_lt_one (r := 1 / 16) (by norm_num) (by norm_num)).mul_left _
  have hterm : ∀ i : ℕ, bbpTerm (i + n) ≤ C * (1 / 16 ^ n) * (1 / 16 : ℝ) ^ i := by
    intro i
    have hkick : bbpKick (i + n) ≤ C := by
      refine (bbpKick_le (i + n)).trans ?_
      rw [hC]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : ((n : ℝ)) ≤ ((i + n : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) i]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) i]
    have hpow : (1 : ℝ) / 16 ^ (i + n) = (1 / 16 ^ n) * (1 / 16 : ℝ) ^ i := by
      rw [div_pow, one_pow, div_mul_div_comm, one_mul, ← pow_add]
      congr 2
      omega
    rw [bbpTerm, hpow]
    calc (1 / 16 ^ n) * (1 / 16 : ℝ) ^ i * bbpKick (i + n)
        ≤ (1 / 16 ^ n) * (1 / 16 : ℝ) ^ i * C :=
          mul_le_mul_of_nonneg_left hkick (by positivity)
    _ = C * (1 / 16 ^ n) * (1 / 16 : ℝ) ^ i := by ring
  have hle : (∑' i : ℕ, bbpTerm (i + n))
      ≤ C * (1 / 16 ^ n) * ((1 : ℝ) - 1 / 16)⁻¹ :=
    le_trans (Summable.tsum_le_tsum hterm hs1 hgeom.summable) (le_of_eq hgeom.tsum_eq)
  rw [htail]
  refine le_trans (mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 16 ^ n)) ?_
  rw [show ((1 : ℝ) - 1 / 16)⁻¹ = 16 / 15 by norm_num, hC]
  have h16 : ((16 : ℝ) ^ n) ≠ 0 := by positivity
  have hB : ((8 : ℝ) * (n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  apply le_of_eq
  field_simp
  ring

/-! ### The headlines: hex-digit runs of π force top-sliver rides -/

/-- Cast bridge: the ℕ-cast base 16 is the real 16. -/
private lemma cast16 : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num

/-- **π hex zero-run dichotomy** (conditional on the BBP series): a run of
`k` hexadecimal zeros of π at position `n` with `16ᵏ > 16(n+1)²/3` — any
run beyond `~2·log₁₆ n` — forces the BBP surrogate into the top sliver
`[1 − 64/(3(8n+1)²), 1)`. -/
theorem pi_top_sliver_of_zeroRun (hπ : PiBBP) {n k : ℕ}
    (hk : 16 * ((n : ℝ) + 1) ^ 2 < 3 * 16 ^ k)
    (h : OccursAt 16 Real.pi (List.replicate k 0) n) :
    1 - 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) ≤ piSurrogate n := by
  have htail : ((16 : ℕ) : ℝ) ^ n * (Real.pi - piPartial n) = 16 ^ n * piTail n := by
    rw [cast16, piTail]
  have hlo : 3 / (16 * ((n : ℝ) + 1) ^ 2)
      ≤ ((16 : ℕ) : ℝ) ^ n * (Real.pi - piPartial n) := by
    rw [htail]; exact piTail_ge hπ n
  have hhi : ((16 : ℕ) : ℝ) ^ n * (Real.pi - piPartial n)
      ≤ 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) := by
    rw [htail]; exact piTail_le hπ n
  have hε : (1 : ℝ) / ((16 : ℕ) : ℝ) ^ k < 3 / (16 * ((n : ℝ) + 1) ^ 2) := by
    rw [cast16, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hcore := top_sliver_of_zeroRun_tail (by norm_num) hlo hhi hε h
  rw [piSurrogate]
  rwa [cast16] at hcore

/-- **π hex F-run dichotomy** (conditional on the BBP series): for `n ≥ 1`,
a run of `k` hex `F`s (digit 15) of π at position `n` with
`16ᵏ > 16(n+1)²/3` forces the surrogate into
`[1 − 64/(3(8n+1)²) − 16⁻ᵏ, 1)`. -/
theorem pi_top_sliver_of_fRun (hπ : PiBBP) {n k : ℕ} (hn : 1 ≤ n)
    (hk : 16 * ((n : ℝ) + 1) ^ 2 < 3 * 16 ^ k)
    (h : OccursAt 16 Real.pi (List.replicate k 15) n) :
    1 - 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) - 1 / (16 : ℝ) ^ k ≤ piSurrogate n := by
  have htail : ((16 : ℕ) : ℝ) ^ n * (Real.pi - piPartial n) = 16 ^ n * piTail n := by
    rw [cast16, piTail]
  have hlo : 3 / (16 * ((n : ℝ) + 1) ^ 2)
      ≤ ((16 : ℕ) : ℝ) ^ n * (Real.pi - piPartial n) := by
    rw [htail]; exact piTail_ge hπ n
  have hhi : ((16 : ℕ) : ℝ) ^ n * (Real.pi - piPartial n)
      ≤ 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) := by
    rw [htail]; exact piTail_le hπ n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hhi2 : 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hε : (1 : ℝ) / ((16 : ℕ) : ℝ) ^ k < 3 / (16 * ((n : ℝ) + 1) ^ 2) := by
    rw [cast16, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h15 : OccursAt 16 Real.pi (List.replicate k (16 - 1)) n := h
  have hcore := top_sliver_of_maxRun_tail (by norm_num) hlo hhi hhi2 hε h15
  rw [piSurrogate]
  rw [cast16] at hcore
  linarith [hcore]

/-! ### Digit agreement: a hex-digit mismatch is a boundary event -/

/-- The hex digit the BBP surrogate predicts at position `n`: the cell
index of `piSurrogate n`. -/
noncomputable def piSurrogateDigit (n : ℕ) : ℕ :=
  (⌊(16 : ℝ) * piSurrogate n⌋).toNat

/-- **π digit-agreement forcing** (conditional on the BBP series; the
Lagarias footnote-1 mechanism for π): for `n ≥ 3`, a disagreement between
the true `n`-th hex digit of π and the BBP-surrogate digit pins the scaled
surrogate `fract (16 · piSurrogate n)` within `1024/(3(8n+1)²)` of the
wrap.  As for `ln 2`, the mismatch event is the separation family in a
density costume — window width `~n⁻²` here, reflecting the quadratic BBP
kick. -/
theorem pi_digit_mismatch_boundary (hπ : PiBBP) {n : ℕ} (hn : 3 ≤ n)
    (hne : digitOf 16 (Int.fract Real.pi) n ≠ piSurrogateDigit n) :
    1 - 1024 / (3 * (8 * (n : ℝ) + 1) ^ 2)
      ≤ Int.fract ((16 : ℝ) * piSurrogate n) := by
  have hn1 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hτlo : 3 / (16 * ((n : ℝ) + 1) ^ 2) ≤ (16 : ℝ) ^ n * piTail n :=
    piTail_ge hπ n
  have hτhi : (16 : ℝ) ^ n * piTail n ≤ 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) :=
    piTail_le hπ n
  set u := piSurrogate n with hu_def
  set τ := (16 : ℝ) ^ n * piTail n with hτ_def
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτlo
  have hbτ : (16 : ℝ) * τ ≤ 1 := by
    have h16 : (16 : ℝ) * τ ≤ 1024 / (3 * (8 * (n : ℝ) + 1) ^ 2) := by
      rw [show (1024 : ℝ) / (3 * (8 * (n : ℝ) + 1) ^ 2)
          = 16 * (64 / (3 * (8 * (n : ℝ) + 1) ^ 2)) by ring]
      linarith
    refine h16.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have hu01 : u ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  -- the true orbit is the perturbed surrogate
  have horb : orbit 16 Real.pi n = Int.fract (u + τ) := by
    simp only [hu_def, hτ_def, piSurrogate, piTail]
    have h := orbit_eq_fract_add_tail 16 Real.pi (piPartial n) n
    rwa [cast16] at h
  -- convert the ℕ digit disagreement to a floor disagreement
  have hbridge : (digitOf 16 (Int.fract Real.pi) n : ℤ)
      = ⌊(16 : ℝ) * orbit 16 Real.pi n⌋ := by
    have h := digitOf_fract_eq_floor_mul_orbit 16 (by norm_num) Real.pi n
    rwa [cast16] at h
  have hsur : (piSurrogateDigit n : ℤ) = ⌊(16 : ℝ) * u⌋ := by
    rw [piSurrogateDigit]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr
      (mul_nonneg (by norm_num) (Int.fract_nonneg _)))
  have hne' : ⌊(16 : ℝ) * u⌋ ≠ ⌊(16 : ℝ) * Int.fract (u + τ)⌋ := by
    intro heq
    apply hne
    have : (digitOf 16 (Int.fract Real.pi) n : ℤ) = (piSurrogateDigit n : ℤ) := by
      rw [hbridge, hsur, horb, heq]
    exact_mod_cast this
  have hcore := fract_mul_top_of_floor_ne (b := 16) (by norm_num)
    hu01 hτ0 (by exact_mod_cast hbτ) (by exact_mod_cast hne')
  have hcast : ((16 : ℕ) : ℝ) = (16 : ℝ) := cast16
  rw [hcast] at hcore
  have h16τ : (16 : ℝ) * τ ≤ 1024 / (3 * (8 * (n : ℝ) + 1) ^ 2) := by
    rw [show (1024 : ℝ) / (3 * (8 * (n : ℝ) + 1) ^ 2)
        = 16 * (64 / (3 * (8 * (n : ℝ) + 1) ^ 2)) by ring]
    linarith
  linarith

end NormalNumbers
