/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertQuantitative

/-!
# Density rungs for the binary digits of `E = Σ 1/(2ⁿ−1)`: audit record (2026-10-03)

`jointWords_power_count` (with `S = {2}`) gives every binary word at `≥ N^{1−ε}` of the first
`N` offsets of the Erdős–Borwein constant.  This file records the next three rungs as open
targets, the cheap implications between them, and the two facts the audit's difficulty check
rests on.  No rung is claimed.  Verdict and grades: `docs/EDENSITY-AUDIT-2026-10-03.md`;
closed routes: the two `Maze` rows dated 2026-10-03.

* `RungPolylog` (R1): `count ≥ N/(log N)^A`.
* `RungRich` (R2): `count ≥ c·N`, positive lower density.
* `RungFair κ` (R3): `liminf count/N ≥ κ·2^{−ℓ}`.  Crandall (Integers 12 (2012) #A23, §7)
  lists even "half the bits of `E` are `1`" as open.

**Mechanism facts proved here.**

* `two_pow_oddExpCount_dvd_card_divisors`: `2^{ω_odd(m)} ∣ τ(m)`, where `ω_odd` counts primes to
  an odd power.  So the term `τ(n+j)/2^j` of `frac(2ⁿE) = frac(Σ_{j≥1} τ(n+j)/2^j)` is an
  integer whenever `j ≤ ω_odd(n+j)` (`fract_card_divisors_div_two_pow_eq_zero`).  For typical
  `n` this kills every position `j ≤ (1−ε) log log n` for free, in base 2 only.  The digits of
  `E` near offset `n` are therefore decided by a band `j = log log n ± O(√(log log n))`.
* The known-false sibling: the parity bit of `τ` is the square indicator, so a mechanism that
  reads only `τ mod 2` sees `Σ_k 2^{−k²}` and at most `√N + 1` ones
  (`card_odd_card_divisors_le`).  Any density argument must use the large 2-adic part of `τ`,
  not its low bit.

**Open premise.**  `ResidualSmallOften` / `ResidualSmallPolylog`: the non-killed part of the
tail is `< 2^{−K}` for a positive (resp. `(log N)^{−A}`) proportion of offsets.  Either would
put the all-zero word `0^K` on R2 (resp. R1), not yet a Lean edge.  General words need, in
addition, a writer position whose `τ` is prescribed exactly, which is the joint local
Erdős–Kac input already named at `Erdos257Squarefree.SqfreeBinaryDisjunctive`.
-/

namespace NormalNumbers.EDensity

open NormalNumbers.JointLambert Finset

/-- A binary word of length `ℓ ≥ 1` with value `v < 2^ℓ`. -/
def ValidWord (ℓ v : ℕ) : Prop := 0 < ℓ ∧ v < 2 ^ ℓ

/-- Offsets `n < N` at which the binary word `(ℓ, v)` starts at digit `n + 1` of `E`.
This is `jointWordCount` at `S = {2}`, so it is the count `jointWords_power_count` bounds. -/
noncomputable def eCount (ℓ v N : ℕ) : ℕ :=
  jointWordCount {2} (fun _ => ℓ) (fun _ => v) N

/-- The proved baseline (unconditional): every word at `≥ N^{1−ε}` offsets, eventually. -/
theorem eCount_power (ℓ v : ℕ) (hw : ValidWord ℓ v) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (N : ℝ) ^ (1 - ε) ≤ (eCount ℓ v N : ℝ) :=
  jointWords_power_count {2} (by simp) _ _
    (fun b hb => by rw [Finset.mem_singleton] at hb; subst hb; exact hw) ε hε

/-- **R1** (open): every word at `≥ N/(log N)^A` offsets, eventually. -/
def RungPolylog : Prop :=
  ∀ ℓ v : ℕ, ValidWord ℓ v → ∃ A : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / Real.log N ^ A ≤ (eCount ℓ v N : ℝ)

/-- **R2** (open): every word has positive lower density of starting offsets. -/
def RungRich : Prop :=
  ∀ ℓ v : ℕ, ValidWord ℓ v → ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    c * N ≤ (eCount ℓ v N : ℝ)

/-- **R3** (open): `liminf count/N ≥ κ · 2^{−ℓ}` for every word. -/
def RungFair (κ : ℝ) : Prop :=
  ∀ ℓ v : ℕ, ValidWord ℓ v → ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (κ - η) * N / 2 ^ ℓ ≤ (eCount ℓ v N : ℝ)

/-- R3 at any `κ > 0` gives R2. -/
theorem rungRich_of_rungFair {κ : ℝ} (hκ : 0 < κ) (h : RungFair κ) : RungRich := by
  intro ℓ v hw
  obtain ⟨N0, hN0⟩ := h ℓ v hw (κ / 2) (by positivity)
  refine ⟨κ / 2 / 2 ^ ℓ, by positivity, N0, fun N hN => ?_⟩
  calc κ / 2 / 2 ^ ℓ * N = (κ - κ / 2) * N / 2 ^ ℓ := by ring
    _ ≤ _ := hN0 N hN

/-- R2 gives R1 (with `A = 1`). -/
theorem rungPolylog_of_rungRich (h : RungRich) : RungPolylog := by
  intro ℓ v hw
  obtain ⟨c, hc, N0, hN0⟩ := h ℓ v hw
  refine ⟨1, max N0 (⌈Real.exp (1 / c)⌉₊ + 1), fun N hN => ?_⟩
  have hN0' : N0 ≤ N := le_trans (le_max_left _ _) hN
  have h1 : (⌈Real.exp (1 / c)⌉₊ + 1 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have h3 : ((⌈Real.exp (1 / c)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
  have h2 : Real.exp (1 / c) ≤ ⌈Real.exp (1 / c)⌉₊ := Nat.le_ceil _
  push_cast at h3
  have hNe : Real.exp (1 / c) < N := by linarith
  have hNpos : (0 : ℝ) < N := lt_trans (Real.exp_pos _) hNe
  have hlog : 1 / c < Real.log N := (Real.lt_log_iff_exp_lt hNpos).mpr hNe
  have hlogpos : 0 < Real.log N := lt_trans (by positivity) hlog
  rw [Real.rpow_one]
  refine le_trans ?_ (hN0 N hN0')
  rw [div_le_iff₀ hlogpos]
  have hcl : 1 ≤ c * Real.log N := by
    have := mul_lt_mul_of_pos_left hlog hc
    rw [mul_one_div_cancel hc.ne'] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hcl hNpos.le]

/-! ## The free 2-adic kill -/

/-- `ω_odd(m)`: the number of primes dividing `m` to an odd power. -/
def oddExpCount (m : ℕ) : ℕ :=
  (m.primeFactors.filter fun p => Odd (m.factorization p)).card

/-- `2^{ω_odd(m)} ∣ τ(m)`: each prime to an odd power `e` contributes the even factor `e + 1`. -/
theorem two_pow_oddExpCount_dvd_card_divisors (m : ℕ) :
    2 ^ oddExpCount m ∣ m.divisors.card := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [Nat.card_divisors hm, oddExpCount,
    ← Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => Odd (m.factorization p)),
    ← Finset.prod_const]
  apply Dvd.dvd.mul_right
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨k, hk⟩ := hp.2
  exact ⟨k + 1, by omega⟩

/-- **The free kill.**  If `j ≤ ω_odd(m)`, the Lambert term `τ(m)/2^j` is an integer, so it
contributes nothing to `frac(2ⁿE)` at `m = n + j`. -/
theorem fract_card_divisors_div_two_pow_eq_zero {m j : ℕ} (hj : j ≤ oddExpCount m) :
    Int.fract ((m.divisors.card : ℝ) / 2 ^ j) = 0 := by
  obtain ⟨q, hq⟩ := (pow_dvd_pow 2 hj).trans (two_pow_oddExpCount_dvd_card_divisors m)
  rw [hq]
  push_cast
  rw [mul_div_cancel_left₀ _ (by positivity)]
  exact Int.fract_natCast q

/-! ## The known-false sibling: `τ mod 2` reads only squares -/

/-- An odd divisor count forces a square (every exponent even). -/
theorem isSquare_of_odd_card_divisors {m : ℕ} (h : Odd m.divisors.card) : IsSquare m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp at h
  rw [Nat.card_divisors hm] at h
  have hev : ∀ p ∈ m.primeFactors, Even (m.factorization p) := by
    intro p hp
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    obtain ⟨k, hk⟩ := hne
    have h2 : 2 ∣ ∏ q ∈ m.primeFactors, (m.factorization q + 1) :=
      (Dvd.intro (k + 1) (by omega)).trans (Finset.dvd_prod_of_mem _ hp)
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  nth_rewrite 1 [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := hev p hp
  omega

/-- **Sibling control.**  At most `√N + 1` integers below `N` have an odd divisor count, so the
parity bit of `τ` alone (the binary digits of `Σ_k 2^{−k²}`) carries density zero. -/
theorem card_odd_card_divisors_le (N : ℕ) :
    ((Finset.range N).filter fun m => Odd m.divisors.card).card ≤ Nat.sqrt N + 1 := by
  calc ((Finset.range N).filter fun m => Odd m.divisors.card).card
      ≤ (Finset.range (Nat.sqrt N + 1)).card := by
        apply Finset.card_le_card_of_injOn Nat.sqrt
        · intro m hm
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hm
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt hm.1.le)
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
          obtain ⟨r, rfl⟩ := isSquare_of_odd_card_divisors ha.2
          obtain ⟨s, rfl⟩ := isSquare_of_odd_card_divisors hb.2
          simp only [Nat.sqrt_eq] at hab
          rw [hab]
    _ = Nat.sqrt N + 1 := Finset.card_range _

/-! ## The open premise (reopen condition of the 2026-10-03 Maze walls) -/

/-- Partial sums of the non-killed Lambert terms after offset `n`:
`Σ_{1 ≤ j ≤ J, 2^j ∤ τ(n+j)} τ(n+j)/2^j`.  The killed terms are integers, so
`frac(2ⁿE)` equals the full residual whenever that residual is `< 1`. -/
noncomputable def residualPartial (n J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J,
    if 2 ^ (j + 1) ∣ (n + (j + 1)).divisors.card then 0
    else ((n + (j + 1)).divisors.card : ℝ) / 2 ^ (j + 1)

/-- Offsets `n < N` whose whole non-killed residual stays below `2^{−K}`, so the word `0^K`
starts at `n` (the bridge to `eCount K 0` is not yet a Lean edge). -/
noncomputable def residualSmallCount (K N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => ∀ J : ℕ, residualPartial n J < 1 / 2 ^ K).card

/-- **Open premise, positive-proportion form.**  Believed true (~85%): heuristically the band
`j ≈ log log n` holds `O(1)` problem positions in expectation, so it is clean with probability
bounded below.  No proof is known; a sieve in dimension `≍ log log N` loses a margin
`≍ log log log N` per band position and reaches only `(log log N)^{−C}`. -/
def ResidualSmallOften : Prop :=
  ∀ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → c * N ≤ (residualSmallCount K N : ℝ)

/-- **Open premise, polylog form** (the R1 analogue).  Believed true (~95%); the paper route
would be the fundamental lemma of the sieve in dimension `≍ log log N` over the integers,
plus Hardy–Ramanujan bounds on large prime factors at each band position (~25% that this
closes on paper; far beyond current Lean infrastructure). -/
def ResidualSmallPolylog : Prop :=
  ∀ K : ℕ, ∃ A : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / Real.log N ^ A ≤ (residualSmallCount K N : ℝ)

/-- The positive-proportion premise implies the polylog one. -/
theorem residualSmallPolylog_of_often (h : ResidualSmallOften) : ResidualSmallPolylog := by
  intro K
  obtain ⟨c, hc, N0, hN0⟩ := h K
  refine ⟨1, max N0 (⌈Real.exp (1 / c)⌉₊ + 1), fun N hN => ?_⟩
  have hN0' : N0 ≤ N := le_trans (le_max_left _ _) hN
  have h1 : (⌈Real.exp (1 / c)⌉₊ + 1 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have h3 : ((⌈Real.exp (1 / c)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
  have h2 : Real.exp (1 / c) ≤ ⌈Real.exp (1 / c)⌉₊ := Nat.le_ceil _
  push_cast at h3
  have hNe : Real.exp (1 / c) < N := by linarith
  have hNpos : (0 : ℝ) < N := lt_trans (Real.exp_pos _) hNe
  have hlog : 1 / c < Real.log N := (Real.lt_log_iff_exp_lt hNpos).mpr hNe
  have hlogpos : 0 < Real.log N := lt_trans (by positivity) hlog
  rw [Real.rpow_one]
  refine le_trans ?_ (hN0 N hN0')
  rw [div_le_iff₀ hlogpos]
  have hcl : 1 ≤ c * Real.log N := by
    have := mul_lt_mul_of_pos_left hlog hc
    rw [mul_one_div_cancel hc.ne'] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hcl hNpos.le]

end NormalNumbers.EDensity
