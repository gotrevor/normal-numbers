/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyGibbs

/-!
# An entropy deficit bounds every set's bias: the Hellinger route

The second piece of finite information theory the frequency theorem needs.  `G4EntropyGibbs`
turns a joint entropy deficit into a sum of coordinate deficits; this module turns *one*
coordinate deficit into a bound on how far a set's probability can be from its uniform value.

The standard tool is Pinsker's inequality `KL₂(p‖u) ≥ 2(p−u)²/log 2`, whose usual proof is a
second-derivative argument.  We do not need the constant, so we take the **Hellinger route**,
which needs no calculus at all:

* `two_mul_sub_sqrt_le` — `2a − 2√a√b ≤ a·log a − a·log b`, one application of
  `log t ≤ t − 1` at `t = √(b/a)`, with `a = 0` true by inspection;
* summing the two branches, `klb p u ≥ (√p−√u)² + (√(1−p)−√(1−u))²` — the squared Hellinger
  distance — and `(√x−√y)² ≥ (x−y)²/4` because `√x + √y ≤ 2`, giving
  **`klb p u ≥ (p−u)²/2`** (`klb_ge_sq`), a factor `4` weaker than Pinsker and entirely
  sufficient;
* `sq_prob_sub_le_logb_card_sub_H₂` — Gibbs against the two-point law
  `q = p/|B| on B, (1−p)/|Bᶜ| off B` identifies `log₂|Ω| − H₂ L` with a binary KL, so

      `(L.prob B − |B|/|Ω|)² / (2·log 2)  ≤  log₂ |Ω| − H₂ L`.

That is the statement used downstream: an alphabet-`ℓ` coordinate whose entropy is within `ε`
of `ℓ` has every word's probability within `√(2 ε log 2)` of `2^{−ℓ}`.
-/

open Finset

namespace NormalNumbers.G4Entropy

/-! ### The Hellinger step -/

/-- `2a − 2√a√b ≤ a·log a − a·log b`.  For `a > 0` this is `log √(b/a) ≤ √(b/a) − 1` scaled by
`2a`; at `a = 0` both sides are `0`. -/
lemma two_mul_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    2 * a - 2 * Real.sqrt a * Real.sqrt b ≤ a * Real.log a - a * Real.log b := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]; simp
  · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 h
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    have hlog : Real.log (Real.sqrt b / Real.sqrt a) ≤ Real.sqrt b / Real.sqrt a - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (Real.sqrt b / Real.sqrt a) = (Real.log b - Real.log a) / 2 := by
      rw [Real.log_div hsb.ne' hsa.ne', Real.log_sqrt hb.le, Real.log_sqrt ha]
      ring
    rw [hsplit] at hlog
    have h2 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * a)
    have hkey : a / Real.sqrt a = Real.sqrt a := by
      rw [eq_comm, eq_div_iff hsa.ne']
      exact Real.mul_self_sqrt ha
    have hid : 2 * a * (Real.sqrt b / Real.sqrt a - 1)
        = 2 * Real.sqrt a * Real.sqrt b - 2 * a := by
      have : 2 * a * (Real.sqrt b / Real.sqrt a - 1)
          = 2 * (a / Real.sqrt a) * Real.sqrt b - 2 * a := by
        field_simp
      rw [this, hkey]
    have hid2 : 2 * a * ((Real.log b - Real.log a) / 2)
        = a * Real.log b - a * Real.log a := by ring
    rw [hid, hid2] at h2
    linarith

/-! ### Binary Kullback–Leibler divergence -/

/-- The binary KL divergence of `p` from `u`, in nats, with mathlib's `log 0 = 0` convention
(harmless: every logarithm appears multiplied by its own mass). -/
noncomputable def klb (p u : ℝ) : ℝ :=
  (p * Real.log p - p * Real.log u) + ((1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - u))

/-- **The Hellinger bound.**  `klb p u ≥ (p−u)²/2` — Pinsker with the constant `1/2` in place
of `2`, proved with no calculus. -/
theorem klb_ge_sq {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu0 : 0 < u) (hu1 : u < 1) :
    (p - u) ^ 2 / 2 ≤ klb p u := by
  set A := Real.sqrt p with hAdef
  set B := Real.sqrt u with hBdef
  set C := Real.sqrt (1 - p) with hCdef
  set D := Real.sqrt (1 - u) with hDdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = p := Real.sq_sqrt hp0
  have hB2 : B ^ 2 = u := Real.sq_sqrt hu0.le
  have hC2 : C ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hD2 : D ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
  have hA1 : A ≤ 1 := by nlinarith [hA2, hA0]
  have hB1 : B ≤ 1 := by nlinarith [hB2, hB0]
  have hC1 : C ≤ 1 := by nlinarith [hC2, hC0]
  have hD1 : D ≤ 1 := by nlinarith [hD2, hD0]
  -- the two Hellinger branches
  have hbr1 : 2 * p - 2 * A * B ≤ p * Real.log p - p * Real.log u :=
    two_mul_sub_sqrt_le hp0 hu0
  have hbr2 : 2 * (1 - p) - 2 * C * D
      ≤ (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - u) :=
    two_mul_sub_sqrt_le (by linarith) (by linarith)
  -- `2 − 2(AB + CD) = (A−B)² + (C−D)²`
  have hsq : (A - B) ^ 2 + (C - D) ^ 2 = 2 * p - 2 * A * B + (2 * (1 - p) - 2 * C * D) := by
    have hexp : (A - B) ^ 2 + (C - D) ^ 2
        = (A ^ 2 + C ^ 2) + (B ^ 2 + D ^ 2) - 2 * (A * B + C * D) := by ring
    rw [hexp, hA2, hB2, hC2, hD2]; ring
  -- `(p−u)² ≤ 4(A−B)²` and `(p−u)² ≤ 4(C−D)²`
  have h1 : (p - u) ^ 2 ≤ 4 * (A - B) ^ 2 := by
    have he : (p - u) ^ 2 = (A - B) ^ 2 * (A + B) ^ 2 := by
      rw [← hA2, ← hB2]; ring
    rw [he]; nlinarith [sq_nonneg (A - B), hA0, hB0, hA1, hB1]
  have h2 : (p - u) ^ 2 ≤ 4 * (C - D) ^ 2 := by
    have he : (p - u) ^ 2 = (C - D) ^ 2 * (C + D) ^ 2 := by
      rw [show p - u = -((1 - p) - (1 - u)) by ring, ← hC2, ← hD2]; ring
    rw [he]; nlinarith [sq_nonneg (C - D), hC0, hD0, hC1, hD1]
  rw [klb]
  linarith [hbr1, hbr2, hsq, h1, h2]

/-! ### The two-point Gibbs bound -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The two-point comparison law: uniform on `B` with total mass `p`, uniform off `B` with
total mass `1 − p`. -/
private noncomputable def twoPt (B : Finset Ω) (p : ℝ) (ω : Ω) : ℝ :=
  if ω ∈ B then p / B.card else (1 - p) / (Bᶜ.card : ℝ)

/-- **An entropy deficit bounds every set's bias.**  If `L` is a law on an alphabet of size
`N` and `B` a proper nonempty subset, then the squared deviation of `L.prob B` from its uniform
value `|B|/N` is at most `2 log 2` times the entropy deficit.

For `B` a singleton in `Fin (2^ℓ)` this reads: a coordinate whose entropy is within `ε` of `ℓ`
gives every word probability within `√(2 ε log 2)` of `2^{−ℓ}`. -/
theorem sq_prob_sub_le_logb_card_sub_H₂ (L : FinLaw Ω) {B : Finset Ω}
    (hB : B.Nonempty) (hBc : Bᶜ.Nonempty) :
    (L.prob B - (B.card : ℝ) / (Fintype.card Ω : ℝ)) ^ 2 / (2 * Real.log 2)
      ≤ Real.logb 2 (Fintype.card Ω) - L.H₂ := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := (B.card : ℝ) with hc
  set d : ℝ := (Bᶜ.card : ℝ) with hd
  have hc0 : 0 < c := by rw [hc]; exact_mod_cast Finset.card_pos.2 hB
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Finset.card_pos.2 hBc
  have hN : (Fintype.card Ω : ℝ) = c + d := by
    rw [hc, hd]
    have := Finset.card_add_card_compl B
    exact_mod_cast this.symm
  have hN0 : (0 : ℝ) < (Fintype.card Ω : ℝ) := by rw [hN]; linarith
  set p : ℝ := L.prob B with hp
  have hp0 : 0 ≤ p := L.prob_nonneg B
  have hpc : L.prob Bᶜ = 1 - p := by
    have := L.prob_add_prob_compl B; linarith
  have hp1 : p ≤ 1 := by
    have := L.prob_nonneg Bᶜ; rw [hpc] at this; linarith
  -- Gibbs against the two-point law
  have hq0 : ∀ ω, 0 ≤ twoPt B p ω := by
    intro ω; rw [twoPt]; split
    · positivity
    · have : 0 ≤ 1 - p := by linarith
      positivity
  have hq1 : ∑ ω, twoPt B p ω ≤ 1 := by
    have hsplit : ∑ ω, twoPt B p ω
        = ∑ ω ∈ B, twoPt B p ω + ∑ ω ∈ Bᶜ, twoPt B p ω :=
      (Finset.sum_add_sum_compl B _).symm
    have h1 : ∑ ω ∈ B, twoPt B p ω = p := by
      rw [Finset.sum_congr rfl fun ω hω => by rw [twoPt, if_pos hω]]
      rw [Finset.sum_const, nsmul_eq_mul, ← hc]
      field_simp
    have h2 : ∑ ω ∈ Bᶜ, twoPt B p ω = 1 - p := by
      rw [Finset.sum_congr rfl fun ω hω =>
        by rw [twoPt, if_neg (Finset.mem_compl.1 hω)]]
      rw [Finset.sum_const, nsmul_eq_mul, ← hd]
      field_simp
    rw [hsplit, h1, h2]; linarith
  have hsupp : ∀ ω, 0 < L.p ω → 0 < twoPt B p ω := by
    intro ω hω
    rw [twoPt]
    split
    · rename_i hmem
      have : 0 < p := lt_of_lt_of_le hω
        (Finset.single_le_sum (f := L.p) (fun i _ => L.nonneg i) hmem)
      positivity
    · rename_i hmem
      have hmc : ω ∈ Bᶜ := Finset.mem_compl.2 hmem
      have : 0 < 1 - p := by
        rw [← hpc]
        exact lt_of_lt_of_le hω
          (Finset.single_le_sum (f := L.p) (fun i _ => L.nonneg i) hmc)
      positivity
  have hgibbs := L.gibbs hq0 hq1 hsupp
  -- evaluate the cross entropy
  have hcross : ∑ ω, L.p ω * Real.logb 2 (twoPt B p ω)
      = p * Real.logb 2 (p / c) + (1 - p) * Real.logb 2 ((1 - p) / d) := by
    have hsplit : ∑ ω, L.p ω * Real.logb 2 (twoPt B p ω)
        = ∑ ω ∈ B, L.p ω * Real.logb 2 (twoPt B p ω)
          + ∑ ω ∈ Bᶜ, L.p ω * Real.logb 2 (twoPt B p ω) :=
      (Finset.sum_add_sum_compl B _).symm
    have h1 : ∑ ω ∈ B, L.p ω * Real.logb 2 (twoPt B p ω) = p * Real.logb 2 (p / c) := by
      rw [Finset.sum_congr rfl fun ω hω => by rw [twoPt, if_pos hω, ← hc]]
      rw [← Finset.sum_mul, ← FinLaw.prob, ← hp]
    have h2 : ∑ ω ∈ Bᶜ, L.p ω * Real.logb 2 (twoPt B p ω)
        = (1 - p) * Real.logb 2 ((1 - p) / d) := by
      rw [Finset.sum_congr rfl fun ω hω =>
        by rw [twoPt, if_neg (Finset.mem_compl.1 hω), ← hd]]
      rw [← Finset.sum_mul, ← FinLaw.prob, hpc]
    rw [hsplit, h1, h2]
  rw [hcross] at hgibbs
  -- the cross entropy is `log₂ N − klb(p, c/N)`
  set u : ℝ := c / (Fintype.card Ω : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hN0, hN]; linarith
  have h1u : 1 - u = d / (Fintype.card Ω : ℝ) := by
    rw [hu, hN]; field_simp; ring
  -- `x * logb 2 (x / y) = x * (log x − log y) / log 2` for `x ≥ 0`, `y > 0`
  have hmul : ∀ x y : ℝ, 0 ≤ x → 0 < y →
      x * Real.logb 2 (x / y) = (x * Real.log x - x * Real.log y) / Real.log 2 := by
    intro x y hx hy
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h]; simp
    · rw [Real.logb, Real.log_div h.ne' hy.ne']; ring
  rw [hmul p c hp0 hc0, hmul (1 - p) d (by linarith) hd0] at hgibbs
  -- assemble
  have hklb : Real.logb 2 (Fintype.card Ω) - L.H₂ ≥ klb p u / Real.log 2 := by
    have hlogN : Real.logb 2 (Fintype.card Ω) = Real.log (Fintype.card Ω) / Real.log 2 := rfl
    have hexp : klb p u / Real.log 2
        = Real.log (Fintype.card Ω) / Real.log 2
          - (-((p * Real.log p - p * Real.log c) / Real.log 2
              + ((1 - p) * Real.log (1 - p) - (1 - p) * Real.log d) / Real.log 2)) := by
      rw [klb, h1u, hu]
      rw [Real.log_div hc0.ne' hN0.ne', Real.log_div hd0.ne' hN0.ne']
      field_simp
      ring
    rw [hlogN, hexp]
    linarith [hgibbs]
  have hsq := klb_ge_sq hp0 hp1 hu0 hu1
  have : (p - u) ^ 2 / (2 * Real.log 2) ≤ klb p u / Real.log 2 := by
    rw [div_le_div_iff₀ (by positivity) hlog2]
    nlinarith [hsq, hlog2]
  linarith [this, hklb]

end NormalNumbers.G4Entropy
