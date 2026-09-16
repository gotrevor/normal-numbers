/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4MertensAP
import NormalNumbers.G4ScheduleHarmonic
import NormalNumbers.G4SchedBParams

/-!
# Campaign A, step A3: from a Mertens rate to a schedule-admissible cutoff exponent

The base-`b` schedule (`G4SchedB*`) uses the cutoff `R = 2^{2^e}` with `e = m₁ b K`, and consumes
the lower Mertens bound only through

    `Sg = ∑_{p ∈ smallPrimes R P₀} 1/p ≥ (2·K·r + 4)/(4θ)`   (`G4SchedBBudget.main_term_le`),

a demand depending on `K` alone (`DESIGN-2026-09-16-prime-subset.md`).  The exponent `e` is free
between that demand and the moment cap `10⁵·T K·e ≤ 2^{8K²}`.

This module is the bridge: `MertensRate S c C` (proved for residue classes in `G4MertensAP`)
produces, for **any** demand `M`, an exponent `e` meeting it, together with the explicit bound
`e ≤ (M + C + c)/(c log 2) + 1` that the cap check needs.  Since the demand is
`exp(O(K log K))` and the cap is `exp(Θ(K²))`, the bound is satisfied for all large `K` — that
is the whole content of "a constant-factor Mertens loss is free for this schedule".
-/

open Finset Real

namespace NormalNumbers.G4.MertensAP

variable {S : ℕ → Prop} [DecidablePred S]

/-- `log log 2 ≥ −1/2`, the only numeric fact needed to convert `log log (2^{2^e})` into
`e · log 2` up to a constant. -/
lemma neg_half_le_log_log_two : (-(1 / 2) : ℝ) ≤ Real.log (Real.log 2) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log (Real.log 2)⁻¹ ≤ (Real.log 2)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at hle
  have hlow : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hinv : (Real.log 2)⁻¹ ≤ 1.4427 := by
    rw [inv_le_comm₀ h2 (by norm_num)]
    nlinarith
  linarith

/-- `log log (2^{2^e}) ≥ e·log 2 − 1/2`. -/
lemma log_log_tower_ge (e : ℕ) :
    (e : ℝ) * Real.log 2 - 1 / 2 ≤ Real.log (Real.log ((2 ^ 2 ^ e : ℕ) : ℝ)) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log ((2 ^ 2 ^ e : ℕ) : ℝ) = (2 : ℝ) ^ e * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog, Real.log_mul (by positivity) h2.ne', Real.log_pow]
  push_cast
  linarith [neg_half_le_log_log_two]

/-- **The bridge.**  A Mertens rate meets any demand `M` at an explicitly bounded cutoff
exponent.  The schedule then only has to check `e` against its moment cap. -/
theorem exists_exponent {c C : ℝ} (h : MertensRate S c C) (M : ℝ) :
    ∃ e : ℕ, M ≤ sumInvPrimesIn S (2 ^ 2 ^ e)
      ∧ (e : ℝ) ≤ max 0 ((M + C + c) / (c * Real.log 2)) + 1 := by
  obtain ⟨hc, hMert⟩ := h
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set t : ℝ := (M + C + c) / (c * Real.log 2) with ht
  refine ⟨⌈t⌉₊, ?_, ?_⟩
  · have hN : 2 ≤ (2 : ℕ) ^ 2 ^ ⌈t⌉₊ := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 2 ^ ⌈t⌉₊ := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    have hM := hMert _ hN
    have hge : (⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2
        ≤ Real.log (Real.log ((2 ^ 2 ^ ⌈t⌉₊ : ℕ) : ℝ)) := log_log_tower_ge _
    have hceil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have hkey : M + C + c ≤ (⌈t⌉₊ : ℝ) * (c * Real.log 2) := by
      have := mul_le_mul_of_nonneg_right hceil (by positivity : (0 : ℝ) ≤ c * Real.log 2)
      rw [ht, div_mul_cancel₀] at this
      · linarith
      · positivity
    have hcc : c * ((⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2) - C ≤ c * Real.log (Real.log ((2 ^ 2 ^ ⌈t⌉₊ : ℕ) : ℝ)) - C := by
      have := mul_le_mul_of_nonneg_left hge hc.le
      linarith
    have hfin : M ≤ c * ((⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2) - C := by
      have hexp : c * ((⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2)
          = (⌈t⌉₊ : ℝ) * (c * Real.log 2) - c / 2 := by ring
      rw [hexp]
      linarith
    linarith [hM, hcc, hfin]
  · rcases le_or_gt 0 t with ht0 | ht0
    · have hlt : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0
      have : t ≤ max 0 t := le_max_right _ _
      linarith
    · have h0 : ⌈t⌉₊ = 0 := by
        rw [Nat.ceil_eq_zero]
        exact ht0.le
      rw [h0]
      have : (0 : ℝ) ≤ max 0 t := le_max_left _ _
      push_cast
      linarith

/-! ### The schedule-side statement

`G4SchedBBudget.main_term_le` consumes `∑ p ∈ smallPrimes R P₀, 1/p ≥ …`.  In the subset world
the sum runs over `smallPrimes R P₀` intersected with `S`, and the only loss relative to
`sumInvPrimesIn S (R+1)` is the frozen primes dividing `P₀` — already bounded by
`Sched.sum_inv_excluded_le` (`≤ 21K² + 2`), *uniformly in `S`* because dropping primes only
decreases the excluded sum.  This is the promised monotonicity: junk only shrinks. -/

open NormalNumbers.PrimeLambert GridParams in
/-- **The subset lower bound at the schedule's small-prime set.**  Everything the base proof
needs, with `S` inserted: the `S`-Mertens sum below the cutoff, minus the frozen primes. -/
theorem sum_inv_smallPrimes_subset_ge {K : ℕ} (hK : 100 ≤ K) (R : ℕ) :
    sumInvPrimesIn S (R + 1) - (21 * (K : ℝ) ^ 2 + 2)
      ≤ ∑ p ∈ {p ∈ smallPrimes R (gridOf K (Sched.N K) (by omega)).P₀ | S p}, (p : ℝ)⁻¹ := by
  classical
  set P₀ := (gridOf K (Sched.N K) (by omega : 1 ≤ K)).P₀ with hP₀
  have hsplit : sumInvPrimesIn S (R + 1)
      = (∑ p ∈ {p ∈ (R + 1).primesBelow | S p ∧ ¬ p ∣ P₀}, (p : ℝ)⁻¹)
        + ∑ p ∈ {p ∈ (R + 1).primesBelow | S p ∧ p ∣ P₀}, (p : ℝ)⁻¹ := by
    rw [sumInvPrimesIn]
    rw [← Finset.sum_filter_add_sum_filter_not {p ∈ (R + 1).primesBelow | S p} (fun p => ¬ p ∣ P₀)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_filter]
      tauto
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_filter, not_not]
      tauto
  have hfirst : ∑ p ∈ {p ∈ (R + 1).primesBelow | S p ∧ ¬ p ∣ P₀}, (p : ℝ)⁻¹
      = ∑ p ∈ {p ∈ smallPrimes R P₀ | S p}, (p : ℝ)⁻¹ := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, smallPrimes]
    tauto
  have hsecond : ∑ p ∈ {p ∈ (R + 1).primesBelow | S p ∧ p ∣ P₀}, (p : ℝ)⁻¹
      ≤ ∑ p ∈ {p ∈ (R + 1).primesBelow | p ∣ P₀}, (p : ℝ)⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have hexcl := Sched.sum_inv_excluded_le hK R
  rw [hsplit, hfirst]
  rw [hP₀] at hsecond
  linarith [hsecond, hexcl]

/-- Monotonicity of the `S`-prime reciprocal sum in the cutoff. -/
lemma sumInvPrimesIn_mono {M N : ℕ} (h : M ≤ N) : sumInvPrimesIn S M ≤ sumInvPrimesIn S N := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp ⊢
  exact ⟨⟨lt_of_lt_of_le hp.1.1 h, hp.1.2⟩, hp.2⟩

open NormalNumbers.PrimeLambert GridParams in
/-- **The drop-in replacement for `G4SchedBParams.sum_inv_smallPrimes_ge`.**  Given a Mertens
rate for `S`, for every target `m` there is a cutoff exponent `e` at which the schedule's
`S`-restricted small-prime sum satisfies the base schedule's bound verbatim —

    `m·log 2 − 21K² − 4 ≤ ∑_{p ∈ smallPrimes (2^{2^e}) P₀, p ∈ S} 1/p` —

together with the explicit bound on `e` (essentially `m/c`) that must be checked against the
moment cap `10⁵·T K·e ≤ 2^{8K²}`.  For `S` = a residue class, `c = 1/(2 φ(q) log 2)`-ish, so the
inflation is by a constant factor in `q`, while the cap is doubly exponential in `K`. -/
theorem exists_cutoff_subset {c C : ℝ} (h : MertensRate S c C) {K : ℕ} (hK : 100 ≤ K) (m : ℕ) :
    ∃ e : ℕ,
      ((m : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
        ≤ ∑ p ∈ {p ∈ smallPrimes (2 ^ 2 ^ e) (gridOf K (Sched.N K) (by omega)).P₀ | S p},
            (p : ℝ)⁻¹)
      ∧ (e : ℝ)
          ≤ max 0 (((m : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + C + c) / (c * Real.log 2)) + 1 := by
  obtain ⟨e, hsum, hbound⟩ :=
    exists_exponent h ((m : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2)
  refine ⟨e, ?_, hbound⟩
  have hmono : sumInvPrimesIn S (2 ^ 2 ^ e) ≤ sumInvPrimesIn S (2 ^ 2 ^ e + 1) :=
    sumInvPrimesIn_mono (Nat.le_succ _)
  have hsched := sum_inv_smallPrimes_subset_ge (S := S) hK (2 ^ 2 ^ e)
  refine le_trans ?_ hsched
  have hstep : (m : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 ≤ sumInvPrimesIn S (2 ^ 2 ^ e + 1) :=
    le_trans hsum hmono
  linarith [hstep, sq_nonneg (K : ℝ)]

/-! ### The cap: the inflated exponent still fits

`exists_cutoff_subset` buys the Mertens demand at an exponent inflated by `1/c` (plus additive
constants), and the schedule's moment order `Mc = 10⁵·T K·e` must stay under `2^{m₂ K} = 2^{8K²}`
(`G4SchedBParams.Mc_le_two_pow_m₂`, needed by `R_pow_two_Mc_le`).  This is the one inequality on
which campaign A's feasibility turns: the demand is `exp(O(K log K))` and the cap is
`exp(Θ(K²))`, so ANY fixed inflation factor `D` is absorbed once `D ≤ 2^K`. -/

/-- **Feasibility certificate.**  With the exponent inflated by any factor `D ≤ 2^K`, the moment
order still obeys the schedule's cap `Mc ≤ 2^{m₂ K}`. -/
theorem moment_cap_subset {b K D e : ℕ} (hb : 3 ≤ b) (hbK : 2 * b ^ 2 ≤ K) (hK : 100 ≤ K)
    (hD : D ≤ 2 ^ K) (he : e ≤ D * (SchedB.m₁ b K + K ^ 2 + 1)) :
    100000 * Sched.T K * e ≤ 2 ^ Sched.m₂ K := by
  have hT := Sched.T_le hK
  have hm₁ := SchedB.m₁_le (K := K) ⟨hb, hbK, hK⟩
  have hK1 : 1 ≤ K := by omega
  have hsq : K ^ 2 + 1 ≤ K ^ (3 * K + 3) := by
    calc K ^ 2 + 1 ≤ K ^ 2 + K ^ 2 := by nlinarith [Nat.one_le_pow 2 K (by omega : 0 < K)]
      _ = 2 * K ^ 2 := by ring
      _ ≤ K * K ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 3 := by ring
      _ ≤ K ^ (3 * K + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsum : SchedB.m₁ b K + K ^ 2 + 1 ≤ 2 * K ^ (3 * K + 3) := by omega
  have he' : e ≤ 2 ^ K * (2 * K ^ (3 * K + 3)) := by
    calc e ≤ D * (SchedB.m₁ b K + K ^ 2 + 1) := he
      _ ≤ 2 ^ K * (2 * K ^ (3 * K + 3)) := Nat.mul_le_mul hD hsum
  have hpow : K ^ (3 * K + 3) * K ^ (3 * K + 3) = K ^ (6 * K + 6) := by
    rw [← pow_add]; ring_nf
  have hstep : 100000 * Sched.T K * e
      ≤ 200000 * (2 ^ K * K ^ (6 * K + 6)) := by
    calc 100000 * Sched.T K * e
        ≤ 100000 * K ^ (3 * K + 3) * (2 ^ K * (2 * K ^ (3 * K + 3))) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hT) he'
      _ = 200000 * (2 ^ K * (K ^ (3 * K + 3) * K ^ (3 * K + 3))) := by ring
      _ = 200000 * (2 ^ K * K ^ (6 * K + 6)) := by rw [hpow]
  have hbig : K ^ (6 * K + 6) ≤ 2 ^ (K * (6 * K + 6)) := Sched.pow_le_two_pow_mul _ _
  have h2e : (200000 : ℕ) ≤ 2 ^ 18 := by norm_num
  have hfin : 200000 * (2 ^ K * K ^ (6 * K + 6)) ≤ 2 ^ (18 + K + K * (6 * K + 6)) := by
    calc 200000 * (2 ^ K * K ^ (6 * K + 6))
        ≤ 2 ^ 18 * (2 ^ K * 2 ^ (K * (6 * K + 6))) := by
          exact Nat.mul_le_mul h2e (Nat.mul_le_mul_left _ hbig)
      _ = 2 ^ (18 + K + K * (6 * K + 6)) := by rw [← pow_add, ← pow_add]; ring_nf
  have hexp : 18 + K + K * (6 * K + 6) ≤ Sched.m₂ K := by
    unfold Sched.m₂
    nlinarith
  exact le_trans hstep (le_trans hfin (Nat.pow_le_pow_right (by norm_num) hexp))

end NormalNumbers.G4.MertensAP
