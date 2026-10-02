/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertQuantitativeStatement
import NormalNumbers.JointLambertUnconditional
import NormalNumbers.JointLambertGcdAverage
import NormalNumbers.JointLambertSmallPool
import NormalNumbers.JointLambertCountAssembly

/-!
# The quantitative joint Lambert theorem

The two ratified endpoints of the counting campaign.  `jointWordCount` and its predicate
are frozen in `JointLambertQuantitativeStatement.lean`; `orbit` and `E_b` are the ones of
`JointLambertStatement.lean`, so the qualitative theorem
`jointWords_unconditional` and these counts speak about the same object.

* `jointWords_quantitative` — for **every** `N ≥ N₀`,
  `A(N) ≥ N exp(-C (log log N)² log log log N)`.
  The parenthesisation is load-bearing: `(-C) * (log log N)^2 * (log log log N)`.
* `jointWords_power_count` — for each **fixed** `ε > 0`, eventually `A(N) ≥ N^{1-ε}`.

Paper route: `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` §§3–5.  The open obligations are
named below with a content locator each; no opaque `Prop` hypothesis stands in for them.
-/

namespace NormalNumbers.JointLambert

open Finset Filter

/-- The iterated-logarithm rate is `o(log N)`: for every `C > 0` and `ε > 0`,
eventually `C (log log N)² log log log N ≤ ε log N`.

This is the only analytic input of §5 of the note, and it is what converts the
exponential-in-iterated-logs count into the power count. -/
theorem iteratedLog_rate_le_eps_log (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      C * (Real.log (Real.log (N : ℝ))) ^ 2 * Real.log (Real.log (Real.log (N : ℝ)))
        ≤ ε * Real.log (N : ℝ) := by
  -- work in the variable `L = log N`, which tends to `atTop`
  have hbase : ∀ᶠ L : ℝ in atTop,
      C * (Real.log L) ^ 2 * Real.log (Real.log L) ≤ ε * L := by
    have hlo := (Real.isLittleO_pow_log_id_atTop (n := 3)).def (div_pos hε hC)
    filter_upwards [hlo, eventually_ge_atTop (3 : ℝ)] with L hL h3
    have hL0 : (0 : ℝ) < L := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log L := by
      have : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) h3
      have h1 : (1 : ℝ) ≤ Real.log 3 := by
        rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
        exact Real.log_le_log (Real.exp_pos 1) (by
          have := Real.exp_one_lt_d9
          linarith)
      linarith
    have hstep : Real.log (Real.log L) ≤ Real.log L := Real.log_le_self (by linarith)
    have hsq : (0 : ℝ) ≤ C * (Real.log L) ^ 2 := by positivity
    have h1 : C * (Real.log L) ^ 2 * Real.log (Real.log L) ≤ C * (Real.log L) ^ 3 := by
      nlinarith [hsq, hstep]
    have hnorm : Real.log L ^ 3 ≤ ε / C * L := by
      have h2 : ‖Real.log L ^ 3‖ ≤ ε / C * ‖id L‖ := hL
      simpa [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ Real.log L by linarith),
        abs_of_nonneg hL0.le, id] using h2
    calc C * (Real.log L) ^ 2 * Real.log (Real.log L) ≤ C * (Real.log L) ^ 3 := h1
      _ ≤ C * (ε / C * L) := by exact mul_le_mul_of_nonneg_left hnorm hC.le
      _ = ε * L := by field_simp
  have htend : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (htend.eventually hbase)

/-- **The quantitative joint Lambert count.**  For every finite set `S` of bases `≥ 2`
and every choice of a nonempty valid word in each base, the number of offsets `n < N` at
which all the words start simultaneously is at least
`N exp(-C (log log N)² log log log N)` for all `N ≥ N₀`.

`C` and `N₀` depend on `S` and the words.  No uniformity in the bases and no effective
threshold is claimed.

Route (note §§3–5): at each large height `X` choose `k = ⌈4 log₂ log X⌉`, `L = k³`, draw the
CRT allocation primes from `(L, 2L)` via `exists_prime_allocation_small_pool`, take `P(X)`
from `exists_pointwise_exponential_distribution` first, get `≥ M/(4 log X)` prime
candidates with `M = ⌊X/B⌋+1`, kill the tail in three ranges
(`sum_tau_progression_le_noncoprime` and `jointA_tau_le` in the middle range), Markov at the
fixed threshold `2δ`, keep the good-set CARDINALITY, and convert to every `N` by
`X = ⌊N/D_N⌋`. -/
theorem jointWords_quantitative (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b)
    (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (Real.log (N : ℝ))) ^ 2
        * Real.log (Real.log (Real.log (N : ℝ))))
          ≤ (jointWordCount S lengths values N : ℝ) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · -- empty base set: the count is `N`, and `exp(-μ²ν) ≤ 1` once `log log N ≥ 1`
    refine ⟨1, one_pos, ?_⟩
    have htend2 : Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (htend2.eventually_ge_atTop (3 : ℝ))
    refine ⟨N0, fun N hN => ?_⟩
    have hμ : (3 : ℝ) ≤ Real.log (Real.log (N : ℝ)) := hN0 N hN
    have hν : (0 : ℝ) ≤ Real.log (Real.log (Real.log (N : ℝ))) := by
      refine Real.log_nonneg ?_
      linarith
    rw [jointWordCount_empty]
    have hexp : Real.exp (-1 * (Real.log (Real.log (N : ℝ))) ^ 2
        * Real.log (Real.log (Real.log (N : ℝ)))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hsq : (0 : ℝ) ≤ (Real.log (Real.log (N : ℝ))) ^ 2 := by positivity
      nlinarith [hsq, hν]
    have hN0' : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [hexp, hN0']
  -- a common multiple of the bases
  set c : ℕ := ∏ b ∈ S, b with hcdef
  have hbc : ∀ b ∈ S, b ∣ c := fun b hb => Finset.dvd_prod_of_mem _ hb
  have hc2 : 2 ≤ c := by
    obtain ⟨b₀, hb₀⟩ := hne
    have h1 : b₀ ≤ c :=
      Finset.single_le_prod' (f := fun i => i) (fun i hi => by have := hb2 i hi; omega) hb₀
    have := hb2 b₀ hb₀
    omega
  -- one positive margin over the finite set
  set P : ℕ := ∏ b ∈ S, b ^ lengths b with hPdef
  have hPbig : ∀ b ∈ S, b ^ lengths b ≤ P :=
    fun b hb => Finset.single_le_prod' (f := fun i => i ^ lengths i)
      (fun i hi => Nat.one_le_pow _ _ (by have := hb2 i hi; omega)) hb
  have hPpos : 0 < P := Finset.prod_pos fun b hb => Nat.pow_pos (by have := hb2 b hb; omega)
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  set ε : ℝ := 1 / (P : ℝ) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  -- interior cylinders for the prescribed words
  obtain ⟨s, a, hs2, ha2, hbox⟩ := evenEncoding S hb2
      (fun b => (values b : ℝ) / (b : ℝ) ^ lengths b)
      (fun b => ((values b : ℝ) + 1 / 2) / (b : ℝ) ^ lengths b) (by
        intro b hb
        have hb2' := hb2 b hb
        have hb0 : (0 : ℝ) < b := by
          have : (2 : ℝ) ≤ b := by exact_mod_cast hb2'
          linarith
        have hbl0 : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
        obtain ⟨hlen, hval⟩ := hwin b hb
        have hvR : (values b : ℝ) + 1 ≤ (b : ℝ) ^ lengths b := by
          have h1 : (values b : ℕ) + 1 ≤ b ^ lengths b := by omega
          have h2 : ((values b : ℕ) + 1 : ℝ) ≤ ((b ^ lengths b : ℕ) : ℝ) := by
            exact_mod_cast h1
          simpa using h2
        refine ⟨by positivity, ?_, ?_⟩
        · rw [div_lt_div_iff₀ hbl0 hbl0]
          nlinarith [hbl0]
        · rw [div_le_one hbl0]; linarith)
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  obtain ⟨C, hC, N0, hmain⟩ := exists_joint_small_tail_count hc2 ha2 hr1 hε
  refine ⟨C, hC, N0, fun N hN => ?_⟩
  obtain ⟨k, hkr, T, hcard, hlt, hkill, hsurv, hall⟩ := hmain N hN
  refine le_trans hcard ?_
  have hwitness : ∀ m ∈ T, ∀ b ∈ S,
      ⌊(b : ℝ) ^ lengths b * orbit b (CastingOut.erdosBorweinAtBase b) m⌋ = (values b : ℤ) := by
    intro m hm b hbS
    have hb2' := hb2 b hbS
    have hb0 : (0 : ℝ) < b := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb2'
      linarith
    have hbl0 : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
    obtain ⟨hlen, hval⟩ := hwin b hbS
    obtain ⟨hlo, hhi⟩ := hbox b hbS
    obtain ⟨hT0, hTε⟩ := hall m hm b hb2'
    have hmargin : ε / 2 ≤ (1 / 2) / (b : ℝ) ^ lengths b := by
      have h1 : ((b ^ lengths b : ℕ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPbig b hbS
      have h2 : (b : ℝ) ^ lengths b ≤ (P : ℝ) := by simpa using h1
      rw [hεdef, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h2, hbl0]
    exact floor_digit_of_common_offset b (lengths b) (values b) c a r k m hb2' (hbc b hbS)
      hval hkr (hkill m hm) (hsurv m hm) hlo hhi hT0 (lt_of_lt_of_le hTε hmargin)
  exact_mod_cast jointWordCount_ge_of_subset T hlt hwitness

/-- **The power count.**  For each fixed `ε > 0`, eventually `A(N) ≥ N^{1-ε}`.
Derived from `jointWords_quantitative` and `iteratedLog_rate_le_eps_log`; `ε > 1` is
allowed by the stated type and is covered by the same argument. -/
theorem jointWords_power_count (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b)
    (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) ^ (1 - ε) ≤ (jointWordCount S lengths values N : ℝ) := by
  obtain ⟨C, hC, N1, hN1⟩ := jointWords_quantitative S hb2 lengths values hwin
  obtain ⟨N2, hN2⟩ := iteratedLog_rate_le_eps_log C ε hC hε
  refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 _) hN)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  refine le_trans ?_ (hN1 N hN1')
  -- `N ^ (1 - ε) = N * exp (-ε * log N) ≤ N * exp (-C * (log log N)^2 * log log log N)`
  have hkey := hN2 N hN2'
  have hrw : (N : ℝ) ^ (1 - ε) = (N : ℝ) * Real.exp (-ε * Real.log (N : ℝ)) := by
    rw [Real.rpow_def_of_pos hNR,
      show Real.log (N : ℝ) * (1 - ε) = Real.log (N : ℝ) + -ε * Real.log (N : ℝ) by ring,
      Real.exp_add, Real.exp_log hNR]
  rw [hrw]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hNR.le
  nlinarith [hkey]

/-! ### Permanent audit examples for the ratified endpoints -/

/-- Exact-type audit anchor for the main count. -/
example (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b) (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (Real.log (N : ℝ))) ^ 2
        * Real.log (Real.log (Real.log (N : ℝ))))
          ≤ (jointWordCount S lengths values N : ℝ) :=
  jointWords_quantitative S hb2 lengths values hwin

/-- Exact-type audit anchor for the power count. -/
example (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b) (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) ^ (1 - ε) ≤ (jointWordCount S lengths values N : ℝ) :=
  jointWords_power_count S hb2 lengths values hwin ε hε

/-- The multiplicatively dependent specialization `S = {2, 4}`, with the binary word `11`
(`lengths 2 = 2`, `values 2 = 3`) and the leading-zero base-4 word `0` (`values 4 = 0`). -/
example : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) ^ (1 - (1 / 2 : ℝ))
      ≤ (jointWordCount ({2, 4} : Finset ℕ)
          (fun b => if b = 2 then 2 else 1) (fun b => if b = 2 then 3 else 0) N : ℝ) := by
  refine jointWords_power_count _ (by decide) _ _ ?_ (1 / 2) (by norm_num)
  decide

end NormalNumbers.JointLambert
