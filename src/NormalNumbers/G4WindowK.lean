import NormalNumbers.G4WiringCRT
import NormalNumbers.G4FarTail

/-!
# The triple-log site schedule `windowK` and the o(1) crux `PrefixDecay`
(KICKOFF-2026-09-20-windowK-lap.md)

Probe 13 (`probes/window_truncation.py`) settled the fixed-`K` question: truncating the window to a
FIXED number of sites does not work (the `K`-site and `J`-site means differ by `≍ 4^{-K}`, uniformly
in `N`), but `K → ∞` does, and it only needs the *average* of `ω` over the window (`≍ log log N`),
not its maximum (`≍ log N`).  So the schedule drops from double-log (`windowJ`) to **triple-log**
(`windowK`), and the crux can be stated in pure `o(1)` form with no sector split, no main terms and
no constants: `PrefixDecay`.
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.G4

open NormalNumbers.PrimeLambert

/-- The triple-log site schedule: `2^{windowK N} > log₂ log₂ N`, so `4^{windowK N} > (log₂ log₂ N)²`. -/
def windowK (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (Nat.log 2 N)) + 1

theorem windowK_le_windowJ (N : ℕ) : windowK N ≤ windowJ N := by
  have := Nat.log_le_self 2 (Nat.log 2 (Nat.log 2 N))
  simpa [windowK, windowJ] using this

theorem windowK_mono : Monotone windowK := fun a b hab => by
  have h1 : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right hab
  have h2 : Nat.log 2 (Nat.log 2 a) ≤ Nat.log 2 (Nat.log 2 b) := Nat.log_mono_right h1
  have h3 : Nat.log 2 (Nat.log 2 (Nat.log 2 a)) ≤ Nat.log 2 (Nat.log 2 (Nat.log 2 b)) :=
    Nat.log_mono_right h2
  simpa [windowK] using h3

theorem tendsto_windowK : Tendsto windowK atTop atTop :=
  tendsto_atTop_atTop.mpr (fun b =>
    ⟨2 ^ (2 ^ (2 ^ b)), fun a ha => by
      have h1 : 2 ^ (2 ^ b) ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) ha
      have h2 : 2 ^ b ≤ Nat.log 2 (Nat.log 2 a) := Nat.le_log_of_pow_le (by norm_num) h1
      have h3 : b ≤ Nat.log 2 (Nat.log 2 (Nat.log 2 a)) := Nat.le_log_of_pow_le (by norm_num) h2
      simpa [windowK] using Nat.le_succ_of_le h3⟩)

/-- Geometric tail: `∑_{K ≤ j < J} 4^{-(j+1)} ≤ 4^{-K}`. -/
lemma geom_tail_le (K J : ℕ) :
    ∑ j ∈ Finset.Ico K J, (1 : ℝ) / 4 ^ (j + 1) ≤ 1 / 4 ^ K := by
  rcases le_or_gt K J with h | h
  · rw [Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i ∈ Finset.range (J - K), (1 : ℝ) / 4 ^ (K + i + 1)
        = (1 / 4 : ℝ) ^ (K + 1) * (1 / 4 : ℝ) ^ i := by
      intro i _
      rw [show K + i + 1 = (K + 1) + i by omega, pow_add, div_pow, div_pow, one_pow, one_pow,
        div_mul_div_comm, one_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hgeo : ∑ i ∈ Finset.range (J - K), (1 / 4 : ℝ) ^ i ≤ 4 / 3 := by
      rw [geom_sum_eq (by norm_num)]
      have h1 : (0:ℝ) < (1/4:ℝ) ^ (J - K) := by positivity
      rw [div_le_iff_of_neg (by norm_num : (1/4:ℝ) - 1 < 0)]
      nlinarith
    calc (1 / 4 : ℝ) ^ (K + 1) * ∑ i ∈ Finset.range (J - K), (1 / 4 : ℝ) ^ i
        ≤ (1 / 4 : ℝ) ^ (K + 1) * (4 / 3) :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = (1 / 4 : ℝ) ^ K * (1 / 3) := by rw [pow_succ]; ring
      _ ≤ (1 / 4 : ℝ) ^ K := by nlinarith [pow_pos (show (0:ℝ) < 1/4 by norm_num) K]
      _ = 1 / 4 ^ K := by rw [div_pow, one_pow]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- Dropping sites `K < j ≤ J` costs the L¹ tail of the phase, by the Lipschitz bound on `ePhase`. -/
theorem norm_fullWindowMean_sub_le (N : ℕ) (h : ℤ) (K J : ℕ) (hK : K ≤ J) (hN : 0 < N) :
    ‖fullWindowMean N J h - fullWindowMean N K h‖
      ≤ 4 * Real.pi * |(h : ℝ)|
          * (∑ n ∈ Finset.Ico N (2 * N), ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1)) / N := by
  have hdiff : ∀ n : ℕ, truncTail J n - truncTail K n
      = ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1) := by
    intro n
    rw [truncTail, truncTail, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun j => omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1))
        (Nat.zero_le K) hK]
    ring
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hsub : fullWindowMean N J h - fullWindowMean N K h
      = (∑ n ∈ Finset.Ico N (2 * N),
          (ePhase (h * truncTail J n) - ePhase (h * truncTail K n))) / N := by
    rw [fullWindowMean, fullWindowMean, ← sub_div, ← Finset.sum_sub_distrib]
  rw [hsub, norm_div, Complex.norm_natCast]
  rw [div_le_div_iff₀ hNpos hNpos]
  have hbound : ‖∑ n ∈ Finset.Ico N (2 * N),
        (ePhase (h * truncTail J n) - ePhase (h * truncTail K n))‖
      ≤ 4 * Real.pi * |(h : ℝ)|
          * ∑ n ∈ Finset.Ico N (2 * N),
              ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1) := by
    calc ‖∑ n ∈ Finset.Ico N (2 * N),
            (ePhase (h * truncTail J n) - ePhase (h * truncTail K n))‖
        ≤ ∑ n ∈ Finset.Ico N (2 * N),
            ‖ePhase (h * truncTail J n) - ePhase (h * truncTail K n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico N (2 * N), 4 * Real.pi * |(h : ℝ)|
            * ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have hnn : (0:ℝ) ≤ ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1) :=
            Finset.sum_nonneg (fun j _ => by
              have := omegaR_nonneg (n + j + 1); positivity)
          calc ‖ePhase (h * truncTail J n) - ePhase (h * truncTail K n)‖
              ≤ 4 * Real.pi * |(h : ℝ) * truncTail J n - (h : ℝ) * truncTail K n| :=
                norm_ePhase_sub _ _
            _ = 4 * Real.pi * |(h : ℝ)| * |truncTail J n - truncTail K n| := by
                rw [← mul_sub, abs_mul]; ring
            _ = 4 * Real.pi * |(h : ℝ)|
                  * ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1) := by
                rw [hdiff n, abs_of_nonneg hnn]
      _ = 4 * Real.pi * |(h : ℝ)|
            * ∑ n ∈ Finset.Ico N (2 * N),
                ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1) := by
          rw [← Finset.mul_sum]
  nlinarith [hbound, hNpos]

/-- The window average of `ω(n+j+1)` on `[N, 2N)` is `≤ log₂(4(log 4N + 1))`, uniformly for the
shifts `j` that occur in the window (`sum_omegaR_add_le` with `X = 2N`, `ρ = j+1`). -/
lemma sum_window_omegaR_le {N j : ℕ} (hN : 1 ≤ N) (hj : j + 1 ≤ 2 * N) :
    ∑ n ∈ Finset.Ico N (2 * N), omegaR (n + j + 1)
      ≤ N * (Real.log (4 * (Real.log (4 * N) + 1)) / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hsub : Finset.Ico N (2 * N) ⊆ Finset.range (2 * N) := by
    intro x hx; simp only [Finset.mem_Ico] at hx; simp only [Finset.mem_range]; omega
  have hne : (Finset.Ico N (2 * N)).Nonempty := ⟨N, by simp only [Finset.mem_Ico]; omega⟩
  have hcard : (Finset.Ico N (2 * N)).card = N := by rw [Nat.card_Ico]; omega
  have key := sum_omegaR_add_le (X := 2 * N) (Finset.Ico N (2 * N)) hsub hne
    (ρ := j + 1) (by omega)
  rw [hcard] at key
  have hrw : ∑ n ∈ Finset.Ico N (2 * N), omegaR (n + (j + 1))
      = ∑ n ∈ Finset.Ico N (2 * N), omegaR (n + j + 1) := by
    refine Finset.sum_congr rfl (fun n _ => ?_); rw [← Nat.add_assoc]
  rw [hrw] at key
  refine key.trans ?_
  set t : ℝ := ((2 * N + (j + 1) : ℕ) : ℝ) with ht
  have ht1 : (1:ℝ) ≤ t := by
    rw [ht]; have : (1:ℕ) ≤ 2 * N + (j + 1) := by omega
    exact_mod_cast this
  have ht4 : t ≤ 4 * (N:ℝ) := by
    rw [ht]; have : (2 * N + (j + 1) : ℕ) ≤ 4 * N := by omega
    exact_mod_cast this
  have htpos : (0:ℝ) < t := by linarith
  have hlogt : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht1
  have hlogle : Real.log t ≤ Real.log (4 * N) := Real.log_le_log htpos ht4
  have hNpos : (0:ℝ) < N := by linarith
  have hstep : t * (Real.log t + 1) / N ≤ 4 * (Real.log (4 * N) + 1) := by
    have h1 : t * (Real.log t + 1) ≤ (4 * (N:ℝ)) * (Real.log (4 * N) + 1) := by
      apply mul_le_mul ht4 (by linarith) (by linarith) (by linarith)
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hposarg : (0:ℝ) < t * (Real.log t + 1) / N := by positivity
  have hlogmono := Real.log_le_log hposarg hstep
  rw [mul_div_assoc]
  have h2 : Real.log (t * (Real.log t + 1) / N) / Real.log 2
      ≤ Real.log (4 * (Real.log (4 * N) + 1)) / Real.log 2 := by gcongr
  nlinarith [h2, hNpos]

/-- `log₂(4(log 4N + 1)) ≤ log₂ log₂ N + 6`: the window average of `ω` is `O(log log N)`. -/
lemma logB_le (N : ℕ) (hN : 2 ≤ N) :
    Real.log (4 * (Real.log (4 * N) + 1)) / Real.log 2
      ≤ (Nat.log 2 (Nat.log 2 N) : ℝ) + 6 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  set L1 := Nat.log 2 N with hL1
  set L2 := Nat.log 2 L1 with hL2
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  -- `4N < 2^(L1+3)`
  have h1 : (N:ℝ) < (2:ℝ) ^ (L1 + 1) := by
    have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) N
    exact_mod_cast this
  have h4N : (4:ℝ) * N < (2:ℝ) ^ (L1 + 3) := by
    have : (2:ℝ) ^ (L1 + 3) = 4 * (2:ℝ) ^ (L1 + 1) := by
      rw [show L1 + 3 = (L1 + 1) + 2 by omega, pow_add]; ring
    rw [this]; linarith
  have h4Npos : (0:ℝ) < 4 * N := by linarith
  have hlog4N : Real.log (4 * N) ≤ ((L1 : ℝ) + 3) * Real.log 2 := by
    have := Real.log_le_log h4Npos h4N.le
    rwa [Real.log_pow, show ((L1 + 3 : ℕ) : ℝ) = (L1 : ℝ) + 3 by push_cast; ring] at this
  have hlog4N' : Real.log (4 * N) + 1 ≤ (L1 : ℝ) + 4 := by
    have hL1nn : (0:ℝ) ≤ (L1 : ℝ) + 3 := by positivity
    nlinarith
  have hlogpos : (0:ℝ) ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
  -- `L1 + 1 ≤ 2^(L2+1)`
  have h2 : (L1 : ℝ) + 1 ≤ (2:ℝ) ^ (L2 + 1) := by
    have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) L1
    have h' : (L1 : ℝ) < (2:ℝ) ^ (L2 + 1) := by exact_mod_cast this
    have hnat : L1 + 1 ≤ 2 ^ (L2 + 1) := this
    exact_mod_cast hnat
  have hkey : 4 * (Real.log (4 * N) + 1) ≤ (2:ℝ) ^ (L2 + 6) := by
    have hpow : (2:ℝ) ^ (L2 + 6) = 32 * (2:ℝ) ^ (L2 + 1) := by
      rw [show L2 + 6 = (L2 + 1) + 5 by omega, pow_add]; norm_num; ring
    have hL1nn : (0:ℝ) ≤ (L1 : ℝ) := by positivity
    rw [hpow]
    nlinarith
  have hargpos : (0:ℝ) < 4 * (Real.log (4 * N) + 1) := by linarith
  have := Real.log_le_log hargpos hkey
  rw [Real.log_pow, show ((L2 + 6 : ℕ) : ℝ) = (L2 : ℝ) + 6 by push_cast; ring] at this
  rw [div_le_iff₀ hlog2]
  nlinarith

/-- `(log₂ log₂ N)² < 4^{windowK N}` — this is what the triple-log schedule buys. -/
lemma sq_lt_four_pow_windowK (N : ℕ) :
    ((Nat.log 2 (Nat.log 2 N) : ℝ)) ^ 2 < (4:ℝ) ^ (windowK N) := by
  set L2 := Nat.log 2 (Nat.log 2 N) with hL2
  have hlt : (L2 : ℝ) < (2:ℝ) ^ (Nat.log 2 L2 + 1) := by
    have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) L2
    exact_mod_cast this
  have hnn : (0:ℝ) ≤ (L2 : ℝ) := by positivity
  have hpow : ((2:ℝ) ^ (Nat.log 2 L2 + 1)) ^ 2 = (4:ℝ) ^ (windowK N) := by
    rw [windowK, ← hL2, ← pow_mul, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  rw [← hpow]
  exact pow_lt_pow_left₀ hlt hnn (by norm_num)

/-- The tail is `o(1)` along `K = windowK N`. -/
theorem window_tail_tendsto_zero (h : ℤ) :
    Tendsto (fun N : ℕ => ‖fullWindowMean N (windowJ N) h - fullWindowMean N (windowK N) h‖)
      atTop (𝓝 0) := by
  have hL2tend : Tendsto (fun N : ℕ => ((Nat.log 2 (Nat.log 2 N) : ℕ) : ℝ)) atTop atTop := by
    have hnat : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
      tendsto_atTop_atTop.mpr (fun b => ⟨2 ^ (2 ^ b), fun a ha => by
        have h1 : 2 ^ b ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) ha
        exact Nat.le_log_of_pow_le (by norm_num) h1⟩)
    exact tendsto_natCast_atTop_atTop.comp hnat
  have hg : Tendsto
      (fun N : ℕ => 28 * Real.pi * |(h:ℝ)| * ((Nat.log 2 (Nat.log 2 N) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (hL2tend.inv_tendsto_atTop).const_mul (28 * Real.pi * |(h:ℝ)|)
  refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_ hg
  filter_upwards [eventually_ge_atTop 16] with N hN
  set K := windowK N with hK
  set J := windowJ N with hJ
  set L2 := Nat.log 2 (Nat.log 2 N) with hL2
  set B := Real.log (4 * (Real.log (4 * N) + 1)) / Real.log 2 with hB
  have hNpos : 0 < N := by omega
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hNpos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBnn : (0:ℝ) ≤ B := by
    rw [hB]
    have h1 : (0:ℝ) ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    exact div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  have hKJ : K ≤ J := windowK_le_windowJ N
  have hJN : J ≤ N + 1 := by
    have h1 : Nat.log 2 N ≤ N := Nat.log_le_self 2 N
    have h2 : Nat.log 2 (Nat.log 2 N) ≤ Nat.log 2 N := Nat.log_le_self 2 _
    simp only [hJ, windowJ]; omega
  -- the L¹ tail, summed
  set S : ℝ := ∑ n ∈ Finset.Ico N (2 * N), ∑ j ∈ Finset.Ico K J,
      omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1) with hS
  have hSbd : S ≤ (N:ℝ) * B / 4 ^ K := by
    have h1 : S = ∑ j ∈ Finset.Ico K J,
        (∑ n ∈ Finset.Ico N (2 * N), omegaR (n + j + 1)) / (4:ℝ) ^ (j + 1) := by
      rw [hS, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_div])
    rw [h1]
    have hjb : ∀ j ∈ Finset.Ico K J,
        (∑ n ∈ Finset.Ico N (2 * N), omegaR (n + j + 1)) / (4:ℝ) ^ (j + 1)
          ≤ ((N:ℝ) * B) / (4:ℝ) ^ (j + 1) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hj2 : j + 1 ≤ 2 * N := by omega
      have := sum_window_omegaR_le (N := N) (j := j) hNpos hj2
      gcongr
    calc ∑ j ∈ Finset.Ico K J,
          (∑ n ∈ Finset.Ico N (2 * N), omegaR (n + j + 1)) / (4:ℝ) ^ (j + 1)
        ≤ ∑ j ∈ Finset.Ico K J, ((N:ℝ) * B) / (4:ℝ) ^ (j + 1) := Finset.sum_le_sum hjb
      _ = (N:ℝ) * B * ∑ j ∈ Finset.Ico K J, (1:ℝ) / 4 ^ (j + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ (N:ℝ) * B * (1 / 4 ^ K) :=
          mul_le_mul_of_nonneg_left (geom_tail_le K J) (by positivity)
      _ = (N:ℝ) * B / 4 ^ K := by ring
  -- the final numeric chain
  have hpowpos : (0:ℝ) < (4:ℝ) ^ K := by positivity
  have hL2ge : (2:ℝ) ≤ (L2 : ℝ) := by
    have h1 : 4 ≤ Nat.log 2 N := by
      have h0 : Nat.log 2 16 ≤ Nat.log 2 N := Nat.log_mono_right hN
      have he : Nat.log 2 16 = 4 := by decide
      omega
    have h2 : 2 ≤ Nat.log 2 (Nat.log 2 N) := by
      have h0 : Nat.log 2 4 ≤ Nat.log 2 (Nat.log 2 N) := Nat.log_mono_right h1
      have he : Nat.log 2 4 = 2 := by decide
      omega
    exact_mod_cast h2
  have hBle : B ≤ (L2 : ℝ) + 6 := logB_le N (by omega)
  have hsq : ((L2:ℝ)) ^ 2 < (4:ℝ) ^ K := sq_lt_four_pow_windowK N
  have hratio : B / 4 ^ K ≤ 7 / (L2 : ℝ) := by
    rw [div_le_div_iff₀ hpowpos (by linarith)]
    nlinarith
  have hSN : S / N ≤ B / 4 ^ K := by
    have hNpos' : (0:ℝ) < N := by linarith
    rw [div_le_div_iff₀ hNpos' hpowpos]
    have := hSbd
    rw [le_div_iff₀ hpowpos] at this
    nlinarith
  have hc : (0:ℝ) ≤ 4 * Real.pi * |(h:ℝ)| := by positivity
  calc ‖fullWindowMean N J h - fullWindowMean N K h‖
      ≤ 4 * Real.pi * |(h : ℝ)| * S / N :=
        norm_fullWindowMean_sub_le N h K J hKJ hNpos
    _ = 4 * Real.pi * |(h : ℝ)| * (S / N) := by ring
    _ ≤ 4 * Real.pi * |(h : ℝ)| * (7 / (L2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hSN.trans hratio) hc
    _ = 28 * Real.pi * |(h : ℝ)| * ((L2 : ℝ))⁻¹ := by
        rw [div_eq_mul_inv]; ring

/-- **Node N0′**: window decay along the triple-log schedule. -/
def WindowDecayK (h : ℤ) : Prop :=
  Tendsto (fun N => fullWindowMean N (windowK N) h) atTop (𝓝 0)

theorem windowDecay_of_windowDecayK {h : ℤ} (hK : WindowDecayK h) : WindowDecay h := by
  have hK' : Tendsto (fun N => fullWindowMean N (windowK N) h) atTop (𝓝 0) := hK
  show Tendsto (fun N => fullWindowMean N (windowJ N) h) atTop (𝓝 0)
  refine squeeze_zero_norm' (a := fun N => ‖fullWindowMean N (windowJ N) h
      - fullWindowMean N (windowK N) h‖ + ‖fullWindowMean N (windowK N) h‖) ?_ ?_
  · filter_upwards with N
    have hle := norm_add_le (fullWindowMean N (windowJ N) h - fullWindowMean N (windowK N) h)
      (fullWindowMean N (windowK N) h)
    simpa using hle
  · simpa using (window_tail_tendsto_zero h).add hK'.norm

theorem isNormal_G4_of_windowDecayK (hW : ∀ h : ℤ, h ≠ 0 → WindowDecayK h) :
    IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_windowDecay (fun h hh => windowDecay_of_windowDecayK (hW h hh))

/-- Partial sums of the full `k`-site phase product. -/
noncomputable def fullPrefixSum (h : ℤ) (k M : ℕ) : ℂ :=
  ∑ m ∈ Finset.range M, ePhase (h * truncTail k m)

/-- **The crux in o(1) form, no sectors**: Elliott-type decay for the `ω`-twists
`∏_{j≤k} e(h/4^j)^{ω(m+j)}` at `k` shifts, uniformly for `k ≤ windowK M`, for every `h ≠ 0`. -/
def PrefixDecay (h : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowK M → ‖fullPrefixSum h k M‖ ≤ ε * M

theorem fullWindowMean_eq_prefixSum (N J : ℕ) (h : ℤ) :
    fullWindowMean N J h = (fullPrefixSum h J (2 * N) - fullPrefixSum h J N) / N := by
  unfold fullWindowMean fullPrefixSum
  congr 1
  rw [eq_sub_iff_add_eq, Finset.range_eq_Ico, Finset.range_eq_Ico, add_comm,
    Finset.sum_Ico_consecutive _ (Nat.zero_le N) (by omega)]

theorem windowDecayK_of_prefixDecay {h : ℤ} (hP : PrefixDecay h) : WindowDecayK h := by
  show Tendsto (fun N => fullWindowMean N (windowK N) h) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := (hP (ε / 6) (by linarith)).exists_forall_of_atTop
  refine ⟨max M₀ 1, fun N hN => ?_⟩
  have hNM : M₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hk1 : 1 ≤ windowK N := Nat.le_add_left 1 _
  have hkN : windowK N ≤ windowK N := le_rfl
  have hk2N : windowK N ≤ windowK (2 * N) := windowK_mono (by omega)
  have hA : ‖fullPrefixSum h (windowK N) N‖ ≤ ε / 6 * N := hM₀ N hNM _ hk1 hkN
  have hB : ‖fullPrefixSum h (windowK N) (2 * N)‖ ≤ ε / 6 * ((2 * N : ℕ) : ℝ) :=
    hM₀ (2 * N) (by omega) _ hk1 hk2N
  have hBcast : ‖fullPrefixSum h (windowK N) (2 * N)‖ ≤ ε / 6 * (2 * (N : ℝ)) := by
    push_cast at hB ⊢; linarith
  rw [dist_eq_norm, sub_zero, fullWindowMean_eq_prefixSum, norm_div, Complex.norm_natCast]
  rw [div_lt_iff₀ hNpos]
  calc ‖fullPrefixSum h (windowK N) (2 * N) - fullPrefixSum h (windowK N) N‖
      ≤ ‖fullPrefixSum h (windowK N) (2 * N)‖ + ‖fullPrefixSum h (windowK N) N‖ :=
        norm_sub_le _ _
    _ ≤ ε / 6 * (2 * (N : ℝ)) + ε / 6 * N := by linarith
    _ < ε * N := by nlinarith

/-- **Headline**: G₄ is normal in base 4 if the `ω`-twist correlations decay at triple-log many
shifts. -/
theorem isNormal_G4_of_prefixDecay (hP : ∀ h : ℤ, h ≠ 0 → PrefixDecay h) :
    IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_windowDecayK (fun h hh => windowDecayK_of_prefixDecay (hP h hh))

end NormalNumbers.G4
