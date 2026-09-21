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
  sorry

/-- The tail is `o(1)` along `K = windowK N`. -/
theorem window_tail_tendsto_zero (h : ℤ) :
    Tendsto (fun N : ℕ => ‖fullWindowMean N (windowJ N) h - fullWindowMean N (windowK N) h‖)
      atTop (𝓝 0) := by
  sorry

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
  sorry

/-- **Headline**: G₄ is normal in base 4 if the `ω`-twist correlations decay at triple-log many
shifts. -/
theorem isNormal_G4_of_prefixDecay (hP : ∀ h : ℤ, h ≠ 0 → PrefixDecay h) :
    IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_windowDecayK (fun h hh => windowDecayK_of_prefixDecay (hP h hh))

end NormalNumbers.G4
