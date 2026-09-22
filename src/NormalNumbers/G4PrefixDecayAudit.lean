import NormalNumbers.G4WindowK

/-!
# A trivial-window obstruction and a usable replacement interface

The original PrefixDecay quantifies over every k>=1 even when all phases
are integral.  At h=4,k=1 the sum is M, not o(M).  Preserve that definition
and prove its failure rather than silently changing a frozen statement.
The replacement allows a fixed lower cutoff depending on h.  It remains
an OPEN analytic input, not a proof of G4 normality.
-/

open Filter Topology Finset
open scoped BigOperators
namespace NormalNumbers.G4
open NormalNumbers.PrimeLambert

theorem fullPrefixSum_four_one (M : ℕ) : fullPrefixSum 4 1 M = (M : ℂ) := by
  have hp : ∀ m, ePhase ((4 : ℝ) * truncTail 1 m) = 1 := by
    intro m
    have ht : (4 : ℝ) * truncTail 1 m = omegaR (m+1) := by
      simp [truncTail]
      ring
    rw [ht]
    have hi := ePhase_add_int 0 (ArithmeticFunction.cardDistinctFactors (m+1) : ℤ)
    simpa [omegaR, ePhase] using hi
  simp only [fullPrefixSum, Int.cast_ofNat, hp, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]

theorem prefixDecay_four_false : ¬ PrefixDecay 4 := by
  intro h
  obtain ⟨M₀, hM₀⟩ := (h (1/2) (by norm_num)).exists_forall_of_atTop
  have hb := hM₀ (max M₀ 1) (le_max_left _ _) 1 le_rfl
    (by unfold windowK; omega)
  rw [fullPrefixSum_four_one, Complex.norm_natCast] at hb
  have hpos : (0 : ℝ) < (max M₀ 1 : ℕ) := by
    exact_mod_cast (show 0 < max M₀ 1 by omega)
  linarith

/-- Corrected sufficient input: cancellation for all sufficiently long windows,
uniformly up to the triple-log schedule.  Still unproved. -/
def EventualPrefixDecay (h : ℤ) : Prop :=
  ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ M : ℕ in atTop, ∀ k, k₀ ≤ k → k ≤ windowK M →
      ‖fullPrefixSum h k M‖ ≤ ε * M

theorem windowDecayK_of_eventualPrefixDecay {h : ℤ}
    (hP : EventualPrefixDecay h) : WindowDecayK h := by
  obtain ⟨k₀, hk₀, hP⟩ := hP
  show Tendsto (fun N => fullWindowMean N (windowK N) h) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := (hP (ε/6) (by linarith)).exists_forall_of_atTop
  obtain ⟨N₀, hN₀⟩ := (tendsto_windowK.eventually_ge_atTop k₀).exists_forall_of_atTop
  refine ⟨max (max M₀ N₀) 1, fun N hN => ?_⟩
  have hNM : M₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN : N₀ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hA := hM₀ N hNM (windowK N) (hN₀ N hNN) le_rfl
  have hB := hM₀ (2*N) (by omega) (windowK N) (hN₀ N hNN)
    (windowK_mono (by omega))
  have hB' : ‖fullPrefixSum h (windowK N) (2*N)‖ ≤ ε/6*(2*(N:ℝ)) := by
    simpa using hB
  rw [dist_eq_norm, sub_zero, fullWindowMean_eq_prefixSum, norm_div, Complex.norm_natCast]
  rw [div_lt_iff₀ hNpos]
  have := norm_sub_le (fullPrefixSum h (windowK N) (2*N)) (fullPrefixSum h (windowK N) N)
  nlinarith

theorem isNormal_G4_of_eventualPrefixDecay
    (hP : ∀ h : ℤ, h ≠ 0 → EventualPrefixDecay h) :
    IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_windowDecayK (fun h hh => windowDecayK_of_eventualPrefixDecay (hP h hh))

/-- info: 'NormalNumbers.G4.prefixDecay_four_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefixDecay_four_false

end NormalNumbers.G4
