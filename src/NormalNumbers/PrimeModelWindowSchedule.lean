import NormalNumbers.PrimeModelGradedTiers

/-!
# Theorem A in schedule form

Leaf **G5b** of the graded-state regrade: fuse the graded window bound
`KMT.window_bound_gradedGM` with the band-tier per-atom bound
`BlockSieve.empLawG_lower_atom_bands`.  The result, `window_bound_schedule`, has **no model or
sieve hypothesis left**: every input is a number attached to the cutoff chain

    y_0 > y_1 > … > y_{k−1} > 2k,     lo b = y_{b+1}  (lo = 2k on the bottom band),

together with the level count `L`, the tier weights `u_b` and the Markov thresholds `T_j`.  The
class count is the canonical `d_q = #{j : q ≤ y_j}`, clipped to `0` below `2k` so that the
sieve's `2 d_q ≤ q` holds globally (this is the paper's `Q = primorial (2k)` split).

    ‖W_N‖ ≤ ∑_j a_j (2 S_P(y_j, N) + k/N)                                   (E1)
            + 2 ∑_j e^20 / T_j^{1/(2 log y_j)} + 0.6 ∑_b e^{−u_b}
              + 2 (2k)# (∏_j ⌊T_j⌋) R²/N                                    (E4)
            + e^{2k} exp(−∑_{p ∈ P, p ≤ y_{j₀}} 1/p),                       (E5)

with `log R = ∑_b (128(b+1) + 4u_b + 14) log y_b`.  The support level is now **graded**: band `b`
costs `128(b+1) log y_b`, not `128k log y_b`, which is exactly the collapse the review lap's
refutation demanded.  Choosing the schedule (Astra §8/§11) and driving the five terms to `0` is
the remaining lap.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.BlockSieve

variable (S : ℕ → Prop) [DecidablePred S]

/-- The canonical class count of a cutoff chain, clipped below `2k`. -/
noncomputable def chainCount (k : ℕ) (y : Fin k → ℕ)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i) : ℕ → ℕ :=
  fun q => if 2 * k ≤ q then (exists_dp_schedule k y hmono).choose q else 0

theorem chainCount_le (k : ℕ) (y : Fin k → ℕ) (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i)
    (q : ℕ) : chainCount k y hmono q ≤ k := by
  rw [chainCount]
  split
  · exact (exists_dp_schedule k y hmono).choose_spec.1 q
  · exact Nat.zero_le _

theorem two_mul_chainCount_le (k : ℕ) (y : Fin k → ℕ)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i) (q : ℕ) :
    2 * chainCount k y hmono q ≤ q := by
  rw [chainCount]
  split
  · have := (exists_dp_schedule k y hmono).choose_spec.1 q
    omega
  · omega

theorem chainCount_spec (k : ℕ) (y : Fin k → ℕ)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i) {q : ℕ} (hq : 2 * k ≤ q) (j : Fin k) :
    q ≤ y j ↔ (j : ℕ) < chainCount k y hmono q := by
  rw [chainCount, if_pos hq]
  exact (exists_dp_schedule k y hmono).choose_spec.2 q j

/-- **G5b, Theorem A in schedule form.**  Both halves of the graded regrade are now discharged:
the tier dimensions are the band indices `b + 1`, and the Markov moment at site `j` runs at the
sharp exponent `1/(2 log y_j)`. -/
theorem window_bound_schedule {k L : ℕ} (hk : 1 ≤ k)
    (y : Fin k → ℕ) (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i)
    (hmy : ∀ j, 2 * k ≤ y j) (hylog : ∀ j, 2 ≤ Real.log (y j))
    (lo : Fin k → ℕ)
    (hloin : ∀ (b : Fin k) (hb : (b : ℕ) + 1 < k), lo b = y ⟨(b : ℕ) + 1, hb⟩)
    (hlotop : ∀ b : Fin k, (b : ℕ) + 1 = k → lo b = 2 * k)
    (hcutlo : ∀ b : Fin k, cut (fun b : Fin k => ((y b : ℕ) : ℝ)) b L ≤ (lo b : ℝ))
    (hcut2 : ∀ b : Fin k, 2 ≤ cut (fun b : Fin k => ((y b : ℕ) : ℝ)) b L)
    (uu : Fin k → ℕ) (hT1 : ∑ b : Fin k, Real.exp (-(uu b : ℝ)) ≤ 1)
    {T : Fin k → ℝ} (hT : ∀ j, 1 ≤ T j)
    (h : ℤ) (hntw : NontrivialWindow k h) (x : ℕ) (hx : 0 < x) :
    ∃ j₀ : Fin k, (j₀ : ℕ) ≤ Nat.log 4 h.natAbs ∧
      ‖windowMeanS S k h x‖
        ≤ (∑ j : Fin k, siteBudget h j.val * (2 * recipSumIoc S (y j) x + (k : ℝ) / x))
          + (2 * (∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log (y j))))
              + 2 * (0.3 * ∑ b : Fin k, Real.exp (-(uu b : ℝ)))
              + 2 * ((primorial (2 * k) : ℕ) : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ))
                  * (gradedLevel Finset.univ (fun b : Fin k => (b : ℕ) + 1) uu
                      (fun b : Fin k => ((y b : ℕ) : ℝ))) ^ 2 / x)
          + Real.exp (2 * k)
              * Real.exp (- ∑ p ∈ (midPrimes S (2 * k) (y ⟨0, hk⟩)).filter (fun p => p ≤ y j₀),
                  (1 : ℝ) / (p : ℝ)) := by
  classical
  set m : ℕ := 2 * k with hm
  set Y : ℕ := y ⟨0, hk⟩ with hY
  set dp : ℕ → ℕ := chainCount k y hmono with hdpdef
  set P : Finset ℕ := midPrimes S m Y with hPdef
  set Q : ℕ := primorial m with hQdef
  have hQpos : 0 < Q := primorial_pos m
  have hPm : ∀ q ∈ P, m < q := fun q hq => ((mem_midPrimes S).mp hq).2.2.1
  have hPprime : ∀ q ∈ P, Nat.Prime q := fun q hq => ((mem_midPrimes S).mp hq).1
  have hPY : ∀ q ∈ P, q ≤ Y := fun q hq => ((mem_midPrimes S).mp hq).2.2.2
  have hdpP : ∀ q ∈ P, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q := fun q hq j =>
    chainCount_spec k y hmono (le_of_lt (hPm q hq)) j
  have hQcop : ∀ p ∈ P, Nat.Coprime Q p := fun p hp =>
    primorial_coprime_of_lt (hPprime p hp) (hPm p hp)
  have hyY : ∀ j, y j ≤ Y := fun j => hmono ⟨0, hk⟩ j (by simp [Fin.le_def])
  -- the per-atom bound, with the tier family discharged
  have hlower := fun t : JointState k P Q =>
    empLawG_lower_atom_bands (k := k) (m := m) (L := L) hk (by omega) y hmy hmono
      lo hloin (by simpa [hm] using hlotop) hcutlo hcut2
      (P := P) hPm (fun q hq => hPY q hq) hPprime
      dp (two_mul_chainCount_le k y hmono) (chainCount_le k y hmono) hdpP
      uu hT1 hQpos hx hQcop t
  refine window_bound_gradedGM S k m y Y hk (by omega) h hntw x hx dp
    (chainCount_le k y hmono) hdpP hmono hmy hyY hylog hT (by positivity) (by positivity)
    (fun t => ?_)
  have := hlower t
  have hgoal : (1 - 0.3 * ∑ b : Fin k, Real.exp (-(uu b : ℝ)))
      = (1 - (0.3 * ∑ b : Fin k, Real.exp (-(uu b : ℝ)))) := by ring
  linarith [this]

end NormalNumbers.PrimeModel.KMT

#print axioms NormalNumbers.PrimeModel.KMT.window_bound_schedule
