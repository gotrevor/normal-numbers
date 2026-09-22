import NormalNumbers.PrimeModelJointLaw
import NormalNumbers.PrimeModelRadicalStateGraded

/-!
# Theorem A, leg E4: the graded joint phase error

Lap 6e of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §2
("E4").  This is `JointLaw.joint_phase_error` with two changes:

* the retained box is the **graded** one, `retainedBoxG` with a per-shift threshold `T_j`, so
  E4a becomes `2 ∑_j e^{20} / T_j^{1/(2 log Y)}` and E4c becomes
  `2 Q (∏_j ⌊T_j⌋₊) R² / x`;
* the per-atom lower bound `(1 − η) μ(t) − R²/x ≤ ν(t)` is taken as a **hypothesis** rather than
  rebuilt: in the multicutoff argument it is supplied by the graded Brun sieve
  (`BlockSieve.graded_brun_lower`) rather than by the nested sieve of `PrimeModelBrunLower`.

**Deviation from Fable §2 (recorded).**  The paper's E4a runs the shift-`j` Markov moment over
the primes `≤ y_j` only, using that in the graded model a prime above `y_j` is never assigned to
shift `j`.  The radical model formalised here (`Radical.weight`) assigns every prime to every
shift with probability `1/p`, so the moment budget is taken over the full range `≤ Y` and is
uniform in `j`.  The per-shift freedom that Theorem C′ actually uses is the threshold `T_j`,
which is retained in full.  A shift-dependent prime family in the radical model would recover
the paper's sharper form; it is not needed downstream.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.JointLaw

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.BrunCount

variable {k : ℕ} (P : Finset ℕ) (Q x : ℕ)

open scoped Classical in
/-- The joint tail over the graded box reduces to the state tail. -/
lemma jointModel_tailG {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Type*) [Fintype R] [Nonempty R] (k : ℕ) (p : ι → ℕ) (T : Fin k → ℝ) :
    (∑ z ∈ (Finset.univ ×ˢ retainedBoxG k p T)ᶜ, jointModel R k (primeRecip p) z)
      = ∑ s ∈ (retainedBoxG k p T)ᶜ, weight k (primeRecip p) s := by
  classical
  have hcard : (0:ℝ) < (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := R)
  have hcompl : ((Finset.univ : Finset R) ×ˢ retainedBoxG k p T)ᶜ
      = (Finset.univ : Finset R) ×ˢ (retainedBoxG k p T)ᶜ := by
    ext z
    simp [Finset.mem_compl, Finset.mem_product]
  rw [hcompl, Finset.sum_product]
  simp only [jointModel]
  rw [Finset.sum_congr rfl (fun r _ => (Finset.sum_div _ _ _).symm), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Theorem A, leg E4 (graded).**  With a per-shift retained box and any per-atom lower
estimate `(1 − η) μ − R²/x ≤ ν` on the box, the empirical law transfers to the model with error
`2 ∑_j e^{20}/T_j^{1/(2 log Y)} + 2η + 2 Q (∏_j ⌊T_j⌋₊) R²/x`. -/
theorem joint_phase_errorG {Y : ℕ} (hk : 1 ≤ k) {T : Fin k → ℝ} {η Rsq : ℝ}
    (hylog : 2 ≤ Real.log Y)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ k < p ∧ p ≤ Y)
    (hQ : 0 < Q) (hx : 0 < x) (hT : ∀ j, 1 ≤ T j)
    (hη : 0 ≤ η) (hRsq : 0 ≤ Rsq)
    (hlower : ∀ t : JointState k P Q,
      (1 - η) * jointModel (Fin Q) k (primeRecip (primeOf P)) t - Rsq / x ≤ empLaw P Q x t)
    (F : JointState k P Q → ℂ) (hF : ∀ t, ‖F t‖ ≤ 1) :
    ‖(∑ t : JointState k P Q, (empLaw P Q x t : ℂ) * F t)
        - ∑ t : JointState k P Q, (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * F t‖
      ≤ 2 * (∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log Y)))
        + 2 * η
        + 2 * (Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * Rsq / x := by
  classical
  have hQne : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hppos : ∀ i : {q // q ∈ P}, 0 < primeOf P i := fun i => (hP i.1 i.2).1.pos
  have hprime : ∀ i : {q // q ∈ P}, (primeOf P i).Prime := fun i => (hP i.1 i.2).1
  have hkp : ∀ i : {q // q ∈ P}, k ≤ primeOf P i := fun i => (hP i.1 i.2).2.1.le
  have hinj : Function.Injective (primeOf P) := Subtype.val_injective
  have hY0 : (0 : ℝ) < (Y : ℝ) := by
    rcases Nat.eq_zero_or_pos Y with hz | hpos
    · rw [hz] at hylog
      norm_num at hylog
    · exact_mod_cast hpos
  have hle : ∀ i : {q // q ∈ P}, ((primeOf P i : ℕ) : ℝ) ≤ (Y : ℝ) := by
    intro i; exact_mod_cast (hP i.1 i.2).2.2
  set B : Finset (JointState k P Q) := Finset.univ ×ˢ retainedBoxG k (primeOf P) T with hB
  have hmain := finite_phase_of_lower_atoms
    (jointModel (Fin Q) k (primeRecip (primeOf P))) (empLaw P Q x) B
    η (fun _ => Rsq / x)
    (fun i => jointModel_nonneg hppos hkp i) (fun i => empLaw_nonneg P Q x i)
    (jointModel_mass_one (Fin Q) k (primeOf P)) (empLaw_mass_one P Q x hQ hx)
    hη (fun i _ => by positivity)
    (fun i _ => hlower i)
    F hF
  have htail : ∑ i ∈ Bᶜ, jointModel (Fin Q) k (primeRecip (primeOf P)) i
      ≤ ∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log Y)) := by
    have h1 := jointModel_tailG (Fin Q) k (primeOf P) T
    have h2 := radical_box_tailG_exp20 k (T := T) (y := fun _ => (Y : ℝ)) hinj hprime hkp
      (fun _ => hY0) (fun _ => hylog) (fun _ i => hle i) hT
    rw [hB]
    convert h1.trans_le h2 using 2
    ext a
    simp
  have hcardB : (B.card : ℝ) ≤ (Q : ℝ) * ∏ j : Fin k, (Nat.floor (T j) : ℝ) := by
    rw [hB, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    exact mul_le_mul_of_nonneg_left (retainedBoxG_card_le hprime hinj k hT) (by positivity)
  have he0 : (0 : ℝ) ≤ Rsq / x := by positivity
  have hsume : ∑ _i ∈ B, Rsq / x = (B.card : ℝ) * (Rsq / x) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hterm : (B.card : ℝ) * (Rsq / x)
      ≤ (Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * (Rsq / x) :=
    mul_le_mul_of_nonneg_right hcardB he0
  rw [hsume] at hmain
  have hshape : 2 * (Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * Rsq / x
      = 2 * ((Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * (Rsq / x)) := by ring
  rw [hshape]
  linarith

end NormalNumbers.PrimeModel.JointLaw
