import NormalNumbers.PrimeModelBrunCount
import NormalNumbers.PrimeModelRadicalState
import NormalNumbers.PrimeModelRadicalMoment
import NormalNumbers.PrimeModelLowerTransfer

/-!
# Prime model, assembly part C: the empirical joint law and its transfer

`papers/prime-model-assembly-2026-09-22.md`, "Empirical joint law" and "E4".

For `n < x` record `(n mod Q, actualState k P n) : Fin Q × (P → Option (Fin k))`.  The
normalised fibre counts `empLaw P Q x` form a probability law, the prefix mean of any
`F ∘ (residue, state)` is `∑ empLaw · F` (fibre-sum identity), and every atom satisfies the
Brun lower bound `empLaw ≥ (1 − 2e^{−σ/2}) · jointModel − R²/x` (via
`actual_state_sifted_iff`, `brun_sifted_count_lower`, `state_model_density`).  Feeding the
lower atoms on the retained box into `finite_phase_of_lower_atoms`, with the model tail
`radical_box_tail_exp20` and the box cardinality `retainedBox_card_le`, gives the transfer
bound `joint_phase_error`.

Nothing here mentions phases or `S`: `P` is an arbitrary finite set of primes in `(k, y]` and
`F` an arbitrary `1`-bounded test function.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.JointLaw

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.BrunCount

variable {k : ℕ} (P : Finset ℕ) (Q x : ℕ)

/-- The joint state space: residue modulo `Q` and radical state on `P`. -/
abbrev JointState (k : ℕ) (P : Finset ℕ) (Q : ℕ) : Type :=
  Fin Q × ({q // q ∈ P} → Option (Fin k))

/-- The empirical joint law of `(n mod Q, actualState k P n)` for `n < x`. -/
noncomputable def empLaw (t : JointState k P Q) : ℝ :=
  (((range x).filter (fun n => n % Q = t.1.val ∧ actualState k P n = t.2)).card : ℝ) / x

lemma empLaw_nonneg (t : JointState k P Q) : 0 ≤ empLaw P Q x t := by
  sorry

/-- The fibres partition `range x`. -/
theorem empLaw_mass_one (hQ : 0 < Q) (hx : 0 < x) :
    ∑ t : JointState k P Q, empLaw P Q x t = 1 := by
  sorry

/-- **Fibre-sum identity.**  The prefix mean of `F(n mod Q, state n)` is `∑_t empLaw t · F t`. -/
theorem prefixMean_eq_sum_empLaw (hQ : 0 < Q) (hx : 0 < x) (F : JointState k P Q → ℂ) :
    (∑ n ∈ range x, F (⟨n % Q, Nat.mod_lt n hQ⟩, actualState k P n)) / (x : ℂ)
      = ∑ t : JointState k P Q, (empLaw P Q x t : ℂ) * F t := by
  sorry

/-- The prime map of the model: `P` indexes itself. -/
abbrev primeOf (P : Finset ℕ) : {q // q ∈ P} → ℕ := fun i => (i : ℕ)

/-- **Lower atoms from the Brun count.**  For every residue and state,
`empLaw (r,s) ≥ (1 − 2e^{−σ/2}) · jointModel (r,s) − (y^σ)²/x`. -/
theorem empLaw_lower_atom {y : ℕ} (hk : 1 ≤ k) {σ : ℝ}
    (hy : Real.exp 2 ≤ (y : ℝ)) (hσ : 1920 * (k : ℝ) ≤ σ)
    (hσA : 40 * Real.log ((4 : ℝ) ^ k * Real.exp (16 * k)) + 4 ≤ σ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ k < p ∧ p ≤ y)
    (hQ : 0 < Q) (hQcop : ∀ p ∈ P, Nat.Coprime Q p) (hx : 0 < x)
    (t : JointState k P Q) :
    (1 - 2 * Real.exp (-σ / 2)) * jointModel (Fin Q) k (primeRecip (primeOf P)) t
        - ((y : ℝ) ^ σ) ^ 2 / x
      ≤ empLaw P Q x t := by
  sorry

/-- **E4, the transfer.**  For every `1`-bounded `F`,
`‖∑ empLaw·F − ∑ jointModel·F‖ ≤ 2·(k e^{20}/T^{1/(2 log y)}) + 4e^{−σ/2} + 2 Q ⌊T⌋₊^k (y^σ)²/x`. -/
theorem joint_phase_error {y : ℕ} (hk : 1 ≤ k) {σ T : ℝ}
    (hy : Real.exp 2 ≤ (y : ℝ)) (hylog : 2 ≤ Real.log y)
    (hσ : 1920 * (k : ℝ) ≤ σ)
    (hσA : 40 * Real.log ((4 : ℝ) ^ k * Real.exp (16 * k)) + 4 ≤ σ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ k < p ∧ p ≤ y)
    (hQ : 0 < Q) (hQcop : ∀ p ∈ P, Nat.Coprime Q p) (hx : 0 < x) (hT : 1 ≤ T)
    (F : JointState k P Q → ℂ) (hF : ∀ t, ‖F t‖ ≤ 1) :
    ‖(∑ t : JointState k P Q, (empLaw P Q x t : ℂ) * F t)
        - ∑ t : JointState k P Q, (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * F t‖
      ≤ 2 * ((k : ℝ) * Real.exp 20 / T ^ (1 / (2 * Real.log y)))
        + 4 * Real.exp (-σ / 2)
        + 2 * (Q : ℝ) * (Nat.floor T : ℝ) ^ k * ((y : ℝ) ^ σ) ^ 2 / x := by
  sorry

end NormalNumbers.PrimeModel.JointLaw
