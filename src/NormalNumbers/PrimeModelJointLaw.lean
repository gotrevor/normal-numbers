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
  unfold empLaw
  positivity

/-- The fibre of the joint map over `t` is exactly the filter defining `empLaw`. -/
private lemma fibre_eq (hQ : 0 < Q) (t : JointState k P Q) :
    ((range x).filter
        (fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualState k P n) = t))
      = ((range x).filter (fun n => n % Q = t.1.val ∧ actualState k P n = t.2)) := by
  refine Finset.filter_congr fun n _ => ?_
  simp [Prod.ext_iff, Fin.ext_iff]

/-- The fibres partition `range x`. -/
theorem empLaw_mass_one (hQ : 0 < Q) (hx : 0 < x) :
    ∑ t : JointState k P Q, empLaw P Q x t = 1 := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualState k P n))
    (s := range x) (t := (Finset.univ : Finset (JointState k P Q)))
    (fun n _ => Finset.mem_univ _)
  have hsum : ∑ t : JointState k P Q,
      ((range x).filter (fun n => n % Q = t.1.val ∧ actualState k P n = t.2)).card = x := by
    rw [← Finset.sum_congr rfl (fun t _ => congrArg Finset.card (fibre_eq P Q x hQ t)),
      ← hfib, Finset.card_range]
  have hx0 : (x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  unfold empLaw
  rw [← Finset.sum_div, ← Nat.cast_sum, hsum]
  exact div_self hx0

/-- **Fibre-sum identity.**  The prefix mean of `F(n mod Q, state n)` is `∑_t empLaw t · F t`. -/
theorem prefixMean_eq_sum_empLaw (hQ : 0 < Q) (hx : 0 < x) (F : JointState k P Q → ℂ) :
    (∑ n ∈ range x, F (⟨n % Q, Nat.mod_lt n hQ⟩, actualState k P n)) / (x : ℂ)
      = ∑ t : JointState k P Q, (empLaw P Q x t : ℂ) * F t := by
  classical
  have key := Finset.sum_fiberwise_of_maps_to
    (g := fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualState k P n))
    (s := range x) (t := (Finset.univ : Finset (JointState k P Q)))
    (fun n _ => Finset.mem_univ _)
    (fun n => F ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualState k P n))
  have hinner : ∀ t : JointState k P Q,
      (∑ n ∈ (range x).filter
          (fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualState k P n) = t),
          F ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualState k P n))
        = (((range x).filter
            (fun n => n % Q = t.1.val ∧ actualState k P n = t.2)).card : ℂ) * F t := by
    intro t
    rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
      Finset.sum_const, nsmul_eq_mul, fibre_eq P Q x hQ t]
  rw [← key, Finset.sum_congr rfl (fun t _ => hinner t), Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold empLaw
  push_cast
  ring

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
  classical
  obtain ⟨r, s⟩ := t
  have hk' : 0 < k := hk
  have hPk : ∀ q ∈ P, k < q := fun q hq => (hP q hq).2.1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  -- the arithmetic filter is the sifted filter
  have hfilter : (range x).filter (fun n => n % Q = r.val ∧ actualState k P n = s)
      = (range x).filter (SiftedCond k (stateA P s) (stateU P s) Q r.val
          (stateShift P s hk')) := by
    refine Finset.filter_congr fun n _ => ?_
    exact actual_state_sifted_iff hk' hPk Q r.val n
  have hA : ∀ p ∈ stateA P s, Nat.Prime p ∧ k < p := by
    intro p hp
    exact ⟨(hP p (stateA_subset hp)).1, (hP p (stateA_subset hp)).2.1⟩
  have hU : ∀ p ∈ stateU P s, Nat.Prime p ∧ k < p ∧ p ≤ y := by
    intro p hp; exact hP p (stateU_subset hp)
  have hQcop' : ∀ p ∈ stateA P s ∪ stateU P s, Nat.Coprime Q p := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hQcop p (stateA_subset h)
    · exact hQcop p (stateU_subset h)
  have hbrun := BrunCount.brun_sifted_count_lower (h := k) (y := y) hk (s := σ) hy hσ hσA
      (stateA P s) (stateU P s) Q r.val (stateShift P s hk') x hA hU
      stateA_disjoint_stateU hQ r.isLt hQcop'
  -- the model atom
  have hprodA : ((∏ p ∈ stateA P s, p : ℕ) : ℝ) = ∏ q ∈ stateA P s, (q : ℝ) :=
    Nat.cast_prod _ _
  have hprodA0 : ((∏ p ∈ stateA P s, p : ℕ) : ℝ) ≠ 0 := by
    rw [hprodA]
    refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
    have := (hA q hq).1.pos
    positivity
  have hQ0 : ((Q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hmodel : jointModel (Fin Q) k (primeRecip (primeOf P)) (r, s)
      = ((1 / ((∏ p ∈ stateA P s, p : ℕ) : ℝ))
          * ∏ q ∈ stateU P s, (1 - (k : ℝ) / q)) / (Q : ℝ) := by
    unfold jointModel
    rw [Fintype.card_fin]
    congr 1
    rw [show (primeRecip (primeOf P)) = Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ)) from
      rfl, state_model_density, hprodA]
  have hgoal : (1 - 2 * Real.exp (-σ / 2)) * jointModel (Fin Q) k (primeRecip (primeOf P)) (r, s)
        - ((y : ℝ) ^ σ) ^ 2 / x
      = ((1 - 2 * Real.exp (-σ / 2))
            * ((x : ℝ) / ((Q : ℝ) * ((∏ p ∈ stateA P s, p : ℕ) : ℝ)))
            * (∏ p ∈ stateU P s, (1 - (k : ℝ) / (p : ℝ))) - ((y : ℝ) ^ σ) ^ 2) / x := by
    rw [hmodel]
    field_simp
  rw [hgoal]
  show _ ≤ ((range x).filter (fun n => n % Q = (⟨r, s⟩ : JointState k P Q).1.val
      ∧ actualState k P n = (⟨r, s⟩ : JointState k P Q).2)).card / (x : ℝ)
  rw [hfilter]
  gcongr

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
  classical
  have hQne : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hppos : ∀ i : {q // q ∈ P}, 0 < primeOf P i := fun i => (hP i.1 i.2).1.pos
  have hprime : ∀ i : {q // q ∈ P}, (primeOf P i).Prime := fun i => (hP i.1 i.2).1
  have hkp : ∀ i : {q // q ∈ P}, k ≤ primeOf P i := fun i => (hP i.1 i.2).2.1.le
  have hinj : Function.Injective (primeOf P) := Subtype.val_injective
  have hle : ∀ i : {q // q ∈ P}, ((primeOf P i : ℕ) : ℝ) ≤ (y : ℝ) := by
    intro i; exact_mod_cast (hP i.1 i.2).2.2
  have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le (Real.exp_pos 2) hy
  set B : Finset (JointState k P Q) := Finset.univ ×ˢ retainedBox k (primeOf P) T with hB
  have hmain := finite_phase_of_lower_atoms
    (jointModel (Fin Q) k (primeRecip (primeOf P))) (empLaw P Q x) B
    (2 * Real.exp (-σ / 2)) (fun _ => ((y : ℝ) ^ σ) ^ 2 / x)
    (fun i => jointModel_nonneg hppos hkp i) (fun i => empLaw_nonneg P Q x i)
    (jointModel_mass_one (Fin Q) k (primeOf P)) (empLaw_mass_one P Q x hQ hx)
    (by positivity) (fun i _ => by positivity)
    (fun i _ => empLaw_lower_atom P Q x hk hy hσ hσA hP hQ hQcop hx i)
    F hF
  have htail : ∑ i ∈ Bᶜ, jointModel (Fin Q) k (primeRecip (primeOf P)) i
      ≤ (k : ℝ) * Real.exp 20 / T ^ (1 / (2 * Real.log y)) := by
    have h1 := jointModel_tail (Fin Q) k (primeOf P) T
    have h2 := radical_box_tail_exp20 k hinj hprime hkp hy0 hylog hle hT
    rw [hB]
    convert h1.trans_le h2 using 2
    ext a
    simp
  have hcardB : (B.card : ℝ) ≤ (Q : ℝ) * (Nat.floor T : ℝ) ^ k := by
    rw [hB, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    exact mul_le_mul_of_nonneg_left (retainedBox_card_le hprime hinj k hT) (by positivity)
  have he0 : (0 : ℝ) ≤ ((y : ℝ) ^ σ) ^ 2 / x := by positivity
  have hsume : ∑ _i ∈ B, ((y : ℝ) ^ σ) ^ 2 / x
      = (B.card : ℝ) * (((y : ℝ) ^ σ) ^ 2 / x) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hterm : (B.card : ℝ) * (((y : ℝ) ^ σ) ^ 2 / x)
      ≤ (Q : ℝ) * (Nat.floor T : ℝ) ^ k * (((y : ℝ) ^ σ) ^ 2 / x) :=
    mul_le_mul_of_nonneg_right hcardB he0
  rw [hsume] at hmain
  have hshape : 2 * (Q : ℝ) * (Nat.floor T : ℝ) ^ k * ((y : ℝ) ^ σ) ^ 2 / x
      = 2 * ((Q : ℝ) * (Nat.floor T : ℝ) ^ k * (((y : ℝ) ^ σ) ^ 2 / x)) := by ring
  rw [hshape]
  linarith

end NormalNumbers.PrimeModel.JointLaw
