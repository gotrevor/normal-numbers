import NormalNumbers.PrimeModelRadical
import NormalNumbers.PrimeModelComplement

/-!
# The retained-box tail for the finite radical model

The radical model of `NormalNumbers.PrimeModelRadical` is a probability law on
the finite state space `ι → Option (Fin k)`.  For each shift `j` the *radical
size* of a state is the product of the primes assigned to that shift,

  `d_j(s) = ∏_i (if s i = some j then p i else 1)`,

and the **retained box** `B(T)` is the set of states with `d_j(s) ≤ T` for every
shift `j`.  This file proves

* `radical_box_tail` : the model mass outside `B(T)` is at most
  `k * exp A / T ^ α`, whenever `α > 0` and the moment budget
  `∑_i ((p i)^α - 1)/(p i) ≤ A` holds — a Markov bound on `d_j^α` per shift
  followed by a union bound over the `k` shifts; and

* `radical_box_phase_transfer` : composing the tail with
  `NormalNumbers.PrimeModel.probability_complement_phase`, any actual law `ν`
  on the same state space whose retained `L¹` discrepancy against the model is
  at most `δ` has expectations matching the model's to within
  `2 * k * exp A / T ^ α + 2 * δ` for every `f` of complex norm `≤ 1`.

The arithmetic estimate `A ≤ 20` (or `4√e`, via `p^α - 1 ≤ √e α log p` and
Mertens) is **not** proved here: `A` is a hypothesis throughout.  The retained
`L¹` discrepancy is likewise a hypothesis, not an axiom.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace NormalNumbers.PrimeModel.Radical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-! ## Radical size -/

/-- The radical size of a state at shift `j`: the product of the primes assigned
to that shift (a real number, the cast of the natural product). -/
def radSize (p : ι → ℕ) (j : Fin k) (s : ι → Option (Fin k)) : ℝ :=
  ∏ i, (if s i = some j then (p i : ℝ) else 1)

lemma radSize_nonneg (p : ι → ℕ) (j : Fin k) (s : ι → Option (Fin k)) :
    0 ≤ radSize p j s := by
  refine Finset.prod_nonneg fun i _ => ?_
  by_cases h : s i = some j <;> simp [h, Nat.cast_nonneg]

lemma one_le_radSize {p : ι → ℕ} (hp : ∀ i, 1 ≤ p i) (j : Fin k)
    (s : ι → Option (Fin k)) : 1 ≤ radSize p j s := by
  calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
    _ ≤ radSize p j s := by
        refine Finset.prod_le_prod (fun i _ => zero_le_one) (fun i _ => ?_)
        by_cases h : s i = some j
        · simp only [h, if_pos rfl]
          exact_mod_cast hp i
        · simp [h]

/-- **The real power of a product identity.**  Real `α`-powers distribute over the
radical size, turning `d_j(s)^α` back into the single-site multiplier shape
consumed by `radical_site_moment_le_exp`. -/
theorem radSize_rpow (p : ι → ℕ) (j : Fin k) (s : ι → Option (Fin k)) (α : ℝ) :
    (radSize p j s) ^ α = ∏ i, (if s i = some j then (p i : ℝ) ^ α else 1) := by
  rw [radSize, ← Real.finsetProd_rpow _ _ (fun i _ => ?_)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : s i = some j
    · simp [h]
    · simp [h, Real.one_rpow]
  · by_cases h : s i = some j <;> simp [h, Nat.cast_nonneg]

/-! ## The `d_j^α` moment bound -/

/-- The `α`-moment of the radical size at any fixed shift is at most `exp A`
under the moment budget `∑_i ((p i)^α - 1)/(p i) ≤ A`. -/
theorem radical_radSize_moment_le_exp {p : ι → ℕ} {α A : ℝ}
    (hp : ∀ i, 1 ≤ p i) (hα : 0 ≤ α)
    (hA : ∑ i, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) ≤ A) (j : Fin k) :
    ∑ s : ι → Option (Fin k), weight k (primeRecip p) s * (radSize p j s) ^ α
      ≤ Real.exp A := by
  have h1 : ∀ i, (1 : ℝ) ≤ (p i : ℝ) ^ α := by
    intro i
    refine Real.one_le_rpow ?_ hα
    exact_mod_cast hp i
  have hmom := radical_site_moment_le_exp k (primeRecip p) j (fun i => (p i : ℝ) ^ α)
    (primeRecip_nonneg p) h1
  have hsum : ∑ i, primeRecip p i * ((p i : ℝ) ^ α - 1)
      = ∑ i, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [primeRecip, div_eq_inv_mul]
  rw [hsum] at hmom
  refine le_trans ?_ (hmom.trans (Real.exp_le_exp.mpr hA))
  refine le_of_eq (Finset.sum_congr rfl fun s _ => ?_)
  rw [radSize_rpow]

/-! ## The retained box -/

open scoped Classical in
/-- The retained box: states whose radical size is at most `T` at *every* shift. -/
noncomputable def retainedBox (k : ℕ) (p : ι → ℕ) (T : ℝ) :
    Finset (ι → Option (Fin k)) :=
  Finset.univ.filter (fun s => ∀ j : Fin k, radSize p j s ≤ T)

open scoped Classical in
lemma mem_retainedBox {p : ι → ℕ} {T : ℝ} {s : ι → Option (Fin k)} :
    s ∈ retainedBox k p T ↔ ∀ j : Fin k, radSize p j s ≤ T := by
  simp [retainedBox]

/-! ## Markov at a fixed shift -/

open scoped Classical in
/-- Markov's inequality at a fixed shift: the model mass of states with
`d_j(s) > T` is at most `exp A / T ^ α`. -/
theorem radical_shift_markov {p : ι → ℕ} {T α A : ℝ}
    (hkp : ∀ i, k ≤ p i) (hp : ∀ i, 1 ≤ p i) (hT : 0 < T) (hα : 0 < α)
    (hA : ∑ i, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) ≤ A) (j : Fin k) :
    ∑ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T),
        weight k (primeRecip p) s ≤ Real.exp A / T ^ α := by
  have hTa : (0 : ℝ) < T ^ α := Real.rpow_pos_of_pos hT α
  have hppos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hp i)
  have hw : ∀ s : ι → Option (Fin k), 0 ≤ weight k (primeRecip p) s :=
    fun s => radical_weight_nonneg_prime hppos hkp s
  -- termwise: on the bad set, `1 ≤ d_j(s)^α / T^α`
  have hstep : ∀ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T),
      weight k (primeRecip p) s
        ≤ (weight k (primeRecip p) s * (radSize p j s) ^ α) / T ^ α := by
    intro s hs
    have hgt : T < radSize p j s := by
      have := (Finset.mem_filter.mp hs).2
      exact lt_of_not_ge this
    have hpow : T ^ α ≤ (radSize p j s) ^ α :=
      le_of_lt (Real.rpow_lt_rpow hT.le hgt hα)
    rw [le_div_iff₀ hTa]
    calc weight k (primeRecip p) s * T ^ α
        ≤ weight k (primeRecip p) s * (radSize p j s) ^ α :=
          mul_le_mul_of_nonneg_left hpow (hw s)
      _ = weight k (primeRecip p) s * (radSize p j s) ^ α := rfl
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_div]
  have hle : ∑ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T),
      weight k (primeRecip p) s * (radSize p j s) ^ α ≤ Real.exp A := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => mul_nonneg (hw s) (Real.rpow_nonneg (radSize_nonneg p j s) α))) ?_
    exact radical_radSize_moment_le_exp hp hα.le hA j
  gcongr

/-! ## The union bound over shifts, and the tail -/

open scoped Classical in
/-- A finite union bound: a nonnegative family summed over the complement of the
retained box is dominated by the sum over the `k` bad shift-sets. -/
theorem sum_compl_retainedBox_le {p : ι → ℕ} {T : ℝ} (g : (ι → Option (Fin k)) → ℝ)
    (hg : ∀ s, 0 ≤ g s) :
    ∑ s ∈ (retainedBox k p T)ᶜ, g s
      ≤ ∑ j : Fin k, ∑ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T), g s := by
  have hpt : ∀ s ∈ (retainedBox k p T)ᶜ,
      g s ≤ ∑ j : Fin k, (if ¬ radSize p j s ≤ T then g s else 0) := by
    intro s hs
    have hs' : ¬ ∀ j : Fin k, radSize p j s ≤ T := by
      simpa [mem_retainedBox] using Finset.mem_compl.mp hs
    obtain ⟨j₀, hj₀⟩ := not_forall.mp hs'
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun j => if ¬ radSize p j s ≤ T then g s else 0)
        (fun j _ => by by_cases h : ¬ radSize p j s ≤ T <;> simp [h, hg s])
        (Finset.mem_univ j₀))
    simp [hj₀]
  refine (Finset.sum_le_sum hpt).trans ?_
  have hext : ∑ s ∈ (retainedBox k p T)ᶜ,
      ∑ j : Fin k, (if ¬ radSize p j s ≤ T then g s else 0)
      ≤ ∑ s : ι → Option (Fin k),
          ∑ j : Fin k, (if ¬ radSize p j s ≤ T then g s else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => ?_)
    refine Finset.sum_nonneg fun j _ => ?_
    by_cases h : ¬ radSize p j s ≤ T <;> simp [h, hg s]
  refine hext.trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter]

open scoped Classical in
/-- **The retained-box tail.**  For `T ≥ 1`, `α > 0` and the moment budget
`∑_i ((p i)^α - 1)/(p i) ≤ A`, the model mass outside the retained box `B(T)` is
at most `k * exp A / T ^ α`.  (The arithmetic bound `A ≤ 20` is *not* proved
here; `A` is a hypothesis.) -/
theorem radical_box_tail (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ} {T α A : ℝ}
    (hkp : ∀ i, k ≤ p i) (hp : ∀ i, 1 ≤ p i) (hT : 1 ≤ T) (hα : 0 < α)
    (hA : ∑ i, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) ≤ A) :
    ∑ s ∈ (retainedBox k p T)ᶜ, weight k (primeRecip p) s
      ≤ (k : ℝ) * Real.exp A / T ^ α := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hppos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hp i)
  refine (sum_compl_retainedBox_le (p := p) (T := T) _
    (fun s => radical_weight_nonneg_prime hppos hkp s)).trans ?_
  refine (Finset.sum_le_sum (fun j _ =>
    radical_shift_markov hkp hp hT0 hα hA j)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_assoc]

/-! ## Phase transfer to the actual law -/

open scoped Classical in
/-- **Phase transfer.**  Let `ν` be any nonnegative normalized law on the same
finite state space whose retained `L¹` discrepancy against the radical model is
at most `δ`.  Then for every `f` with `‖f s‖ ≤ 1` the expectations differ by at
most `2 k exp A / T ^ α + 2 δ`.

This is `NormalNumbers.PrimeModel.probability_complement_phase` composed with
`radical_box_tail`; neither the tail nor the `L¹` discrepancy is assumed as an
axiom (`A` and `δ` are explicit hypotheses). -/
theorem radical_box_phase_transfer (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ} {T α A δ : ℝ}
    (hkp : ∀ i, k ≤ p i) (hp : ∀ i, 1 ≤ p i) (hT : 1 ≤ T) (hα : 0 < α)
    (hA : ∑ i, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) ≤ A)
    (ν : (ι → Option (Fin k)) → ℝ) (hν_nonneg : ∀ s, 0 ≤ ν s)
    (hν_one : ∑ s, ν s = 1)
    (hδ : ∑ s ∈ retainedBox k p T, |ν s - weight k (primeRecip p) s| ≤ δ)
    (f : (ι → Option (Fin k)) → ℂ) (hf : ∀ s, ‖f s‖ ≤ 1) :
    ‖(∑ s, (ν s : ℂ) * f s) - (∑ s, (weight k (primeRecip p) s : ℂ) * f s)‖
      ≤ 2 * ((k : ℝ) * Real.exp A / T ^ α) + 2 * δ := by
  have hppos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hp i)
  set μ : (ι → Option (Fin k)) → ℝ := weight k (primeRecip p) with hμdef
  have hμ : Summable μ := Summable.of_finite
  have hνs : Summable ν := Summable.of_finite
  have hμ_nonneg : ∀ s, 0 ≤ μ s := fun s => radical_weight_nonneg_prime hppos hkp s
  have hμ_one : ∑' s, μ s = 1 := by
    rw [tsum_fintype]; exact radical_mass_one_prime k p
  have hν_one' : ∑' s, ν s = 1 := by rw [tsum_fintype]; exact hν_one
  have hmain := probability_complement_phase μ ν (retainedBox k p T) hμ hνs
    hμ_nonneg hν_nonneg hμ_one hν_one' f hf
  -- rewrite the two tsums as finite sums
  have hsub : (∑' s : {s // s ∉ retainedBox k p T}, μ s)
      = ∑ s ∈ (retainedBox k p T)ᶜ, μ s := by
    rw [tsum_fintype]
    exact (Finset.sum_subtype _ (fun x => by simp) μ).symm
  rw [hsub] at hmain
  rw [tsum_fintype, tsum_fintype] at hmain
  refine hmain.trans ?_
  have htail := radical_box_tail k hkp hp hT hα hA
  have : ∑ s ∈ (retainedBox k p T)ᶜ, μ s ≤ (k : ℝ) * Real.exp A / T ^ α := htail
  linarith

/-! ## Numeric anchors

`k = 2`, two sites carrying the primes `3, 5` (the `k = 2` instrument).  The nine
states and their masses are

  `(none,none) 1/5`, `(s j,none) 1/5` each, and the six states with both sites
  assigned or the first site free carrying mass `1/15` each,

so `d_j` takes the values `1, 3, 5, 15`.  The tail masses below are computed by
**expanding the state space by hand** (through `Fin.consEquiv`), independently of
`radical_box_tail`: `T = 1, 2 ↦ 4/5`; `T = 3 ↦ 2/5`; `T = 5 ↦ 2/15` (only the two
states assigning *both* primes to the *same* shift exceed `5`, each of mass
`1/15`); `T = 15 ↦ 0`. -/

section Anchors

open scoped Classical

/-- The two-site instrument: primes `3` and `5`. -/
private def pA : Fin 2 → ℕ := ![3, 5]

private lemma optCases (z : Option (Fin 2)) : z = none ∨ z = some 0 ∨ z = some 1 := by
  rcases z with _ | z
  · exact Or.inl rfl
  · fin_cases z
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private lemma sum_funUnique' (f : (Fin 1 → Option (Fin 2)) → ℝ) :
    ∑ y, f y = ∑ b : Option (Fin 2), f (fun _ => b) :=
  (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Option (Fin 2))).symm f).symm

private lemma tail_eq_filter (T : ℝ) :
    ∑ s ∈ (retainedBox 2 pA T)ᶜ, weight 2 (primeRecip pA) s
      = ∑ s : Fin 2 → Option (Fin 2),
          (if ∀ j : Fin 2, radSize pA j s ≤ T then 0
            else weight 2 (primeRecip pA) s) := by
  have hc : (retainedBox 2 pA T)ᶜ
      = Finset.univ.filter (fun s => ¬ ∀ j : Fin 2, radSize pA j s ≤ T) := by
    ext s; simp [mem_retainedBox]
  rw [hc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : ∀ j : Fin 2, radSize pA j s ≤ T <;> simp [h]

/-- Hand expansion of the nine states, for any threshold. -/
private lemma tail_expand (T : ℝ) :
    ∑ s ∈ (retainedBox 2 pA T)ᶜ, weight 2 (primeRecip pA) s
      = ∑ a : Option (Fin 2), ∑ b : Option (Fin 2),
          (if ∀ j : Fin 2, radSize pA j ![a, b] ≤ T then 0
            else weight 2 (primeRecip pA) ![a, b]) := by
  rw [tail_eq_filter]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2 => Option (Fin 2))),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_funUnique' ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rfl

private lemma anchor_simp (T : ℝ) :
    ∑ s ∈ (retainedBox 2 pA T)ᶜ, weight 2 (primeRecip pA) s
      = ∑ a : Option (Fin 2), ∑ b : Option (Fin 2),
          (if ((if a = some 0 then (3:ℝ) else 1) * (if b = some 0 then (5:ℝ) else 1) ≤ T
              ∧ (if a = some 1 then (3:ℝ) else 1) * (if b = some 1 then (5:ℝ) else 1) ≤ T)
            then 0
            else (if a = none then (1:ℝ)/3 else 1/3) * (if b = none then (3:ℝ)/5 else 1/5)) := by
  rw [tail_expand]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  · simp only [Fin.forall_fin_two, radSize, Fin.prod_univ_two, pA,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    rcases optCases a with ha | ha | ha <;> rcases optCases b with hb | hb | hb <;>
      subst ha <;> subst hb <;>
      simp only [reduceCtorEq, Option.some.injEq, Fin.reduceEq, if_false, if_true] <;>
      norm_num
  · cases a <;> cases b <;>
      simp [weight, Fin.prod_univ_two, primeRecip, pA, localWeight] <;> norm_num

example : ∑ s ∈ (retainedBox 2 pA 1)ᶜ, weight 2 (primeRecip pA) s = 4/5 := by
  rw [anchor_simp]; simp only [Fintype.sum_option, Fin.sum_univ_two, reduceCtorEq,
    Option.some.injEq, Fin.reduceEq, if_false, if_true]
  norm_num

example : ∑ s ∈ (retainedBox 2 pA 2)ᶜ, weight 2 (primeRecip pA) s = 4/5 := by
  rw [anchor_simp]; simp only [Fintype.sum_option, Fin.sum_univ_two, reduceCtorEq,
    Option.some.injEq, Fin.reduceEq, if_false, if_true]
  norm_num

example : ∑ s ∈ (retainedBox 2 pA 3)ᶜ, weight 2 (primeRecip pA) s = 2/5 := by
  rw [anchor_simp]; simp only [Fintype.sum_option, Fin.sum_univ_two, reduceCtorEq,
    Option.some.injEq, Fin.reduceEq, if_false, if_true]
  norm_num

example : ∑ s ∈ (retainedBox 2 pA 5)ᶜ, weight 2 (primeRecip pA) s = 2/15 := by
  rw [anchor_simp]; simp only [Fintype.sum_option, Fin.sum_univ_two, reduceCtorEq,
    Option.some.injEq, Fin.reduceEq, if_false, if_true]
  norm_num

example : ∑ s ∈ (retainedBox 2 pA 15)ᶜ, weight 2 (primeRecip pA) s = 0 := by
  rw [anchor_simp]; simp only [Fintype.sum_option, Fin.sum_univ_two, reduceCtorEq,
    Option.some.injEq, Fin.reduceEq, if_false, if_true]
  norm_num

end Anchors

end NormalNumbers.PrimeModel.Radical
