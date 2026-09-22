import NormalNumbers.PrimeModelRadicalGraded
import NormalNumbers.PrimeModelRadicalStateGraded

/-!
# The graded retained-box tail: one Markov range per shift

Leaf **G2** of the graded-state regrade (`PENDING_WORK.md`, 2026-09-22 route correction).

`RadicalState.radical_box_tailG_exp20` bounds the model mass outside the per-shift retained box
by `∑_j e^{20} / T_j^{1/(2 log y_j)}`, but its Markov moment at shift `j` runs over the **whole**
prime family, so the exponent it can honestly claim is `1/(2 log Y)` with `Y` the top of the
range.  Along the multicutoff schedule (`log T_j ≍ 2^{-j/2} log N`, `log Y ≍ a log N`) that makes
each term tend to `e^{20}` as `j` grows and the sum diverge like `J e^{20}` — the second wall of
the route correction.

In the graded model a prime is never assigned to a shift it does not reach, so the shift-`j`
moment automatically restricts to `livePrimes dp j = {i : j < d_i}`, all of whose primes are
`≤ y_j`.  The exponent is then the sharp `1/(2 log y_j)` and the sum converges (Astra (8.4)).
This file carries that through `radical_site_momentG` to the box tail:

* `radical_site_momentG_le_exp`, `radical_radSize_momentG_le_exp` — the moment in `exp` form,
  with the budget taken over the live primes only;
* `radical_shift_markovG` — Markov at a fixed shift for the graded law;
* `radical_box_tailGG` — the union bound over shifts (`sum_compl_retainedBoxG_le` is already
  generic in the summand, so it is reused verbatim);
* `radical_box_tailGG_exp20` — the budget discharged by `radical_moment_budget` applied to the
  subtype of live primes, giving `∑_j e^{20} / T_j^{1/(2 log y_j)}` with **no hypothesis that the
  whole family lies below a single `Y`** — only that site `j`'s own primes lie below `y_j`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.Radical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The primes that site `j` actually sees: those whose class count exceeds `j`. -/
def livePrimes (dp : ι → ℕ) (j : Fin k) : Finset ι :=
  Finset.univ.filter (fun i => (j : ℕ) < dp i)

@[simp] lemma mem_livePrimes {dp : ι → ℕ} {j : Fin k} {i : ι} :
    i ∈ livePrimes dp j ↔ (j : ℕ) < dp i := by simp [livePrimes]

/-- **G2a.**  The graded single-site moment in exponential form: the budget is collected only
over the primes the site sees. -/
theorem radical_site_momentG_le_exp (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (q : ι → ℝ)
    (j₀ : Fin k) (t : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (ht : ∀ i, 1 ≤ t i) :
    ∑ s : ι → Option (Fin k),
        weightG k dp q s * ∏ i, (if s i = some j₀ then t i else 1)
      ≤ Real.exp (∑ i ∈ livePrimes dp j₀, q i * (t i - 1)) := by
  classical
  rw [radical_site_momentG k dp hd q j₀ t, Real.exp_sum, livePrimes, Finset.prod_filter]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · by_cases hlive : (j₀ : ℕ) < dp i
    · rw [if_pos hlive]
      have : 0 ≤ q i * (t i - 1) := mul_nonneg (hq i) (sub_nonneg.mpr (ht i))
      linarith
    · rw [if_neg hlive]; norm_num
  · by_cases hlive : (j₀ : ℕ) < dp i
    · rw [if_pos hlive, if_pos hlive, add_comm]
      exact Real.add_one_le_exp _
    · rw [if_neg hlive, if_neg hlive]

/-- **G2b.**  The `α`-moment of the radical size at shift `j` for the graded law, with the
budget over the live primes. -/
theorem radical_radSize_momentG_le_exp {p dp : ι → ℕ} {α A : ℝ} {j : Fin k}
    (hd : ∀ i, dp i ≤ k) (hp : ∀ i, 1 ≤ p i) (hα : 0 ≤ α)
    (hA : ∑ i ∈ livePrimes dp j, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) ≤ A) :
    ∑ s : ι → Option (Fin k), weightG k dp (primeRecip p) s * (radSize p j s) ^ α
      ≤ Real.exp A := by
  classical
  have h1 : ∀ i, (1 : ℝ) ≤ (p i : ℝ) ^ α := by
    intro i
    refine Real.one_le_rpow ?_ hα
    exact_mod_cast hp i
  have hmom := radical_site_momentG_le_exp k dp hd (primeRecip p) j (fun i => (p i : ℝ) ^ α)
    (primeRecip_nonneg p) h1
  have hsum : ∑ i ∈ livePrimes dp j, primeRecip p i * ((p i : ℝ) ^ α - 1)
      = ∑ i ∈ livePrimes dp j, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [primeRecip, div_eq_inv_mul]
  rw [hsum] at hmom
  refine le_trans ?_ (hmom.trans (Real.exp_le_exp.mpr hA))
  refine le_of_eq (Finset.sum_congr rfl fun s _ => ?_)
  rw [radSize_rpow]

open scoped Classical in
/-- **G2c.**  Markov's inequality at a fixed shift for the graded law. -/
theorem radical_shift_markovG {p dp : ι → ℕ} {T α A : ℝ} {j : Fin k}
    (hd : ∀ i, dp i ≤ k) (hkp : ∀ i, k ≤ p i) (hp : ∀ i, 1 ≤ p i)
    (hT : 0 < T) (hα : 0 < α)
    (hA : ∑ i ∈ livePrimes dp j, (((p i : ℝ) ^ α - 1) / (p i : ℝ)) ≤ A) :
    ∑ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T),
        weightG k dp (primeRecip p) s ≤ Real.exp A / T ^ α := by
  classical
  have hTa : (0 : ℝ) < T ^ α := Real.rpow_pos_of_pos hT α
  have hppos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hp i)
  have hdple : ∀ i, dp i ≤ p i := fun i => le_trans (hd i) (hkp i)
  have hw : ∀ s : ι → Option (Fin k), 0 ≤ weightG k dp (primeRecip p) s :=
    fun s => weightG_nonneg_prime hppos hdple s
  have hstep : ∀ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T),
      weightG k dp (primeRecip p) s
        ≤ (weightG k dp (primeRecip p) s * (radSize p j s) ^ α) / T ^ α := by
    intro s hs
    have hgt : T < radSize p j s := lt_of_not_ge (Finset.mem_filter.mp hs).2
    have hpow : T ^ α ≤ (radSize p j s) ^ α := le_of_lt (Real.rpow_lt_rpow hT.le hgt hα)
    rw [le_div_iff₀ hTa]
    exact mul_le_mul_of_nonneg_left hpow (hw s)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_div]
  have hle : ∑ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T),
      weightG k dp (primeRecip p) s * (radSize p j s) ^ α ≤ Real.exp A := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => mul_nonneg (hw s) (Real.rpow_nonneg (radSize_nonneg p j s) α))) ?_
    exact radical_radSize_momentG_le_exp hd hp hα.le hA
  gcongr

end NormalNumbers.PrimeModel.Radical

namespace NormalNumbers.PrimeModel.RadicalState

open NormalNumbers.PrimeModel.Radical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

open scoped Classical in
/-- **G2d, the graded box tail.**  One Markov exponent and one budget per shift, with the budget
taken over the primes that shift sees. -/
theorem radical_box_tailGG (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p dp : ι → ℕ} {T α A : Fin k → ℝ}
    (hd : ∀ i, dp i ≤ k) (hkp : ∀ i, k ≤ p i) (hp : ∀ i, 1 ≤ p i)
    (hT : ∀ j, 1 ≤ T j) (hα : ∀ j, 0 < α j)
    (hA : ∀ j, ∑ i ∈ livePrimes dp j, (((p i : ℝ) ^ (α j) - 1) / (p i : ℝ)) ≤ A j) :
    ∑ s ∈ (retainedBoxG k p T)ᶜ, weightG k dp (primeRecip p) s
      ≤ ∑ j : Fin k, Real.exp (A j) / (T j) ^ (α j) := by
  classical
  have hppos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hp i)
  have hdple : ∀ i, dp i ≤ p i := fun i => le_trans (hd i) (hkp i)
  refine (sum_compl_retainedBoxG_le (p := p) (T := T) _
    (fun s => weightG_nonneg_prime hppos hdple s)).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  exact radical_shift_markovG hd hkp hp (lt_of_lt_of_le zero_lt_one (hT j)) (hα j) (hA j)

open scoped Classical in
/-- **G2, the graded box tail with the budget discharged.**  At shift `j` the Markov exponent is
`1/(2 log y_j)` and the budget is `radical_moment_budget` applied to the subtype of primes that
site `j` sees — so the hypothesis needed is only `p i ≤ y_j` for the *live* primes of site `j`,
not for the whole family.  This is the per-shift Markov range of Fable §2 / Astra (8.4). -/
theorem radical_box_tailGG_exp20 (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p dp : ι → ℕ} {T y : Fin k → ℝ}
    (hd : ∀ i, dp i ≤ k) (hinj : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hkp : ∀ i, k ≤ p i) (hy0 : ∀ j, 0 < y j) (hy : ∀ j, 2 ≤ Real.log (y j))
    (hle : ∀ j : Fin k, ∀ i, (j : ℕ) < dp i → (p i : ℝ) ≤ y j) (hT : ∀ j, 1 ≤ T j) :
    ∑ s ∈ (retainedBoxG k p T)ᶜ, weightG k dp (primeRecip p) s
      ≤ ∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log (y j))) := by
  classical
  refine radical_box_tailGG k hd hkp (fun i => (hprime i).one_lt.le.trans' (by norm_num)) hT
    (fun j => by have := hy j; positivity) (fun j => ?_)
  -- the budget over the live primes of site `j`, via the subtype of live primes
  have hbudget := radical_moment_budget (ι := {i : ι // (j : ℕ) < dp i})
    (p := fun i => p (i : ι))
    (fun a b hab => Subtype.ext (hinj hab)) (fun i => hprime (i : ι))
    (hy0 j) (hy j) (fun i => hle j (i : ι) i.2)
  have hsubtype : ∑ i ∈ livePrimes dp j,
      (((p i : ℝ) ^ (1 / (2 * Real.log (y j))) - 1) / (p i : ℝ))
      = ∑ i : {i : ι // (j : ℕ) < dp i},
          (((p (i : ι) : ℝ) ^ (1 / (2 * Real.log (y j))) - 1) / (p (i : ι) : ℝ)) :=
    Finset.sum_subtype (livePrimes dp j) (fun _ => mem_livePrimes) _
  rw [hsubtype]
  exact hbudget

end NormalNumbers.PrimeModel.RadicalState
