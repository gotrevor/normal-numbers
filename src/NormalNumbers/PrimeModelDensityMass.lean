import NormalNumbers.PrimeModelParameters

/-!
# Prime model, Part II-a: from a prime-density bound to reciprocal-mass bounds

`papers/prime-model-assembly-2026-09-22.md`, Part II, "(M1)" and "(M2)".

Write `π_P(t) = #{p < t : p prime, p ∈ P}` (`(t.primesBelow.filter P).card`).

* **(M1)** dominated Abel summation: if `π_P(t) ≤ δ π(t)` for `y < t ≤ N+1` then
  `recipSumIoc P y N ≤ δ (∑_{y<p≤N} 1/p + 1)`.
* **(M1')** with the interval Mertens bound `primeRecipSum_le`:
  `recipSumIoc P y N ≤ δ (9 + 12 log(log N / log y))` for `2 ≤ y ≤ N`.
* **(M2)** under `Sparse P` (`π_P(x) log log x ≤ π(x)` eventually), the accumulated mass is
  `recipSumLe P N ≤ C_P + 100 log log log N` for all large `N`: cut `(a_i, a_{i+1}]` at
  `a_i = ⌊exp exp 2^i⌋₊`, where the density is `≤ 1/(2^i − 1)` and the Mertens ratio is
  `log a_{i+1}/log a_i ≤ 2 exp 2^i`, so each range carries mass `≤ 42`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.DensityMass

open NormalNumbers.G4Sparse

variable (P : ℕ → Prop) [DecidablePred P]

/-- `π_P(t) = #{p < t : p prime, p ∈ P}`. -/
def piP (t : ℕ) : ℕ := (t.primesBelow.filter P).card

/-- **The density hypothesis of the family theorem**: `π_P(x) · log log x ≤ π(x)` eventually. -/
def Sparse : Prop :=
  ∀ᶠ x : ℕ in atTop, (piP P x : ℝ) * Real.log (Real.log x) ≤ (x.primesBelow.card : ℝ)

/-- `recipSumLe` splits at any intermediate point. -/
theorem recipSumLe_add_recipSumIoc {a b : ℕ} (hab : a ≤ b) :
    recipSumLe P b = recipSumLe P a + recipSumIoc P a b := by
  have hsplit : Finset.Iic b = Finset.Iic a ∪ Finset.Ioc a b := by
    ext n; simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Iic a) (Finset.Ioc a b) :=
    Finset.disjoint_left.mpr (by
      intro n hn hn'
      simp only [Finset.mem_Iic] at hn
      simp only [Finset.mem_Ioc] at hn'
      omega)
  unfold recipSumLe recipSumIoc
  rw [hsplit, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]

/-- `recipSumIoc ≥ 0`. -/
theorem recipSumIoc_nonneg (y N : ℕ) : 0 ≤ recipSumIoc P y N := by
  unfold recipSumIoc
  exact Finset.sum_nonneg fun i _ => by positivity

/-- `recipSumLe P` is monotone. -/
theorem recipSumLe_mono {a b : ℕ} (hab : a ≤ b) : recipSumLe P a ≤ recipSumLe P b := by
  rw [recipSumLe_add_recipSumIoc P hab]
  linarith [recipSumIoc_nonneg P a b]

private theorem range_succ_eq_Iic (n : ℕ) : Finset.range (n + 1) = Finset.Iic n := by
  ext m; simp only [Finset.mem_range, Finset.mem_Iic]; omega

/-- Divergent reciprocal sum ⇒ the partial sums tend to infinity. -/
theorem recipSumLe_tendsto_atTop (hP : DivergentRecip P) :
    Tendsto (recipSumLe P) atTop atTop := by
  have hnn : ∀ n : ℕ, 0 ≤ (if n.Prime ∧ P n then (1 : ℝ) / n else 0) := by
    intro n; split_ifs with h
    · positivity
    · exact le_refl 0
  have hdiv : ¬ Summable (fun p : ℕ => if p.Prime ∧ P p then (1 : ℝ) / p else 0) := hP
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hdiv
  have heq : ∀ n : ℕ, recipSumLe P n
      = ∑ i ∈ Finset.range (n + 1), (if i.Prime ∧ P i then (1 : ℝ) / i else 0) := by
    intro n
    rw [range_succ_eq_Iic]
    unfold recipSumLe
    rw [Finset.sum_filter]
  have := h.comp (Filter.tendsto_add_atTop_nat 1)
  refine this.congr ?_
  intro n
  exact (heq n).symm

/-- Abel summation over `Ioc y N` with weights `c`. -/
private theorem abel_Ioc (f c : ℕ → ℝ) (y : ℕ) : ∀ N : ℕ,
    ∑ n ∈ Finset.Ioc y N, f n * c n
      = c N * (∑ n ∈ Finset.Ioc y N, f n)
        + ∑ m ∈ Finset.Ico (y + 1) N, (c m - c (m + 1)) * (∑ n ∈ Finset.Ioc y m, f n) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rcases lt_or_ge N y with h | h
    · have h1 : Finset.Ioc y (N + 1) = (∅ : Finset ℕ) := by
        rw [Finset.Ioc_eq_empty]; omega
      have h2 : Finset.Ico (y + 1) (N + 1) = (∅ : Finset ℕ) := by
        rw [Finset.Ico_eq_empty]; omega
      simp [h1, h2]
    · rcases eq_or_lt_of_le h with heq | hlt
      · -- y = N
        have h1 : Finset.Ioc y (N + 1) = {N + 1} := by
          ext n; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
        have h2 : Finset.Ico (y + 1) (N + 1) = (∅ : Finset ℕ) := by
          rw [Finset.Ico_eq_empty]; omega
        have h3 : Finset.Ioc y N = (∅ : Finset ℕ) := by
          rw [Finset.Ioc_eq_empty]; omega
        simp [h1, h2, mul_comm]
      · have hIoc : Finset.Ioc y (N + 1) = insert (N + 1) (Finset.Ioc y N) := by
          ext n; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
        have hIco : Finset.Ico (y + 1) (N + 1) = insert N (Finset.Ico (y + 1) N) := by
          ext m; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        have hn1 : (N + 1) ∉ Finset.Ioc y N := by simp
        have hn2 : N ∉ Finset.Ico (y + 1) N := by simp
        rw [hIoc, hIco, Finset.sum_insert hn1, Finset.sum_insert hn1, Finset.sum_insert hn2, ih]
        ring

private theorem telescope (c : ℕ → ℝ) {a N : ℕ} (h : a ≤ N) :
    ∑ m ∈ Finset.Ico a N, (c m - c (m + 1)) = c a - c N := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [Finset.sum_Ico_succ_top hN, ih]; ring


private theorem piP_eq_sum (t : ℕ) :
    (piP P t : ℝ) = ∑ n ∈ Finset.range t, (if n.Prime ∧ P n then (1:ℝ) else 0) := by
  unfold piP
  rw [Nat.primesBelow_eq_filter_range, Finset.filter_filter, Finset.card_filter]
  push_cast; rfl

private theorem pi_eq_sum (t : ℕ) :
    (t.primesBelow.card : ℝ) = ∑ n ∈ Finset.range t, (if n.Prime then (1:ℝ) else 0) := by
  rw [Nat.primesBelow_eq_filter_range, Finset.card_filter]
  push_cast; rfl

private theorem range_split (f : ℕ → ℝ) {y t : ℕ} (h : y ≤ t) :
    ∑ n ∈ Finset.range (t+1), f n
      = ∑ n ∈ Finset.range (y+1), f n + ∑ n ∈ Finset.Ioc y t, f n := by
  have h1 : Finset.Ioc y t = Finset.Ico (y+1) (t+1) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [h1, Finset.range_eq_Ico, Finset.range_eq_Ico,
    Finset.sum_Ico_consecutive f (Nat.zero_le _) (by omega)]

theorem recipSumIoc_le_of_dominated {δ : ℝ} (hδ : 0 ≤ δ) (y N : ℕ)
    (hdom : ∀ t, y < t → t ≤ N + 1 → (piP P t : ℝ) ≤ δ * (t.primesBelow.card : ℝ)) :
    recipSumIoc P y N ≤ δ * ((∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (1 : ℝ) / p) + 1) := by
  set fa : ℕ → ℝ := fun n => if n.Prime ∧ P n then (1:ℝ) else 0 with hfa
  set fb : ℕ → ℝ := fun n => if n.Prime then (1:ℝ) else 0 with hfb
  set c : ℕ → ℝ := fun n => 1 / (n:ℝ) with hc
  have hfa0 : ∀ n, 0 ≤ fa n := by intro n; simp only [hfa]; split_ifs <;> norm_num
  have hfb1 : ∀ n, fb n ≤ 1 := by intro n; simp only [hfb]; split_ifs <;> norm_num
  have hpiPs : ∀ t : ℕ, (piP P t : ℝ) = ∑ n ∈ Finset.range t, fa n := by
    intro t; simp only [hfa]; exact piP_eq_sum P t
  have hpis : ∀ t : ℕ, (t.primesBelow.card : ℝ) = ∑ n ∈ Finset.range t, fb n := by
    intro t; simp only [hfb]; exact pi_eq_sum t
  have hLHS : recipSumIoc P y N = ∑ n ∈ Finset.Ioc y N, fa n * c n := by
    unfold recipSumIoc
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hfa, hc]; split_ifs <;> ring
  have hRHS : (∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (1 : ℝ) / p)
      = ∑ n ∈ Finset.Ioc y N, fb n * c n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hfb, hc]; split_ifs <;> ring
  rcases le_or_gt N y with hNy | hNy
  · have he : Finset.Ioc y N = (∅ : Finset ℕ) := by rw [Finset.Ioc_eq_empty]; omega
    unfold recipSumIoc
    rw [he]
    simp only [Finset.filter_empty, Finset.sum_empty]
    linarith
  -- main case  y < N
  have hyN1 : y + 1 ≤ N := hNy
  have hc0 : ∀ n : ℕ, 0 ≤ c n := by intro n; simp only [hc]; positivity
  have hd0 : ∀ m ∈ Finset.Ico (y+1) N, 0 ≤ c m - c (m+1) := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    simp only [hc, sub_nonneg]
    have h1 : (0:ℝ) < (m:ℝ) := by
      have : 1 ≤ m := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    apply one_div_le_one_div_of_le h1
    push_cast; linarith
  have hAle : ∀ t, y ≤ t → t ≤ N →
      (∑ n ∈ Finset.Ioc y t, fa n) ≤ δ * (((t+1).primesBelow.card : ℝ)) := by
    intro t hyt htN
    have h1 : (∑ n ∈ Finset.Ioc y t, fa n) ≤ (piP P (t+1) : ℝ) := by
      rw [hpiPs]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hfa0 i)
      intro n hn
      simp only [Finset.mem_Ioc] at hn
      simp only [Finset.mem_range]; omega
    exact h1.trans (hdom (t+1) (by omega) (by omega))
  have hBge : ∀ t, y ≤ t →
      (((t+1).primesBelow.card : ℝ)) - ((y:ℝ)+1) ≤ ∑ n ∈ Finset.Ioc y t, fb n := by
    intro t hyt
    have hsp := range_split fb hyt
    rw [← hpis] at hsp
    have hsmall : ∑ n ∈ Finset.range (y+1), fb n ≤ ((y:ℝ)+1) := by
      calc ∑ n ∈ Finset.range (y+1), fb n ≤ ∑ _n ∈ Finset.range (y+1), (1:ℝ) :=
            Finset.sum_le_sum (fun i _ => hfb1 i)
        _ = ((y:ℝ)+1) := by simp
    linarith
  set X : ℝ := c N * (((N+1).primesBelow.card : ℝ))
      + ∑ m ∈ Finset.Ico (y+1) N, (c m - c (m+1)) * (((m+1).primesBelow.card : ℝ)) with hX
  have step1 : (∑ n ∈ Finset.Ioc y N, fa n * c n) ≤ δ * X := by
    have e1 : δ * X = δ * (c N * (((N+1).primesBelow.card : ℝ)))
        + ∑ m ∈ Finset.Ico (y+1) N,
            δ * ((c m - c (m+1)) * (((m+1).primesBelow.card : ℝ))) := by
      rw [hX, mul_add, Finset.mul_sum]
    rw [abel_Ioc fa c y N, e1]
    have t1 : c N * (∑ n ∈ Finset.Ioc y N, fa n) ≤ δ * (c N * (((N+1).primesBelow.card : ℝ))) :=
      le_of_le_of_eq (mul_le_mul_of_nonneg_left (hAle N (le_of_lt hNy) le_rfl) (hc0 N)) (by ring)
    have t2 : ∑ m ∈ Finset.Ico (y+1) N, (c m - c (m+1)) * (∑ n ∈ Finset.Ioc y m, fa n)
        ≤ ∑ m ∈ Finset.Ico (y+1) N,
            δ * ((c m - c (m+1)) * (((m+1).primesBelow.card : ℝ))) := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hdm := hd0 m hm
      simp only [Finset.mem_Ico] at hm
      exact le_of_le_of_eq (mul_le_mul_of_nonneg_left (hAle m (by omega) (by omega)) hdm) (by ring)
    linarith
  have hy1c : ((y:ℝ)+1) * c (y+1) = 1 := by
    simp only [hc]
    push_cast
    field_simp
  have step2 : X ≤ (∑ n ∈ Finset.Ioc y N, fb n * c n) + 1 := by
    rw [abel_Ioc fb c y N, hX]
    have hBN : c N * ((((N+1).primesBelow.card : ℝ)) - ((y:ℝ)+1)) ≤ c N * (∑ n ∈ Finset.Ioc y N, fb n) :=
      mul_le_mul_of_nonneg_left (hBge N (le_of_lt hNy)) (hc0 N)
    have hBN' : c N * ((((N+1).primesBelow.card : ℝ)) - ((y:ℝ)+1))
        = c N * (((N+1).primesBelow.card : ℝ)) - ((y:ℝ)+1) * c N := by ring
    have hBsum : ∑ m ∈ Finset.Ico (y+1) N,
          (c m - c (m+1)) * ((((m+1).primesBelow.card : ℝ)) - ((y:ℝ)+1))
        ≤ ∑ m ∈ Finset.Ico (y+1) N, (c m - c (m+1)) * (∑ n ∈ Finset.Ioc y m, fb n) := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hdm := hd0 m hm
      simp only [Finset.mem_Ico] at hm
      exact mul_le_mul_of_nonneg_left (hBge m (by omega)) hdm
    have hsplit : ∑ m ∈ Finset.Ico (y+1) N,
          (c m - c (m+1)) * ((((m+1).primesBelow.card : ℝ)) - ((y:ℝ)+1))
        = (∑ m ∈ Finset.Ico (y+1) N, (c m - c (m+1)) * (((m+1).primesBelow.card : ℝ)))
          - ((y:ℝ)+1) * (∑ m ∈ Finset.Ico (y+1) N, (c m - c (m+1))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    have htel : ∑ m ∈ Finset.Ico (y+1) N, (c m - c (m+1)) = c (y+1) - c N :=
      telescope c hyN1
    rw [hsplit, htel] at hBsum
    have hexp : ((y:ℝ)+1) * (c (y+1) - c N)
        = ((y:ℝ)+1) * c (y+1) - ((y:ℝ)+1) * c N := by ring
    linarith
  rw [hLHS, hRHS]
  exact step1.trans (mul_le_mul_of_nonneg_left step2 hδ)

theorem recipSumIoc_le_of_dominated' {δ : ℝ} (hδ : 0 ≤ δ) {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N)
    (hdom : ∀ t, y < t → t ≤ N + 1 → (piP P t : ℝ) ≤ δ * (t.primesBelow.card : ℝ)) :
    recipSumIoc P y N ≤ δ * (9 + 12 * Real.log (Real.log N / Real.log y)) := by
  have h1 := recipSumIoc_le_of_dominated P hδ y N hdom
  have hy2 : (2:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have hyNr : (y:ℝ) ≤ (N:ℝ) := by exact_mod_cast hyN
  have key := NormalNumbers.PrimeModel.PrimeDensity.primeRecipSum_le (y:ℝ) hy2 N hyNr
  have hset : (Finset.Iic N).filter (fun p => Nat.Prime p ∧ ((y:ℝ)) < (p:ℝ))
      = (Finset.Ioc y N).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc, Nat.cast_lt]
    tauto
  rw [hset] at key
  have h2 : (∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (1 : ℝ) / p) + 1
      ≤ 9 + 12 * Real.log (Real.log N / Real.log y) := by linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hδ)


/-! ### (M2): the cut points `a_i = ⌊exp exp 2^i⌋₊` -/

/-- The cut points `a_i = ⌊exp exp 2^i⌋₊`. -/
noncomputable def aSeq (i : ℕ) : ℕ := ⌊Real.exp (Real.exp ((2:ℝ) ^ i))⌋₊

theorem aSeq_le (i : ℕ) : (aSeq i : ℝ) ≤ Real.exp (Real.exp ((2:ℝ) ^ i)) :=
  Nat.floor_le (by positivity)

theorem lt_aSeq_add_one (i : ℕ) : Real.exp (Real.exp ((2:ℝ) ^ i)) < (aSeq i : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem aSeq_mono {i j : ℕ} (h : i ≤ j) : aSeq i ≤ aSeq j := by
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_right₀ (by norm_num) h

private theorem nat_add_one_le_two_pow (i : ℕ) : (i:ℝ) + 1 ≤ (2:ℝ)^i := by
  induction i with
  | zero => norm_num
  | succ n ih =>
    have h2n : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hr : (2:ℝ)^(n+1) = 2 * 2^n := by ring
    push_cast
    rw [hr]
    linarith

theorem le_aSeq (i : ℕ) : i ≤ aSeq i := by
  by_contra hcon
  rw [Nat.not_le] at hcon
  have h1 : (aSeq i : ℝ) + 1 ≤ (i : ℝ) := by
    have : aSeq i + 1 ≤ i := hcon
    exact_mod_cast this
  have h2 : ((i:ℝ) + 2) ≤ Real.exp (Real.exp ((2:ℝ)^i)) := by
    have e1 : (i:ℝ) + 1 ≤ (2:ℝ)^i := nat_add_one_le_two_pow i
    have e2 : (2:ℝ)^i + 1 ≤ Real.exp ((2:ℝ)^i) := Real.add_one_le_exp _
    have e3 : Real.exp ((2:ℝ)^i) + 1 ≤ Real.exp (Real.exp ((2:ℝ)^i)) := Real.add_one_le_exp _
    linarith
  have := lt_aSeq_add_one i
  linarith

theorem log_ratio_bound (i : ℕ) (h2 : 2 ≤ aSeq i) :
    Real.log (Real.log (aSeq (i+1)) / Real.log (aSeq i)) ≤ Real.log 2 + (2:ℝ)^i := by
  set E : ℝ := (2:ℝ)^i with hE
  have hE1 : (1:ℝ) ≤ E := one_le_pow₀ (by norm_num)
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hexp1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexpE : Real.exp 1 ≤ Real.exp E := Real.exp_le_exp.mpr hE1
  have hE27 : (2.7182818283 : ℝ) < Real.exp E := lt_of_lt_of_le hexp1 hexpE
  have hexpexp : (2:ℝ) ≤ Real.exp (Real.exp E) := by
    have : Real.exp 1 ≤ Real.exp (Real.exp E) := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- upper bound on log (aSeq (i+1))
  have hposi1 : (0:ℝ) < (aSeq (i+1) : ℝ) := by
    have : 2 ≤ aSeq (i+1) := le_trans h2 (aSeq_mono (Nat.le_succ i))
    exact_mod_cast lt_of_lt_of_le (by norm_num) this
  have hE2 : (2:ℝ)^(i+1) = 2 * E := by rw [hE]; ring
  have hup : Real.log (aSeq (i+1)) ≤ Real.exp E * Real.exp E := by
    have h1 := Real.log_le_log hposi1 (aSeq_le (i+1))
    rw [Real.log_exp, hE2, two_mul, Real.exp_add] at h1
    exact h1
  -- lower bound on log (aSeq i)
  have hposi : (0:ℝ) < (aSeq i : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) h2
  have hhalf : Real.exp (Real.exp E) / 2 ≤ (aSeq i : ℝ) := by
    have := lt_aSeq_add_one i
    rw [← hE] at this
    linarith
  have hlow : Real.exp E - Real.log 2 ≤ Real.log (aSeq i) := by
    have h1 := Real.log_le_log (by positivity : (0:ℝ) < Real.exp (Real.exp E) / 2) hhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_exp] at h1
    exact h1
  have hlogpos : (0:ℝ) < Real.log (aSeq i) := by linarith
  have hratio : Real.log (aSeq (i+1)) / Real.log (aSeq i) ≤ 2 * Real.exp E := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [hlow, hup, hE27, hlog2]
  have hrpos : (0:ℝ) < Real.log (aSeq (i+1)) / Real.log (aSeq i) := by
    apply div_pos _ hlogpos
    have : Real.exp E - Real.log 2 ≤ Real.log (aSeq (i+1)) := by
      have := Real.log_le_log hposi (by exact_mod_cast aSeq_mono (Nat.le_succ i) :
        ((aSeq i : ℝ)) ≤ (aSeq (i+1) : ℝ))
      linarith
    linarith
  have := Real.log_le_log hrpos hratio
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at this
  exact this


/-- **(M2) accumulated mass under `Sparse`.** -/
theorem recipSumLe_le_of_sparse (hS : Sparse P) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      recipSumLe P N ≤ C + 100 * Real.log (Real.log (Real.log N)) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hS
  set i₀ : ℕ := max x₀ 2 with hi₀
  have hi₀2 : 2 ≤ i₀ := le_max_right _ _
  have haSeq2 : ∀ i, i₀ ≤ i → 2 ≤ aSeq i := fun i hi =>
    le_trans (le_trans hi₀2 hi) (le_aSeq i)
  -- density domination on each block
  have hdom : ∀ i, i₀ ≤ i → ∀ t : ℕ, aSeq i < t →
      (piP P t : ℝ) ≤ (1 / (2:ℝ)^i) * (t.primesBelow.card : ℝ) := by
    intro i hi t ht
    have hEpos : (0:ℝ) < (2:ℝ)^i := by positivity
    have hE1 : (1:ℝ) ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num)
    have htx : x₀ ≤ t := le_trans (le_trans (le_max_left x₀ 2) (le_trans hi (le_aSeq i))) ht.le
    have hsp := hx₀ t htx
    -- log log t > 2 ^ i
    have htr : Real.exp (Real.exp ((2:ℝ)^i)) < (t : ℝ) := by
      have h1 := lt_aSeq_add_one i
      have h2 : (aSeq i : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast ht
      linarith
    have hlt1 : Real.exp ((2:ℝ)^i) < Real.log t := by
      have := Real.log_lt_log (by positivity) htr
      rwa [Real.log_exp] at this
    have hll : (2:ℝ)^i < Real.log (Real.log t) := by
      have := Real.log_lt_log (by positivity) hlt1
      rwa [Real.log_exp] at this
    have hpiP0 : (0:ℝ) ≤ (piP P t : ℝ) := by positivity
    have hkey : (piP P t : ℝ) * (2:ℝ)^i ≤ (t.primesBelow.card : ℝ) := by
      nlinarith [hsp, hpiP0, hll]
    calc (piP P t : ℝ) = (1 / (2:ℝ)^i) * ((piP P t : ℝ) * (2:ℝ)^i) := by
          field_simp
      _ ≤ (1 / (2:ℝ)^i) * (t.primesBelow.card : ℝ) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
  -- each block carries mass at most 30
  have hblock : ∀ i, i₀ ≤ i → recipSumIoc P (aSeq i) (aSeq (i+1)) ≤ 30 := by
    intro i hi
    have hE1 : (1:ℝ) ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num)
    have hEpos : (0:ℝ) < (2:ℝ)^i := by positivity
    have h := recipSumIoc_le_of_dominated' P (δ := 1 / (2:ℝ)^i) (by positivity)
      (haSeq2 i hi) (aSeq_mono (Nat.le_succ i))
      (fun t ht _ => hdom i hi t ht)
    have hL := log_ratio_bound i (haSeq2 i hi)
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hinv : 1 / (2:ℝ)^i ≤ 1 := by
      rw [div_le_one hEpos]; exact hE1
    have hinv0 : (0:ℝ) < 1 / (2:ℝ)^i := by positivity
    have hstep : (1 / (2:ℝ)^i) * (9 + 12 * Real.log (Real.log (aSeq (i+1)) / Real.log (aSeq i)))
        ≤ (1 / (2:ℝ)^i) * (9 + 12 * (Real.log 2 + (2:ℝ)^i)) :=
      mul_le_mul_of_nonneg_left (by linarith) hinv0.le
    have hid : (1 / (2:ℝ)^i) * (9 + 12 * (Real.log 2 + (2:ℝ)^i))
        = (1 / (2:ℝ)^i) * (9 + 12 * Real.log 2) + 12 := by
      field_simp; ring
    have hfin : (1 / (2:ℝ)^i) * (9 + 12 * Real.log 2) ≤ 18 := by
      have : (0:ℝ) ≤ 9 + 12 * Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      nlinarith [hinv, hinv0, hlog2]
    linarith
  -- telescoping the blocks
  have hind : ∀ n : ℕ, recipSumLe P (aSeq (i₀ + n)) ≤ recipSumLe P (aSeq i₀) + 30 * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hmono : aSeq (i₀ + n) ≤ aSeq (i₀ + (n+1)) := aSeq_mono (by omega)
      have hsp : recipSumLe P (aSeq (i₀ + (n+1)))
          = recipSumLe P (aSeq (i₀ + n)) + recipSumIoc P (aSeq (i₀ + n)) (aSeq (i₀ + (n+1))) :=
        recipSumLe_add_recipSumIoc P hmono
      have hb : recipSumIoc P (aSeq (i₀ + n)) (aSeq (i₀ + n + 1)) ≤ 30 :=
        hblock (i₀ + n) (by omega)
      have hrw : i₀ + (n + 1) = i₀ + n + 1 := by omega
      rw [hrw] at hsp
      push_cast
      rw [hrw, hsp]
      linarith
  refine ⟨recipSumLe P (aSeq i₀) + 30, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 21] with N hN
  have hN0 : (0:ℝ) < (N:ℝ) := by
    have : (21:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hexp3 : Real.exp 3 ≤ 21 := by
    have h : Real.exp 1 ^ (3 : ℕ) = Real.exp (3 : ℕ) := Real.exp_one_pow 3
    have h2 : Real.exp 1 ^ (3 : ℕ) ≤ (2.7182818286 : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 3
    rw [h] at h2
    norm_num at h2 ⊢
    linarith
  have hlogN : (3:ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have : (21:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hlogN0 : (0:ℝ) < Real.log N := by linarith
  have hL2 : (1:ℝ) ≤ Real.log (Real.log N) := by
    rw [Real.le_log_iff_exp_le hlogN0]
    have := Real.exp_one_lt_d9
    linarith
  have hL2pos : (0:ℝ) < Real.log (Real.log N) := by linarith
  have hL3 : (0:ℝ) ≤ Real.log (Real.log (Real.log N)) := Real.log_nonneg hL2
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set u : ℝ := Real.log (Real.log (Real.log N)) / Real.log 2 with hu
  have hu0 : (0:ℝ) ≤ u := div_nonneg hL3 hlog2pos.le
  set n : ℕ := ⌊u⌋₊ + 1 with hn
  have hnu : u < (n:ℝ) := by
    rw [hn]; push_cast; exact Nat.lt_floor_add_one u
  have hnu' : (n:ℝ) ≤ u + 1 := by
    rw [hn]; push_cast; linarith [Nat.floor_le hu0]
  -- N ≤ aSeq (i₀ + n)
  have hlt : Real.log (Real.log (Real.log N)) < (n:ℝ) * Real.log 2 := by
    have h1 : u * Real.log 2 < (n:ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_right hnu hlog2pos
    rw [hu] at h1
    rw [div_mul_cancel₀] at h1
    · exact h1
    · exact ne_of_gt hlog2pos
  have hL2lt : Real.log (Real.log N) < (2:ℝ)^n := by
    have h2 : Real.log (Real.log (Real.log N)) < Real.log ((2:ℝ)^n) := by
      rw [Real.log_pow]; exact_mod_cast hlt
    have h3 := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log hL2pos, Real.exp_log (by positivity)] at h3
  have hpow : (2:ℝ)^n ≤ (2:ℝ)^(i₀ + n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hNle : N ≤ aSeq (i₀ + n) := by
    have h1 : Real.log (Real.log N) < (2:ℝ)^(i₀ + n) := lt_of_lt_of_le hL2lt hpow
    have h2 : (N:ℝ) < Real.exp (Real.exp ((2:ℝ)^(i₀ + n))) := by
      have h3 := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr h1)
      rwa [Real.exp_log hlogN0, Real.exp_log hN0] at h3
    have h4 := lt_aSeq_add_one (i₀ + n)
    have h5 : (N:ℝ) < (aSeq (i₀ + n) : ℝ) + 1 := by linarith
    have h6 : N < aSeq (i₀ + n) + 1 := by exact_mod_cast h5
    omega
  calc recipSumLe P N ≤ recipSumLe P (aSeq (i₀ + n)) := recipSumLe_mono P hNle
    _ ≤ recipSumLe P (aSeq i₀) + 30 * n := hind n
    _ ≤ recipSumLe P (aSeq i₀) + 30 * (u + 1) := by linarith
    _ ≤ (recipSumLe P (aSeq i₀) + 30) + 100 * Real.log (Real.log (Real.log N)) := by
        have hkey : 30 * u ≤ 100 * Real.log (Real.log (Real.log N)) := by
          have h9 := Real.log_two_gt_d9
          have hueq : u * Real.log 2 = Real.log (Real.log (Real.log N)) := by
            rw [hu]; exact div_mul_cancel₀ _ (ne_of_gt hlog2pos)
          have hprod : 0 ≤ u * (100 * Real.log 2 - 30) :=
            mul_nonneg hu0 (by linarith)
          nlinarith [hueq, hprod]
        linarith

end NormalNumbers.PrimeModel.DensityMass
