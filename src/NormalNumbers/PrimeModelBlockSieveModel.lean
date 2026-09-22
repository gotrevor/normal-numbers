import NormalNumbers.PrimeModelBlockSieve

/-!
# Lemma B, part 2: the relative defect under the product model

Lap 2 of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §3
"Relative defect" and `papers/ROUND2-multicutoff-astra.md` §4.  Still no arithmetic: this file is
about a finite family of blocks with independent block statistics.

* `model_defect` — if `V i ≤ E[U i] ≤ V i (1 + D̄ i)` with `V i > 0`, `D̄ i ≥ 0`, then
  `E[L] = ∏ E[U] − ∑ V_i D̄_i ∏_{j≠i} E[U_j] ≥ (∏ V)(1 − (∑ D̄) e^{∑ D̄})`.
  This is the packaged form of `E[L] ≥ (1 − η) ∏ V`.
* `exp_neg_two_mul_le_one_sub` — `e^{−2t} ≤ 1 − t` on `[0, 1/2]`, the inequality behind
  `V ≥ e^{−2λ}` (and the only place `2 d_p ≤ p` is used).
* `esymm_le_pow_div_factorial` — `∑_{E ⊆ B, |E| = k} ∏_E g ≤ (∑_B g)^k / k!` for `g ≥ 0`,
  the bound on `E[D] = e_{r+1}(g)`.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

variable {ι : Type*} [DecidableEq ι]

/-! ### The abstract model defect -/

/-- **Fable §3, relative defect** in abstract form: the model expectation of the graded block
minorant is at least `(∏ V)(1 − (∑ D̄) e^{∑ D̄})`. -/
theorem model_defect (s : Finset ι) (V Ub Db : ι → ℝ)
    (hV : ∀ i ∈ s, 0 < V i) (hDb : ∀ i ∈ s, 0 ≤ Db i)
    (hlow : ∀ i ∈ s, V i ≤ Ub i) (hhigh : ∀ i ∈ s, Ub i ≤ V i * (1 + Db i)) :
    (∏ i ∈ s, V i) * (1 - (∑ i ∈ s, Db i) * Real.exp (∑ i ∈ s, Db i))
      ≤ (∏ i ∈ s, Ub i) - ∑ i ∈ s, (V i * Db i) * ∏ j ∈ s.erase i, Ub j := by
  classical
  have hUbnn : ∀ i ∈ s, 0 ≤ Ub i := fun i hi => (hV i hi).le.trans (hlow i hi)
  have hVprod : 0 < ∏ i ∈ s, V i := Finset.prod_pos hV
  -- (1) `∏ V ≤ ∏ Ub`
  have h1 : (∏ i ∈ s, V i) ≤ ∏ i ∈ s, Ub i :=
    Finset.prod_le_prod (fun i hi => (hV i hi).le) hlow
  -- (2) `∏_{j ∈ s} (1 + D̄ j) ≤ exp (∑ D̄)`
  have hexp : (∏ i ∈ s, (1 + Db i)) ≤ Real.exp (∑ i ∈ s, Db i) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun i hi => by linarith [hDb i hi]) (fun i _ => ?_)
    rw [add_comm]
    exact Real.add_one_le_exp _
  have hexpnn : 0 ≤ Real.exp (∑ i ∈ s, Db i) := (Real.exp_pos _).le
  -- (3) each defect term is at most `D̄ i (∏ V) exp (∑ D̄)`
  have h2 : ∀ i ∈ s, (V i * Db i) * ∏ j ∈ s.erase i, Ub j
      ≤ Db i * ((∏ j ∈ s, V j) * Real.exp (∑ j ∈ s, Db j)) := by
    intro i hi
    have hsub : ∀ j ∈ s.erase i, j ∈ s := fun j hj => Finset.mem_of_mem_erase hj
    have hstep : (∏ j ∈ s.erase i, Ub j) ≤ ∏ j ∈ s.erase i, (V j * (1 + Db j)) :=
      Finset.prod_le_prod (fun j hj => hUbnn j (hsub j hj)) (fun j hj => hhigh j (hsub j hj))
    have hsplit : (∏ j ∈ s.erase i, (V j * (1 + Db j)))
        = (∏ j ∈ s.erase i, V j) * ∏ j ∈ s.erase i, (1 + Db j) := Finset.prod_mul_distrib
    have hVi : V i * ∏ j ∈ s.erase i, V j = ∏ j ∈ s, V j := Finset.mul_prod_erase s V hi
    have honenn' : 0 ≤ ∏ j ∈ s.erase i, (1 + Db j) :=
      Finset.prod_nonneg fun j hj => by linarith [hDb j (Finset.mem_of_mem_erase hj)]
    have hone : (∏ j ∈ s.erase i, (1 + Db j)) ≤ ∏ j ∈ s, (1 + Db j) := by
      have hfac : (1 + Db i) * ∏ j ∈ s.erase i, (1 + Db j) = ∏ j ∈ s, (1 + Db j) :=
        Finset.mul_prod_erase s (fun j => 1 + Db j) hi
      nlinarith [hDb i hi, honenn']
    have hprodnn : 0 ≤ ∏ j ∈ s.erase i, V j :=
      Finset.prod_nonneg fun j hj => (hV j (hsub j hj)).le
    have honenn : 0 ≤ ∏ j ∈ s.erase i, (1 + Db j) :=
      Finset.prod_nonneg fun j hj => by linarith [hDb j (hsub j hj)]
    have hDbi : 0 ≤ Db i := hDb i hi
    have hVipos : 0 < V i := hV i hi
    calc (V i * Db i) * ∏ j ∈ s.erase i, Ub j
        ≤ (V i * Db i) * ((∏ j ∈ s.erase i, V j) * ∏ j ∈ s.erase i, (1 + Db j)) := by
          refine mul_le_mul_of_nonneg_left (hstep.trans_eq hsplit) ?_
          positivity
      _ = Db i * ((V i * ∏ j ∈ s.erase i, V j) * ∏ j ∈ s.erase i, (1 + Db j)) := by ring
      _ = Db i * ((∏ j ∈ s, V j) * ∏ j ∈ s.erase i, (1 + Db j)) := by rw [hVi]
      _ ≤ Db i * ((∏ j ∈ s, V j) * Real.exp (∑ j ∈ s, Db j)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hone.trans hexp) hVprod.le)
            hDbi
  have h3 : (∑ i ∈ s, (V i * Db i) * ∏ j ∈ s.erase i, Ub j)
      ≤ (∑ i ∈ s, Db i) * ((∏ j ∈ s, V j) * Real.exp (∑ j ∈ s, Db j)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum h2
  nlinarith [hVprod, hexpnn]

/-! ### `1 − t ≥ e^{−2t}` on `[0, 1/2]` -/

/-- On `[0, 1/2]`, `e^{−2t} ≤ 1 − t`.  Proof: `1/(1−t) ≤ 1 + 2t ≤ e^{2t}`, the first step
being `t(1 − 2t) ≥ 0`. -/
theorem exp_neg_two_mul_le_one_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    Real.exp (-(2 * t)) ≤ 1 - t := by
  have hlt : 0 < 1 - t := by linarith
  have hexp : 1 + 2 * t ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t)
    linarith
  have hinv : 1 ≤ (1 + 2 * t) * (1 - t) := by nlinarith
  have hkey : 1 ≤ Real.exp (2 * t) * (1 - t) := by nlinarith [Real.exp_pos (2 * t)]
  have hexppos : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hexppos]
  linarith

/-! ### `e_k(g) ≤ (∑ g)^k / k!` -/

variable {α : Type*} [DecidableEq α]

/-- The `k`-th elementary symmetric sum of `g` over `B`. -/
noncomputable def esymmOn (g : α → ℝ) (B : Finset α) (k : ℕ) : ℝ :=
  ∑ E ∈ B.powersetCard k, ∏ p ∈ E, g p

theorem esymmOn_nonneg (g : α → ℝ) (hg : ∀ p, 0 ≤ g p) (B : Finset α) (k : ℕ) :
    0 ≤ esymmOn g B k :=
  Finset.sum_nonneg fun E _ => Finset.prod_nonneg fun p _ => hg p

@[simp] theorem esymmOn_zero (g : α → ℝ) (B : Finset α) : esymmOn g B 0 = 1 := by
  simp [esymmOn]

@[simp] theorem esymmOn_empty_succ (g : α → ℝ) (k : ℕ) : esymmOn g ∅ (k + 1) = 0 := by
  have h : (∅ : Finset α).powersetCard (k + 1) = ∅ :=
    Finset.powersetCard_eq_empty.2 (by simp)
  simp [esymmOn, h]

/-- Pascal-type recursion for the elementary symmetric sums. -/
theorem esymmOn_insert (g : α → ℝ) {a : α} {B : Finset α} (ha : a ∉ B) (k : ℕ) :
    esymmOn g (insert a B) (k + 1) = esymmOn g B (k + 1) + g a * esymmOn g B k := by
  classical
  have hdisj : Disjoint (Finset.powersetCard (k + 1) B)
      ((Finset.powersetCard k B).image (insert a)) := by
    rw [Finset.disjoint_right]
    intro E hE hE'
    rw [Finset.mem_image] at hE
    obtain ⟨F, _, rfl⟩ := hE
    rw [Finset.mem_powersetCard] at hE'
    exact ha (hE'.1 (Finset.mem_insert_self a F))
  have hinj : Set.InjOn (insert a) (Finset.powersetCard k B : Set (Finset α)) := by
    intro E hE F hF hEF
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hE hF
    have h1 : (insert a E).erase a = E := Finset.erase_insert (fun h => ha (hE.1 h))
    have h2 : (insert a F).erase a = F := Finset.erase_insert (fun h => ha (hF.1 h))
    rw [← h1, ← h2, hEF]
  unfold esymmOn
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj,
    Finset.sum_image (f := fun E => ∏ p ∈ E, g p) hinj]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [Finset.mem_powersetCard] at hE
  have hnot : a ∉ E := fun h => ha (hE.1 h)
  rw [Finset.prod_insert hnot]

/-- Two-term binomial minorant: `(x + y)^{k+1} ≥ y^{k+1} + (k+1) x y^k` for `x, y ≥ 0`. -/
theorem add_pow_ge_two_terms {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∀ k : ℕ, y ^ (k + 1) + (k + 1 : ℝ) * x * y ^ k ≤ (x + y) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp; linarith
  | succ k ih =>
      have hyk : 0 ≤ y ^ k := pow_nonneg hy k
      have hxy : 0 ≤ x + y := by linarith
      have hstep : (x + y) ^ (k + 2) = (x + y) * (x + y) ^ (k + 1) := by ring
      have h1 : (x + y) * (y ^ (k + 1) + (k + 1 : ℝ) * x * y ^ k)
          ≤ (x + y) * (x + y) ^ (k + 1) := mul_le_mul_of_nonneg_left ih hxy
      have hexp : (x + y) * (y ^ (k + 1) + (k + 1 : ℝ) * x * y ^ k)
          = y ^ (k + 2) + ((k + 1 : ℝ) + 1) * x * y ^ (k + 1)
            + (k + 1 : ℝ) * x ^ 2 * y ^ k := by ring
      have hlast : 0 ≤ (k + 1 : ℝ) * x ^ 2 * y ^ k := by positivity
      have : y ^ (k + 2) + ((k + 1 : ℝ) + 1) * x * y ^ (k + 1) ≤ (x + y) ^ (k + 2) := by
        rw [hstep]; linarith [h1, hexp ▸ h1]
      convert this using 3 <;> push_cast <;> ring

/-- **The factorial bound**: `k! · e_k(g) ≤ (∑_B g)^k` for a nonnegative weight. -/
theorem factorial_mul_esymmOn_le (g : α → ℝ) (hg : ∀ p, 0 ≤ g p) :
    ∀ (B : Finset α) (k : ℕ), (k.factorial : ℝ) * esymmOn g B k ≤ (∑ p ∈ B, g p) ^ k := by
  classical
  intro B
  induction B using Finset.induction with
  | empty =>
      intro k
      cases k with
      | zero => simp
      | succ m => simp
  | insert a B ha ih =>
      intro k
      cases k with
      | zero => simp
      | succ m =>
          have hS' : 0 ≤ ∑ p ∈ B, g p := Finset.sum_nonneg fun p _ => hg p
          have hga : 0 ≤ g a := hg a
          have hem : 0 ≤ esymmOn g B m := esymmOn_nonneg g hg B m
          have hfac : ((m + 1).factorial : ℝ) = (m + 1 : ℝ) * (m.factorial : ℝ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          have hA : ((m + 1).factorial : ℝ) * esymmOn g B (m + 1) ≤ (∑ p ∈ B, g p) ^ (m + 1) :=
            ih (m + 1)
          have hB : ((m + 1).factorial : ℝ) * (g a * esymmOn g B m)
              ≤ (m + 1 : ℝ) * g a * (∑ p ∈ B, g p) ^ m := by
            rw [hfac]
            have hmul := mul_le_mul_of_nonneg_left (ih m)
              (show (0:ℝ) ≤ ((m:ℝ) + 1) * g a by positivity)
            nlinarith [hmul]
          have hbin := add_pow_ge_two_terms hga hS' m
          rw [Finset.sum_insert ha, esymmOn_insert g ha m, mul_add]
          linarith


/-! ### `n! ≥ (n/e)^n` and the per-block defect -/

/-- `n^n ≤ n! e^n`, i.e. `n! ≥ (n/e)^n`.  Induction via `(1 + 1/n)^n ≤ e`. -/
theorem pow_self_le_factorial_mul_exp : ∀ n : ℕ,
    (n : ℝ) ^ n ≤ (n.factorial : ℝ) * Real.exp n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hnr : (0:ℝ) < n := by exact_mod_cast hn
        -- `(n+1)^n ≤ n^n e`
        have hstep : ((n : ℝ) + 1) ^ n ≤ (n : ℝ) ^ n * Real.exp 1 := by
          have h1 : (1 + 1 / (n:ℝ)) ^ n ≤ Real.exp 1 := by
            have hb : (1 + 1 / (n:ℝ)) ≤ Real.exp (1 / (n:ℝ)) := by
              have := Real.add_one_le_exp (1 / (n:ℝ)); linarith
            have hbn : (0:ℝ) ≤ 1 + 1 / (n:ℝ) := by positivity
            calc (1 + 1 / (n:ℝ)) ^ n ≤ (Real.exp (1 / (n:ℝ))) ^ n := by
                  exact pow_le_pow_left₀ hbn hb n
              _ = Real.exp ((n:ℝ) * (1 / (n:ℝ))) := by
                  rw [← Real.exp_nat_mul]
              _ = Real.exp 1 := by
                  rw [mul_one_div, div_self (ne_of_gt hnr)]
          have hid : ((n:ℝ) + 1) ^ n = (n:ℝ) ^ n * (1 + 1 / (n:ℝ)) ^ n := by
            rw [← mul_pow]
            congr 1
            field_simp
          rw [hid]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have hfac : (((n+1).factorial : ℝ)) = ((n:ℝ) + 1) * (n.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hexp : Real.exp ((n:ℝ) + 1) = Real.exp n * Real.exp 1 := by
          rw [← Real.exp_add]
        have hnn : (0:ℝ) ≤ (n:ℝ) ^ n := by positivity
        have hexppos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
        push_cast
        calc ((n:ℝ) + 1) ^ (n + 1) = ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ n := by ring
          _ ≤ ((n:ℝ) + 1) * ((n:ℝ) ^ n * Real.exp 1) := by
              exact mul_le_mul_of_nonneg_left hstep (by positivity)
          _ ≤ ((n:ℝ) + 1) * (((n.factorial : ℝ) * Real.exp n) * Real.exp 1) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right ih hexppos.le
          _ = (((n+1).factorial : ℝ)) * Real.exp ((n:ℝ) + 1) := by
              rw [hfac, hexp]; ring
      
/-- `e/8 ≤ e^{−1}` (i.e. `e² ≤ 8`), the numerical step behind `8ed/(r+1) ≤ 1/2`. -/
theorem exp_one_div_eight_le : Real.exp 1 / 8 ≤ Real.exp (-1) := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  have hsq : Real.exp 1 * Real.exp 1 ≤ 8 := by nlinarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (by norm_num) hpos]
  linarith

/-- **The per-block defect bound** (Fable §3): with `g ≤ 1/2` on the block, block mass
`≤ 8d` and the even degree `r = 64d + 2u + 2l + 4`, the defect `e_{r+1}(g)` is at most
`e^{−u−l−2}` times the block's model density `∏ (1 − g)`. -/
theorem block_defect_le {d u l : ℕ} (hd : 1 ≤ d) (g : α → ℝ) (B : Finset α)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p ∈ B, g p ≤ 1 / 2)
    (hmass : ∑ p ∈ B, g p ≤ 8 * d) :
    esymmOn g B (64 * d + 2 * u + 2 * l + 5)
      ≤ Real.exp (-(u:ℝ) - l - 2) * ∏ p ∈ B, (1 - g p) := by
  set n : ℕ := 64 * d + 2 * u + 2 * l + 5 with hn
  set lam : ℝ := ∑ p ∈ B, g p with hlam
  have hlam0 : 0 ≤ lam := Finset.sum_nonneg fun p _ => hg0 p
  have hnr : (64 * (d:ℝ)) ≤ (n:ℝ) := by rw [hn]; push_cast; linarith
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  -- (1) the model density dominates `exp (−2λ)`
  have hV : Real.exp (-(2 * lam)) ≤ ∏ p ∈ B, (1 - g p) := by
    have hprod : (∏ p ∈ B, Real.exp (-(2 * g p))) = Real.exp (-(2 * lam)) := by
      rw [← Real.exp_sum, hlam, Finset.mul_sum, Finset.sum_neg_distrib]
    rw [← hprod]
    exact Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le)
      (fun p hp => exp_neg_two_mul_le_one_sub (hg0 p) (hg1 p hp))
  -- (2) the factorial bound, then `λ ≤ n/8`
  have hfac := factorial_mul_esymmOn_le g hg0 B n
  have hfacpos : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hlamn : lam ≤ (n:ℝ) / 8 := by
    have : (8 : ℝ) * d ≤ (n:ℝ) / 8 := by linarith
    exact hmass.trans this
  have hfacge : ((n:ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    have h := pow_self_le_factorial_mul_exp n
    have hexppos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc (n:ℝ) ^ n ≤ (n.factorial : ℝ) * Real.exp n := h
      _ = (n.factorial : ℝ) * (Real.exp 1) ^ n := by
          rw [← Real.exp_nat_mul]; ring_nf
  -- (3) `e_n ≤ λ^n / n! ≤ (e/8)^n ≤ e^{−n}`
  have hstep : esymmOn g B n ≤ (Real.exp (-1)) ^ n := by
    have he : esymmOn g B n ≤ lam ^ n / (n.factorial : ℝ) := by
      rw [le_div_iff₀ hfacpos]
      calc esymmOn g B n * (n.factorial : ℝ) = (n.factorial : ℝ) * esymmOn g B n := by ring
        _ ≤ lam ^ n := hfac
    have hnum : lam ^ n ≤ ((n:ℝ) / 8) ^ n := pow_le_pow_left₀ hlam0 hlamn n
    have hden : ((n:ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := hfacge
    have hdiv : lam ^ n / (n.factorial : ℝ) ≤ ((n:ℝ) / 8) ^ n / ((n:ℝ) / Real.exp 1) ^ n := by
      have hp : (0:ℝ) < ((n:ℝ) / Real.exp 1) ^ n := by positivity
      exact div_le_div₀ (by positivity) hnum hp hden
    have hid : ((n:ℝ) / 8) ^ n / ((n:ℝ) / Real.exp 1) ^ n = (Real.exp 1 / 8) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp
    have hmono : (Real.exp 1 / 8) ^ n ≤ (Real.exp (-1)) ^ n :=
      pow_le_pow_left₀ (by positivity) exp_one_div_eight_le n
    calc esymmOn g B n ≤ lam ^ n / (n.factorial : ℝ) := he
      _ ≤ ((n:ℝ) / 8) ^ n / ((n:ℝ) / Real.exp 1) ^ n := hdiv
      _ = (Real.exp 1 / 8) ^ n := hid
      _ ≤ (Real.exp (-1)) ^ n := hmono
  -- (4) numerics: `e^{−n} ≤ e^{−u−l−2} e^{−16 d} ≤ e^{−u−l−2} exp(−2λ)`
  have hexpn : (Real.exp (-1)) ^ n = Real.exp (-(n:ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hcount : -(n:ℝ) ≤ (-(u:ℝ) - l - 2) + (-(2 * lam)) := by
    have h2 : 2 * lam ≤ 16 * (d:ℝ) := by linarith
    rw [hn]; push_cast; linarith
  calc esymmOn g B n ≤ (Real.exp (-1)) ^ n := hstep
    _ = Real.exp (-(n:ℝ)) := hexpn
    _ ≤ Real.exp ((-(u:ℝ) - l - 2) + (-(2 * lam))) := Real.exp_le_exp.2 hcount
    _ = Real.exp (-(u:ℝ) - l - 2) * Real.exp (-(2 * lam)) := Real.exp_add _ _
    _ ≤ Real.exp (-(u:ℝ) - l - 2) * ∏ p ∈ B, (1 - g p) :=
        mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le

end NormalNumbers.PrimeModel.BlockSieve
