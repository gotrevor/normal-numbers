import NormalNumbers.PrimeModelGradedLemmaB
import NormalNumbers.PrimeModelJointLawGraded

/-!
# The per-atom lower bound from the graded sieve

Lap 6g of `KICKOFF-2026-09-22-multicutoff-lean.md`.  Theorem A (`KMT.window_bound_graded`) has
one remaining hypothesis: the per-atom estimate

    (1 − η) · μ(r,s) − R²/x ≤ ν(r,s)

for the joint model `μ` and the empirical law `ν`.  In the ungraded assembly this is
`JointLaw.empLaw_lower_atom`, proved from the nested sieve of `PrimeModelBrunLower`.  Here it
comes from the **graded block sieve** of laps 1–4: `BlockSieve.graded_brun_lower`.

The join has three pieces:

* `siftedCondD_const_iff` — with `d_p = k` on the sieve range, the graded sifted condition
  `SiftedCondD` is the ungraded `Radical.SiftedCond`, so `actual_state_sifted_iff` identifies
  the arithmetic filter with the joint-state fibre;
* `dpK` — the class count `p ↦ (if 2k ≤ p then k else 0)`, which satisfies `2 d_p ≤ p` for
  *every* `p` and equals `k` on the sieve range (all of whose primes exceed `2k`).  This is
  where the paper's `Q = primorial (2k)` split is used;
* `Radical.state_model_density` — the model atom is `(1/∏_A q) ∏_U (1 − k/q) / Q`, which is
  exactly the main term of `graded_brun_lower` divided by `x`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.BlockSieve

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.BrunGraded

/-- The constant class count, clipped below `2k` so that `2 d_p ≤ p` holds for every `p`. -/
def dpK (k : ℕ) : ℕ → ℕ := fun p => if 2 * k ≤ p then k else 0

theorem two_mul_dpK_le (k p : ℕ) : 2 * dpK k p ≤ p := by
  rw [dpK]
  split
  · omega
  · omega

theorem dpK_eq (k p : ℕ) (h : 2 * k ≤ p) : dpK k p = k := by rw [dpK, if_pos h]

/-- With `d_p = k` on the sieve range the graded sifted condition is the ungraded one. -/
theorem siftedCondD_const_iff {k : ℕ} (A U : Finset ℕ) (dd : ℕ → ℕ)
    (hU : ∀ p ∈ U, dd p = k) (jf : ℕ → Fin k) (Q r n : ℕ) :
    SiftedCondD A U dd (fun p => (jf p).val) Q r n ↔ Radical.SiftedCond k A U Q r jf n := by
  unfold SiftedCondD Radical.SiftedCond
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h p hp t
    exact h p hp t.val (by rw [hU p hp]; exact t.isLt)
  · intro h p hp t ht
    have ht' : t < k := by rw [hU p hp] at ht; exact ht
    exact h p hp ⟨t, ht'⟩

/-- **The per-atom lower bound from the graded sieve.** -/
theorem empLaw_lower_atom_graded {k : ℕ} (hk : 1 ≤ k) {P : Finset ℕ} {Q x : ℕ}
    (hPk : ∀ q ∈ P, 2 * k < q) (hPprime : ∀ q ∈ P, Nat.Prime q)
    (hQ : 0 < Q) (hx : 0 < x) (hQcop : ∀ p ∈ P, Nat.Coprime Q p)
    (r : Fin Q) (s : {q // q ∈ P} → Option (Fin k))
    {κ : Type*} [DecidableEq κ] (tt : Finset κ) (L : ℕ) (dd uu : κ → ℕ) (hdd : ∀ j, 1 ≤ dd j)
    (UU : κ → Finset ℕ) (yy : κ → ℝ) (hy : ∀ j, 1 ≤ yy j)
    (hUdisj : ∀ j j', j ≠ j' → Disjoint (UU j) (UU j'))
    (hUprime : ∀ j, ∀ p ∈ UU j, Nat.Prime p)
    (hcut : ∀ j ∈ tt, ∀ l < L, 2 ≤ cut yy j (l + 1))
    (hT1 : ∑ j ∈ tt, Real.exp (-(uu j : ℝ)) ≤ 1)
    (hkdd : ∀ j, k ≤ dd j)
    (hcover : (tt ×ˢ Finset.range L).biUnion (gradedBlock UU yy) = stateU P s) :
    (1 - 0.3 * ∑ j ∈ tt, Real.exp (-(uu j : ℝ)))
          * jointModel (Fin Q) k (primeRecip (primeOf P)) (r, s)
        - (gradedLevel tt dd uu yy) ^ 2 / x
      ≤ empLaw P Q x (r, s) := by
  classical
  have hk' : 0 < k := hk
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  set W : Finset ℕ := (tt ×ˢ Finset.range L).biUnion (gradedBlock UU yy) with hW
  set A : Finset ℕ := stateA P s with hA
  set jp : ℕ → ℕ := fun p => (stateShift P s hk' p).val with hjp
  have hWU : W = stateU P s := hcover
  have hWP : ∀ p ∈ W, p ∈ P := by rw [hWU]; exact fun p hp => stateU_subset hp
  have hAP : ∀ p ∈ A, p ∈ P := fun p hp => stateA_subset hp
  -- the arithmetic filter is the joint-state fibre
  have hdW : ∀ p ∈ W, dpK k p = k := fun p hp => dpK_eq k p (le_of_lt (hPk p (hWP p hp)))
  have hfilter : (range x).filter (SiftedCondD A W (dpK k) jp Q r.val)
      = (range x).filter (fun n => n % Q = r.val ∧ actualState k P n = s) := by
    refine Finset.filter_congr fun n _ => ?_
    rw [siftedCondD_const_iff A W (dpK k) hdW (stateShift P s hk') Q r.val n]
    rw [hWU, hA]
    exact (actual_state_sifted_iff (P := P) (s := s) hk' (fun q hq => lt_of_le_of_lt
      (by omega : k ≤ 2 * k) (hPk q hq)) Q r.val n).symm
  -- the graded sieve lower bound
  have hbrun := graded_brun_lower tt L dd uu hdd UU yy hy hUdisj hUprime hcut hT1
    (dpK k) jp (two_mul_dpK_le k) (fun j p hpj => by
      rw [dpK]
      split
      · exact hkdd j
      · exact Nat.zero_le _)
    A Q r.val x
    (fun p hp => hPprime p (hAP p hp))
    (fun p hp => lt_of_lt_of_le (Fin.is_lt _) (le_of_lt (lt_of_le_of_lt
      (by omega : k ≤ 2 * k) (hPk p (hAP p hp)))))
    (by
      rw [show (tt ×ˢ Finset.range L).biUnion (gradedBlock UU yy) = stateU P s from hcover]
      exact stateA_disjoint_stateU)
    hQ r.isLt
    (fun p hp => by
      rcases Finset.mem_union.1 hp with h | h
      · exact hQcop p (hAP p h)
      · exact hQcop p (hWP p h))
  rw [hfilter] at hbrun
  -- rewrite the product over `W` as the state's model density
  have hprodW : ∏ p ∈ W, (1 - (dpK k p : ℝ) / p) = ∏ q ∈ stateU P s, (1 - (k : ℝ) / q) := by
    rw [← hWU]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hdW p hp]
  rw [hprodW] at hbrun
  -- the model atom
  have hprodA : ((∏ p ∈ A, p : ℕ) : ℝ) = ∏ q ∈ A, (q : ℝ) := Nat.cast_prod _ _
  have hprodA0 : ((∏ p ∈ A, p : ℕ) : ℝ) ≠ 0 := by
    rw [hprodA]
    refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
    have := (hPprime q (hAP q hq)).pos
    positivity
  have hQ0 : ((Q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hmodel : jointModel (Fin Q) k (primeRecip (primeOf P)) (r, s)
      = ((1 / ((∏ p ∈ A, p : ℕ) : ℝ)) * ∏ q ∈ stateU P s, (1 - (k : ℝ) / q)) / (Q : ℝ) := by
    unfold jointModel
    rw [Fintype.card_fin]
    congr 1
    rw [show (primeRecip (primeOf P)) = Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ)) from
      rfl, state_model_density, hprodA, hA]
  have hgoal : (1 - 0.3 * ∑ j ∈ tt, Real.exp (-(uu j : ℝ)))
          * jointModel (Fin Q) k (primeRecip (primeOf P)) (r, s)
        - (gradedLevel tt dd uu yy) ^ 2 / x
      = ((x : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
            * ((1 - 0.3 * ∑ j ∈ tt, Real.exp (-(uu j : ℝ)))
              * ∏ q ∈ stateU P s, (1 - (k : ℝ) / q))
          - (gradedLevel tt dd uu yy) ^ 2) / x := by
    rw [hmodel]
    field_simp
  rw [hgoal]
  rw [empLaw]
  rw [div_le_div_iff_of_pos_right hxpos]
  exact hbrun

end NormalNumbers.PrimeModel.BlockSieve

#print axioms NormalNumbers.PrimeModel.BlockSieve.empLaw_lower_atom_graded
