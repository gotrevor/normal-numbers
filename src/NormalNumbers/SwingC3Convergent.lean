/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Mean

/-!
# The machinery closes UNCONDITIONALLY when `∑ 1/p` converges

Laps 5–12 reduced `ConjC3` to the master inequality

    ‖∑_{n<N} e(jn/Q)·e(h·L(n))‖  ≤  (period ∏_{p∈S, p≤K} p)·Q  +  16|h|·(discarded mass),

and showed the two terms fight: the period forces `K ≲ log N`, the discarded mass
`≍ N·∑_{p>K} 1/p` forces `K ≳ N`.  The *only* reason they fight is that `∑_p 1/p` diverges.

This file proves the theorem the machinery gives when it does not.  For **any** set `S` of
primes with `∑_{p∈S} 1/p < ∞`, coprime to `Q`, the twisted Weyl sum of the closed-form constant

    L_S(n)  =  ∑_{p ∈ S}  b^{n mod p}/(b^p − 1)        ( ≡ b^n · ∑_{p∈S} 1/(b^p−1)  mod 1 )

tends to `0` — unconditionally (`setTail_addChar_tendsto`).  So every ingredient of the swing is
complete and verified end to end, and the single missing input for `ConjC3` is isolated
exactly: **the divergence of `∑_p 1/p`**, nothing else.
-/

open Finset Filter Topology

namespace NormalNumbers

variable (S : ℕ → Prop) [DecidablePred S]

/-- The summand of the closed form over an arbitrary set `S` of primes. -/
noncomputable def setSummand (b n p : ℕ) : ℝ := if S p then tailPrimeTerm b p n else 0

/-- The closed-form constant's orbit, over an arbitrary set `S` of primes. -/
noncomputable def setTail (b n : ℕ) : ℝ := ∑' p : ℕ, setSummand S b n p

/-- Its truncation at `K`. -/
noncomputable def setTrunc (b K n : ℕ) : ℝ := ∑ p ∈ (range (K + 1)).filter S, tailPrimeTerm b p n

/-- The period of the truncation. -/
def setPeriod (K : ℕ) : ℕ := ∏ p ∈ (range (K + 1)).filter S, p

variable {S}

theorem setPeriod_pos (hSp : ∀ p, S p → p.Prime) (K : ℕ) : 0 < setPeriod S K :=
  Finset.prod_pos fun p hp => (hSp p (Finset.mem_filter.1 hp).2).pos

theorem setSummand_nonneg {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime) (n p : ℕ) :
    0 ≤ setSummand S b n p := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  rw [setSummand]
  split_ifs with hp
  · have hp2 : 2 ≤ p := (hSp p hp).two_le
    have : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
    rw [tailPrimeTerm]; positivity
  · exact le_rfl

theorem setSummand_le {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime) (n p : ℕ) :
    setSummand S b n p ≤ 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ p := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  rw [setSummand]
  split_ifs with hp
  · have h := tailPrimeSummand_le (b := b) (P := 0) hb n p
    rw [tailPrimeSummand, if_pos ⟨(hSp p hp).pos, hSp p hp⟩] at h
    exact h
  · positivity

theorem summable_setSummand {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime) (n : ℕ) :
    Summable (setSummand S b n) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  refine Summable.of_nonneg_of_le (fun p => setSummand_nonneg hb hSp n p)
    (fun p => setSummand_le hb hSp n p) ?_
  exact ((summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity)
    (by rw [inv_lt_one_iff₀]; right; linarith)).mul_left _)

/-- The truncation is the head of the closed form. -/
theorem setTrunc_eq_sum_range (b K n : ℕ) :
    setTrunc S b K n = ∑ p ∈ range (K + 1), setSummand S b n p := by
  rw [setTrunc, Finset.sum_filter]
  exact (Finset.sum_congr rfl fun p _ => by rw [setSummand]).symm

/-- The truncation defect is a nonnegative tail. -/
theorem setTail_sub_setTrunc {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime) (K n : ℕ) :
    setTail S b n - setTrunc S b K n = ∑' i : ℕ, setSummand S b n (i + (K + 1)) := by
  have hS := summable_setSummand hb hSp (S := S) n
  have hsplit := hS.sum_add_tsum_nat_add (K + 1)
  rw [setTail, setTrunc_eq_sum_range, ← hsplit]
  ring

theorem setTail_sub_setTrunc_nonneg {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime) (K n : ℕ) :
    0 ≤ setTail S b n - setTrunc S b K n := by
  rw [setTail_sub_setTrunc hb hSp]
  exact tsum_nonneg fun i => setSummand_nonneg hb hSp _ _

/-! ### The per-prime partial-sum bound -/

/-- **The key per-prime bound.**  The `+1` stub of `sum_range_tailPrimeTerm_le` is absorbed into
`N/p` when `p ≤ N` (since then `1 ≤ N/p`), and for `p > N` only a geometric term survives.  This
is what avoids needing any prime-counting input. -/
theorem sum_range_setSummand_le {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime) (N p : ℕ) :
    ∑ n ∈ range N, setSummand S b n p
      ≤ (if S p then 2 * (N : ℝ) / p * (1 / ((b : ℝ) - 1)) else 0)
        + (if N < p then 2 * (b : ℝ) ^ N * ((b : ℝ)⁻¹) ^ p else 0) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  by_cases hp : S p
  · have hpp : p.Prime := hSp p hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
    have hden : (0 : ℝ) < (b : ℝ) ^ p - 1 := by linarith
    have heq : ∀ n, setSummand S b n p = tailPrimeTerm b p n := fun n => if_pos hp
    rw [Finset.sum_congr rfl (fun n _ => heq n), if_pos hp]
    rcases le_or_gt p N with hpN | hpN
    · -- `p ≤ N`: absorb the stub
      have h := sum_range_tailPrimeTerm_le hb (p := p) hpp.pos N
      have hNp : (1 : ℝ) ≤ (N : ℝ) / p := by
        rw [le_div_iff₀ (by exact_mod_cast hpp.pos)]
        simp only [one_mul]
        exact_mod_cast hpN
      have hsecond : (0 : ℝ) ≤ (if N < p then 2 * (b : ℝ) ^ N * ((b : ℝ)⁻¹) ^ p else 0) := by
        split_ifs
        · positivity
        · exact le_rfl
      have : ((N : ℝ) / p + 1) * (1 / ((b : ℝ) - 1)) ≤ 2 * (N : ℝ) / p * (1 / ((b : ℝ) - 1)) := by
        rw [mul_div_assoc]
        have : (N : ℝ) / p + 1 ≤ 2 * ((N : ℝ) / p) := by linarith
        nlinarith [this, (by positivity : (0:ℝ) < 1 / ((b : ℝ) - 1))]
      linarith
    · -- `N < p`: the whole range is inside one period
      rw [if_pos hpN]
      have hval : ∀ n ∈ range N, tailPrimeTerm b p n = (b : ℝ) ^ n / ((b : ℝ) ^ p - 1) := by
        intro n hn
        rw [tailPrimeTerm, Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hn) hpN.le)]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_div]
      have hgeo : ∑ n ∈ range N, (b : ℝ) ^ n ≤ (b : ℝ) ^ N := by
        rw [geom_sum_eq (by intro hc; simp at hc; linarith) N]
        rw [div_le_iff₀ hb1]
        nlinarith [pow_pos hb0 N]
      have hinv : (1 : ℝ) / ((b : ℝ) ^ p - 1) ≤ 2 * ((b : ℝ) ^ p)⁻¹ := by
        rw [div_le_iff₀ hden]
        have hbp2 : (2 : ℝ) ≤ (b : ℝ) ^ p := by
          calc (2:ℝ) ≤ (b:ℝ) ^ 1 := by simpa using hbR
            _ ≤ (b:ℝ) ^ p := pow_le_pow_right₀ (by linarith) (by omega)
        have hX : (0:ℝ) < (b:ℝ) ^ p := by positivity
        have hinvX : ((b:ℝ) ^ p)⁻¹ * (b:ℝ) ^ p = 1 := inv_mul_cancel₀ (ne_of_gt hX)
        have hle : ((b:ℝ) ^ p)⁻¹ ≤ (2:ℝ)⁻¹ := by gcongr
        nlinarith [hinvX, hle, hX]
      have hnn : (0 : ℝ) ≤ 2 * (N : ℝ) / p * (1 / ((b : ℝ) - 1)) := by positivity
      have hstep : (∑ n ∈ range N, (b : ℝ) ^ n) / ((b : ℝ) ^ p - 1)
          ≤ 2 * (b : ℝ) ^ N * ((b : ℝ)⁻¹) ^ p := by
        rw [div_eq_mul_one_div, inv_pow]
        have h1 : (∑ n ∈ range N, (b : ℝ) ^ n) * (1 / ((b : ℝ) ^ p - 1))
            ≤ (b : ℝ) ^ N * (2 * ((b : ℝ) ^ p)⁻¹) := by
          apply mul_le_mul hgeo hinv (by positivity) (by positivity)
        calc (∑ n ∈ range N, (b : ℝ) ^ n) * (1 / ((b : ℝ) ^ p - 1))
            ≤ (b : ℝ) ^ N * (2 * ((b : ℝ) ^ p)⁻¹) := h1
          _ = 2 * (b : ℝ) ^ N * ((b : ℝ) ^ p)⁻¹ := by ring
      linarith
  · have hz : ∀ n, setSummand S b n p = 0 := fun n => if_neg hp
    rw [Finset.sum_congr rfl (fun n _ => hz n), Finset.sum_const_zero, if_neg hp, zero_add]
    split_ifs
    · positivity
    · exact le_rfl

/-! ### The aggregate bound over the discarded primes -/

/-- The discarded tail, indexed by the primes themselves. -/
theorem setTail_sub_setTrunc_eq {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime) (K n : ℕ) :
    setTail S b n - setTrunc S b K n
      = ∑' p : ℕ, (if K < p then setSummand S b n p else 0) := by
  have hS := summable_setSummand hb hSp (S := S) n
  have hg : Summable (fun p => if K < p then setSummand S b n p else 0) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hS
    · split_ifs
      · exact setSummand_nonneg hb hSp _ _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact setSummand_nonneg hb hSp _ _
  have hsplit := hg.sum_add_tsum_nat_add (K + 1)
  have hhead : ∑ p ∈ range (K + 1), (if K < p then setSummand S b n p else 0) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    exact if_neg (by simp only [Finset.mem_range] at hp; omega)
  have htail : ∀ i : ℕ, (if K < i + (K + 1) then setSummand S b n (i + (K + 1)) else 0)
      = setSummand S b n (i + (K + 1)) := fun i => if_pos (by omega)
  rw [setTail_sub_setTrunc hb hSp, ← hsplit, hhead, zero_add]
  exact (tsum_congr htail).symm

/-- The reciprocal tail of `S` beyond `K`. -/
noncomputable def recipTail (S : ℕ → Prop) [DecidablePred S] (K : ℕ) : ℝ :=
  ∑' p : ℕ, (if S p ∧ K < p then (1 : ℝ) / p else 0)

theorem summable_recipTail_summand (hconv : Summable (fun p => if S p then (1 : ℝ) / p else 0))
    (K : ℕ) : Summable (fun p : ℕ => if S p ∧ K < p then (1 : ℝ) / p else 0) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hconv
  · split_ifs
    · positivity
    · exact le_rfl
  · split_ifs with h1 h2
    · exact le_rfl
    · exact absurd h1.1 h2
    · positivity
    · exact le_rfl

/-- The reciprocal tail is antitone: more of `S` is discarded for smaller `K`. -/
theorem recipTail_antitone (hconv : Summable (fun p => if S p then (1 : ℝ) / p else 0))
    {K K' : ℕ} (h : K ≤ K') : recipTail S K' ≤ recipTail S K := by
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_recipTail_summand hconv K')
    (summable_recipTail_summand hconv K)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, by omega⟩ h2
  · positivity
  · exact le_rfl

/-- **The aggregate discarded mass.**  Uniformly in `K`, the mean discarded mass is
`≤ 2·(recipTail S K)/(b−1)` up to an additive constant. -/
theorem sum_range_defect_le {b : ℕ} (hb : 2 ≤ b) (hSp : ∀ p, S p → p.Prime)
    (hconv : Summable (fun p => if S p then (1 : ℝ) / p else 0)) (K N : ℕ) :
    ∑ n ∈ range N, (setTail S b n - setTrunc S b K n)
      ≤ 2 * (N : ℝ) * (1 / ((b : ℝ) - 1)) * recipTail S K + 2 / ((b : ℝ) - 1) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  set r : ℝ := (b : ℝ)⁻¹ with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, inv_lt_one_iff₀]; right; linarith
  -- the two majorants
  set A : ℕ → ℝ := fun p => if S p ∧ K < p then 2 * (N : ℝ) * (1 / ((b : ℝ) - 1)) * (1 / p) else 0
    with hA
  set B : ℕ → ℝ := fun p => if N < p then 2 * (b : ℝ) ^ N * r ^ p else 0 with hB
  have hAsum : Summable A := by
    refine ((summable_recipTail_summand hconv K).mul_left
      (2 * (N : ℝ) * (1 / ((b : ℝ) - 1)))).congr fun p => ?_
    simp only [hA, mul_ite, mul_zero]
  have hBsum : Summable B := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left (2 * (b : ℝ) ^ N))
    · simp only [hB]; split_ifs
      · positivity
      · exact le_rfl
    · simp only [hB]; split_ifs
      · exact le_rfl
      · positivity
  -- swap the finite and infinite sums
  have hgsum : ∀ n : ℕ, Summable (fun p => if K < p then setSummand S b n p else 0) := by
    intro n
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (summable_setSummand hb hSp n)
    · split_ifs
      · exact setSummand_nonneg hb hSp _ _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact setSummand_nonneg hb hSp _ _
  have hswap : ∑ n ∈ range N, (setTail S b n - setTrunc S b K n)
      = ∑' p : ℕ, ∑ n ∈ range N, (if K < p then setSummand S b n p else 0) := by
    rw [Summable.tsum_finsetSum (fun n _ => hgsum n)]
    exact Finset.sum_congr rfl fun n _ => setTail_sub_setTrunc_eq hb hSp K n
  have hterm : ∀ p : ℕ, ∑ n ∈ range N, (if K < p then setSummand S b n p else 0) ≤ A p + B p := by
    intro p
    by_cases hKp : K < p
    · have hrw : ∀ n, (if K < p then setSummand S b n p else 0) = setSummand S b n p :=
        fun n => if_pos hKp
      rw [Finset.sum_congr rfl (fun n _ => hrw n)]
      refine le_trans (sum_range_setSummand_le hb hSp N p) ?_
      simp only [hA, hB]
      gcongr ?_ + ?_
      · by_cases hSpp : S p
        · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hSp p hSpp).pos.ne'
          rw [if_pos hSpp, if_pos (⟨hSpp, hKp⟩ : S p ∧ K < p)]
          apply le_of_eq
          field_simp

        · rw [if_neg hSpp, if_neg (fun hc : S p ∧ K < p => hSpp hc.1)]
      · exact le_rfl
    · have hrw : ∀ n, (if K < p then setSummand S b n p else 0) = 0 := fun n => if_neg hKp
      rw [Finset.sum_congr rfl (fun n _ => hrw n), Finset.sum_const_zero]
      simp only [hA, hB]
      have hA0 : (0:ℝ) ≤ (if S p ∧ K < p then 2 * (N : ℝ) * (1 / ((b : ℝ) - 1)) * (1 / p) else 0) := by
        split_ifs
        · positivity
        · exact le_rfl
      have hB0 : (0:ℝ) ≤ (if N < p then 2 * (b : ℝ) ^ N * r ^ p else 0) := by
        split_ifs
        · positivity
        · exact le_rfl
      linarith
  have hsumLHS : Summable (fun p => ∑ n ∈ range N, (if K < p then setSummand S b n p else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => Finset.sum_nonneg fun n _ => ?_) hterm
      (hAsum.add hBsum)
    split_ifs
    · exact setSummand_nonneg hb hSp _ _
    · exact le_rfl
  have hAval : ∑' p, A p = 2 * (N : ℝ) * (1 / ((b : ℝ) - 1)) * recipTail S K := by
    rw [recipTail, ← tsum_mul_left]
    exact tsum_congr fun p => by simp only [hA, mul_ite, mul_zero]
  have hBval : ∑' p, B p ≤ 2 / ((b : ℝ) - 1) := by
    have hhead : ∑ p ∈ range (N + 1), B p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [hB]
      exact if_neg (by simp only [Finset.mem_range] at hp; omega)
    have hsplit := hBsum.sum_add_tsum_nat_add (N + 1)
    have htail : ∀ i : ℕ, B (i + (N + 1)) = 2 * (b : ℝ) ^ N * r ^ (i + (N + 1)) := by
      intro i; simp only [hB]; exact if_pos (by omega)
    have hgeo : ∑' i : ℕ, (2 * (b : ℝ) ^ N * r ^ (i + (N + 1)))
        = 2 * (b : ℝ) ^ N * r ^ (N + 1) * (1 - r)⁻¹ := by
      rw [show (fun i : ℕ => 2 * (b : ℝ) ^ N * r ^ (i + (N + 1)))
          = fun i : ℕ => (2 * (b : ℝ) ^ N * r ^ (N + 1)) * r ^ i from
        funext fun i => by rw [pow_add]; ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
    rw [← hsplit, hhead, zero_add, tsum_congr htail, hgeo]
    have hrv : r ^ (N + 1) = ((b : ℝ) ^ N)⁻¹ * r := by
      rw [pow_succ, hr, ← inv_pow]
    have hinvr : (1 - r)⁻¹ = (b : ℝ) / ((b : ℝ) - 1) := by
      rw [hr]; field_simp
    rw [hrv, hinvr, hr]
    have hbN : (0:ℝ) < (b : ℝ) ^ N := by positivity
    field_simp
    norm_num
  calc ∑ n ∈ range N, (setTail S b n - setTrunc S b K n)
      = ∑' p : ℕ, ∑ n ∈ range N, (if K < p then setSummand S b n p else 0) := hswap
    _ ≤ ∑' p : ℕ, (A p + B p) :=
        Summable.tsum_le_tsum hterm hsumLHS (hAsum.add hBsum)
    _ = (∑' p, A p) + ∑' p, B p := hAsum.tsum_add hBsum
    _ ≤ 2 * (N : ℝ) * (1 / ((b : ℝ) - 1)) * recipTail S K + 2 / ((b : ℝ) - 1) := by
        rw [hAval]; linarith [hBval]

/-! ### The period side, for an arbitrary set of primes -/

theorem setTrunc_add_period {b : ℕ} (K n : ℕ) :
    setTrunc S b K (n + setPeriod S K) = setTrunc S b K n := by
  refine Finset.sum_congr rfl fun p hp => ?_
  refine tailPrimeTerm_congr ?_
  have hdvd : p ∣ setPeriod S K := Finset.dvd_prod_of_mem _ hp
  exact ((Nat.modEq_iff_dvd' (Nat.le_add_right n _)).2 (by simpa using hdvd)).symm

theorem coprime_setPeriod {Q : ℕ} (hSQ : ∀ p, S p → Nat.Coprime p Q) (K : ℕ) :
    Nat.Coprime (setPeriod S K) Q :=
  Nat.Coprime.prod_left (fun p hp => hSQ p (Finset.mem_filter.1 hp).2)

/-- **The complete-period sum vanishes**, for an arbitrary set `S` of primes coprime to `Q`. -/
theorem sum_addChar_setTrunc_eq_zero {b K Q j : ℕ} (hQ : 0 < Q)
    (hSp : ∀ p, S p → p.Prime) (hSQ : ∀ p, S p → Nat.Coprime p Q)
    (hj0 : 0 < j) (hjQ : j < Q) (h : ℤ) :
    ∑ n ∈ range (setPeriod S K * Q),
        ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ) = 0 :=
  sum_addChar_mul_periodic_eq_zero (setPeriod_pos hSp K) hQ (coprime_setPeriod hSQ K) hj0 hjQ
    _ (fun n => by rw [setTrunc_add_period])

/-- The quantitative truncated bound, for an arbitrary set `S`. -/
theorem norm_sum_addChar_setTrunc_le {b K Q j : ℕ} (hQ : 0 < Q)
    (hSp : ∀ p, S p → p.Prime) (hSQ : ∀ p, S p → Nat.Coprime p Q)
    (hj0 : 0 < j) (hjQ : j < Q) (h : ℤ) (N : ℕ) :
    ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ)‖ ≤ ((setPeriod S K * Q : ℕ) : ℝ) := by
  set L : ℕ := setPeriod S K * Q with hLdef
  have hL : 0 < L := Nat.mul_pos (setPeriod_pos hSp K) hQ
  set g : ℕ → ℂ := fun n => ee (((j : ℝ) * n / Q : ℝ) : ℂ)
    * ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ) with hgdef
  have hgper : ∀ n, g (n + L) = g n := by
    intro n
    have h1 : setTrunc S b K (n + L) = setTrunc S b K n := by
      refine Finset.sum_congr rfl fun p hp => ?_
      refine tailPrimeTerm_congr ?_
      have hdvd : p ∣ L := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hp) Q
      exact ((Nat.modEq_iff_dvd' (Nat.le_add_right n L)).2 (by simpa using hdvd)).symm
    have h2 : ee (((j : ℝ) * ((n + L : ℕ) : ℝ) / Q : ℝ) : ℂ)
        = ee (((j : ℝ) * n / Q : ℝ) : ℂ) := by
      have hQR : (Q : ℝ) ≠ 0 := by positivity
      have hreal : ((j : ℝ) * ((n + L : ℕ) : ℝ) / Q : ℝ)
          = ((j : ℝ) * n / Q : ℝ) + ((((j * setPeriod S K : ℕ) : ℤ) : ℝ)) := by
        rw [hLdef]; push_cast; field_simp
      rw [hreal, Complex.ofReal_add, Complex.ofReal_intCast, ee_add, ee_int, mul_one]
    rw [hgdef]; simp only; rw [h1, h2]
  have hzero : ∑ m ∈ range L, g m = 0 :=
    sum_addChar_setTrunc_eq_zero (b := b) (K := K) hQ hSp hSQ hj0 hjQ h
  have hnorm : ∀ n, ‖g n‖ ≤ 1 := by
    intro n; rw [hgdef]; simp only [norm_mul, norm_ee_real, mul_one, le_refl]
  exact norm_sum_range_le_of_period hL g hgper hzero hnorm N

/-- **The master inequality for an arbitrary set `S` of primes.** -/
theorem norm_sum_addChar_setTail_le {b K Q j : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (hSp : ∀ p, S p → p.Prime) (hSQ : ∀ p, S p → Nat.Coprime p Q)
    (hj0 : 0 < j) (hjQ : j < Q) (h : ℤ) (N : ℕ) :
    ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ee (((h : ℝ) * setTail S b n : ℝ) : ℂ)‖
      ≤ ((setPeriod S K * Q : ℕ) : ℝ)
        + 16 * |(h : ℝ)| * ∑ n ∈ range N, (setTail S b n - setTrunc S b K n) := by
  classical
  have hsplit : ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
      * ee (((h : ℝ) * setTail S b n : ℝ) : ℂ)
      = (∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
          * ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ))
        + ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
          * (ee (((h : ℝ) * setTail S b n : ℝ) : ℂ)
            - ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hAbd := norm_sum_addChar_setTrunc_le (b := b) (K := K) hQ hSp hSQ hj0 hjQ h N
  have hDbd : ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
      * (ee (((h : ℝ) * setTail S b n : ℝ) : ℂ)
        - ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ))‖
      ≤ 16 * |(h : ℝ)| * ∑ n ∈ range N, (setTail S b n - setTrunc S b K n) := by
    calc ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * (ee (((h : ℝ) * setTail S b n : ℝ) : ℂ)
          - ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ))‖
        ≤ ∑ n ∈ range N, ‖ee (((j : ℝ) * n / Q : ℝ) : ℂ)
            * (ee (((h : ℝ) * setTail S b n : ℝ) : ℂ)
              - ee (((h : ℝ) * setTrunc S b K n : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, 16 * |(h : ℝ)| * (setTail S b n - setTrunc S b K n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_ee_real, one_mul]
          refine le_trans (norm_ee_sub_ee_le _ _) ?_
          have hnn := setTail_sub_setTrunc_nonneg hb hSp K n
          have habs : |(h : ℝ) * setTail S b n - (h : ℝ) * setTrunc S b K n|
              = |(h : ℝ)| * (setTail S b n - setTrunc S b K n) := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hnn]
          rw [habs]
          ring_nf
          exact le_rfl
      _ = 16 * |(h : ℝ)| * ∑ n ∈ range N, (setTail S b n - setTrunc S b K n) := by
          rw [← Finset.mul_sum]
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (by linarith)

end NormalNumbers
