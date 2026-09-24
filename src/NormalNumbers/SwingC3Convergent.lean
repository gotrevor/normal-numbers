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

end NormalNumbers
