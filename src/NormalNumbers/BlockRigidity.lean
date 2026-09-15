/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Block rigidity: a shift-invariant density system dominated by the uniform one is uniform

This is the combinatorial heart of **"normal to base `b` ⇒ normal to base `b^K`"**, isolated
from every notion of normality, of digits, or of measure.

Setting.  Let `F m k` be a real number attached to the base-`b` word of length `m` whose numeric
value is `k < b^m`.  Think of `F m k` as the (limiting) density of that word among the read
positions lying in **one** residue class mod `K`, renormalised so the empty word has `F 0 0 = 1`.
Three structural facts are available for free:

* `right`  — refining on the right: `F m k = ∑_{s<b} F (m+1) (k·b + s)`;
* `shift`  — `K` steps of the "prepend a digit and drop one residue class" relation close up,
  because the class index is read mod `K`:  `F m k = ∑_{t<b^K} F (m+K) (t·b^m + k)`;
* `bdd`    — the `K` classes together carry the *unrestricted* density, which normality pins at
  `b^{-m}`; so a single class obeys `F m k ≤ C·b^{-m}` with `C = K`.

**Theorem (`Sys.eq_uniform`): these force `F m k = b^{-m}`.**  Measure-theoretically this is
"a `σ^K`-invariant measure absolutely continuous with respect to Bernoulli must *be* Bernoulli",
i.e. ergodicity of the Bernoulli shift.  The proof below is elementary and finite: the energy

    `A m = ∑_{k<b^m} b^m · (F m k)^2`

is nondecreasing with increments `Var m ≥ 0` (Cauchy–Schwarz on the `right` relation), bounded by
`C`; and the `shift` relation makes `Var` nondecreasing along each residue class mod `K`
(Cauchy–Schwarz again).  A summable nondecreasing sequence vanishes, so every increment is `0`,
so `A m = A 0 = 1`, and equality in Cauchy–Schwarz gives `F m k = b^{-m}`.

No measure theory, no compactness, no ergodic theorem.
-/

open Finset

namespace NormalNumbers.BlockRigidity

/-- Splitting `range (P*A)` along the division algorithm. -/
lemma sum_range_mul' {β : Type*} [AddCommMonoid β] (g : ℕ → β) (P A : ℕ) :
    ∑ w ∈ Finset.range (P * A), g w
      = ∑ a ∈ Finset.range P, ∑ e ∈ Finset.range A, g (a * A + e) := by
  induction P with
  | zero => simp
  | succ P ih =>
    have hsplit : (P + 1) * A = P * A + A := by ring
    rw [Finset.sum_range_succ, ← ih, hsplit]
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive g (Nat.zero_le (P * A)) (Nat.le_add_right (P * A) A),
      ← Finset.range_eq_Ico]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp

/-- **The density system.**  `F m k` is attached to the base-`b` word of length `m` and value
`k`; see the module docstring. -/
structure Sys (b K : ℕ) (C : ℝ) (F : ℕ → ℕ → ℝ) : Prop where
  bpos : 0 < b
  Kpos : 0 < K
  nonneg : ∀ m k, 0 ≤ F m k
  bdd : ∀ m k, F m k ≤ C / (b : ℝ) ^ m
  unit : F 0 0 = 1
  right : ∀ m k, F m k = ∑ s ∈ Finset.range b, F (m + 1) (k * b + s)
  shift : ∀ m k, F m k = ∑ t ∈ Finset.range (b ^ K), F (m + K) (t * b ^ m + k)

namespace Sys

variable {b K : ℕ} {C : ℝ} {F : ℕ → ℕ → ℝ}

/-- The energy of level `m`. -/
noncomputable def A (b : ℕ) (F : ℕ → ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (b ^ m), (b : ℝ) ^ m * (F m k) ^ 2

/-- The refinement defect at `(m, k, s)`. -/
noncomputable def D (b : ℕ) (F : ℕ → ℕ → ℝ) (m k s : ℕ) : ℝ :=
  F (m + 1) (k * b + s) - F m k / (b : ℝ)

/-- The energy increment of level `m`. -/
noncomputable def Var (b : ℕ) (F : ℕ → ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (b ^ m), ∑ s ∈ Finset.range b, (b : ℝ) ^ (m + 1) * (D b F m k s) ^ 2

lemma bR_pos (h : Sys b K C F) : (0 : ℝ) < (b : ℝ) := by
  have := h.bpos; exact_mod_cast this

/-- Total mass is conserved. -/
lemma sum_eq_one (h : Sys b K C F) (m : ℕ) : ∑ k ∈ Finset.range (b ^ m), F m k = 1 := by
  induction m with
  | zero => simpa using h.unit
  | succ m ih =>
      have hpow : b ^ (m + 1) = b ^ m * b := by ring
      rw [hpow, sum_range_mul' (fun k => F (m + 1) k) (b ^ m) b, ← ih]
      exact Finset.sum_congr rfl fun k _ => (h.right m k).symm

lemma A_zero (h : Sys b K C F) : A b F 0 = 1 := by
  rw [A]
  simp [h.unit]

lemma A_nonneg (h : Sys b K C F) (m : ℕ) : 0 ≤ A b F m := by
  refine Finset.sum_nonneg fun k _ => ?_
  have := h.bR_pos
  positivity

lemma A_le (h : Sys b K C F) (m : ℕ) : A b F m ≤ C := by
  have hb := h.bR_pos
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  have hstep : ∀ k ∈ Finset.range (b ^ m), (b : ℝ) ^ m * (F m k) ^ 2 ≤ C * F m k := by
    intro k _
    have h1 := h.nonneg m k
    have h2 := h.bdd m k
    have h3 : (b : ℝ) ^ m * F m k ≤ C := by
      rw [le_div_iff₀ hbm] at h2
      linarith [h2]
    nlinarith
  calc A b F m ≤ ∑ k ∈ Finset.range (b ^ m), C * F m k := Finset.sum_le_sum hstep
    _ = C * ∑ k ∈ Finset.range (b ^ m), F m k := by rw [Finset.mul_sum]
    _ = C := by rw [h.sum_eq_one m]; ring

lemma Var_nonneg (h : Sys b K C F) (m : ℕ) : 0 ≤ Var b F m := by
  refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun s _ => ?_
  have := h.bR_pos
  positivity

/-- **The energy increment.**  `A (m+1) = A m + Var m`: Cauchy–Schwarz on the `right` relation,
in its exact (Pythagorean) form. -/
lemma A_succ (h : Sys b K C F) (m : ℕ) : A b F (m + 1) = A b F m + Var b F m := by
  have hb := h.bR_pos
  have hpow : b ^ (m + 1) = b ^ m * b := by ring
  have hA1 : A b F (m + 1)
      = ∑ k ∈ Finset.range (b ^ m), ∑ s ∈ Finset.range b,
          (b : ℝ) ^ (m + 1) * (F (m + 1) (k * b + s)) ^ 2 := by
    rw [A, hpow, sum_range_mul' (fun k' => (b : ℝ) ^ (m + 1) * (F (m + 1) k') ^ 2) (b ^ m) b]
  rw [hA1, A, Var, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  set g : ℝ := F m k with hg
  have hsum : ∑ s ∈ Finset.range b, F (m + 1) (k * b + s) = g := (h.right m k).symm
  have hkey : ∑ s ∈ Finset.range b, (F (m + 1) (k * b + s) - g / (b : ℝ)) ^ 2
      = (∑ s ∈ Finset.range b, (F (m + 1) (k * b + s)) ^ 2) - g ^ 2 / (b : ℝ) := by
    have hexp : ∀ s, (F (m + 1) (k * b + s) - g / (b : ℝ)) ^ 2
        = (F (m + 1) (k * b + s)) ^ 2 - 2 * (g / (b : ℝ)) * F (m + 1) (k * b + s)
          + (g / (b : ℝ)) ^ 2 := by
      intro s; ring
    simp only [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    ring
  have hVar : ∑ s ∈ Finset.range b, (b : ℝ) ^ (m + 1) * (D b F m k s) ^ 2
      = (b : ℝ) ^ (m + 1) * ((∑ s ∈ Finset.range b, (F (m + 1) (k * b + s)) ^ 2)
          - g ^ 2 / (b : ℝ)) := by
    simp only [D]
    rw [← Finset.mul_sum, ← hkey]
  rw [hVar, ← Finset.mul_sum]
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb
  field_simp
  ring

/-- **The `shift` relation pushes defects down.** -/
lemma D_shift (h : Sys b K C F) (m k s : ℕ) :
    D b F m k s = ∑ t ∈ Finset.range (b ^ K), D b F (m + K) (t * b ^ m + k) s := by
  have hb := h.bR_pos
  have h1 : F (m + 1) (k * b + s)
      = ∑ t ∈ Finset.range (b ^ K), F (m + 1 + K) (t * b ^ (m + 1) + (k * b + s)) :=
    h.shift (m + 1) (k * b + s)
  have h2 : F m k = ∑ t ∈ Finset.range (b ^ K), F (m + K) (t * b ^ m + k) := h.shift m k
  have hterm : ∀ t : ℕ, D b F (m + K) (t * b ^ m + k) s
      = F (m + 1 + K) (t * b ^ (m + 1) + (k * b + s))
        - F (m + K) (t * b ^ m + k) * (b : ℝ)⁻¹ := by
    intro t
    rw [D, div_eq_mul_inv]
    have harg : (t * b ^ m + k) * b + s = t * b ^ (m + 1) + (k * b + s) := by ring
    have hlev : m + K + 1 = m + 1 + K := by omega
    rw [harg, hlev]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_sub_distrib, ← Finset.sum_mul,
    D, div_eq_mul_inv, h1, h2]

/-- **The increments are nondecreasing along each class mod `K`.** -/
lemma Var_le_shift (h : Sys b K C F) (m : ℕ) : Var b F m ≤ Var b F (m + K) := by
  have hb := h.bR_pos
  have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  have hpw : (b : ℝ) ^ (m + 1) * (b : ℝ) ^ K = (b : ℝ) ^ (m + K + 1) := by
    rw [← pow_add]; congr 1; omega
  have hcs : ∀ k s : ℕ, (D b F m k s) ^ 2
      ≤ ((b : ℝ) ^ K) * ∑ t ∈ Finset.range (b ^ K), (D b F (m + K) (t * b ^ m + k) s) ^ 2 := by
    intro k s
    have hch := sq_sum_le_card_mul_sum_sq (s := Finset.range (b ^ K))
      (f := fun t => D b F (m + K) (t * b ^ m + k) s)
    rw [Finset.card_range] at hch
    rw [h.D_shift m k s]
    have hcast : (((b ^ K : ℕ) : ℝ)) = (b : ℝ) ^ K := by push_cast; ring
    rwa [hcast] at hch
  have hstep : Var b F m
      ≤ ∑ k ∈ Finset.range (b ^ m), ∑ s ∈ Finset.range b, ∑ t ∈ Finset.range (b ^ K),
          (b : ℝ) ^ (m + K + 1) * (D b F (m + K) (t * b ^ m + k) s) ^ 2 := by
    rw [Var]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun s _ => ?_
    have hb1 : (0 : ℝ) ≤ (b : ℝ) ^ (m + 1) := by positivity
    calc (b : ℝ) ^ (m + 1) * (D b F m k s) ^ 2
        ≤ (b : ℝ) ^ (m + 1)
            * ((b : ℝ) ^ K * ∑ t ∈ Finset.range (b ^ K),
                (D b F (m + K) (t * b ^ m + k) s) ^ 2) :=
          mul_le_mul_of_nonneg_left (hcs k s) hb1
      _ = ∑ t ∈ Finset.range (b ^ K),
            (b : ℝ) ^ (m + K + 1) * (D b F (m + K) (t * b ^ m + k) s) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← mul_assoc, hpw]
  refine hstep.trans (le_of_eq ?_)
  rw [Var]
  have hpow : b ^ (m + K) = b ^ K * b ^ m := by rw [← pow_add]; congr 1; omega
  rw [hpow, sum_range_mul' (fun k' => ∑ s ∈ Finset.range b,
    (b : ℝ) ^ (m + K + 1) * (D b F (m + K) k' s) ^ 2) (b ^ K) (b ^ m)]
  have hswap : ∀ k : ℕ, ∑ s ∈ Finset.range b, ∑ t ∈ Finset.range (b ^ K),
      (b : ℝ) ^ (m + K + 1) * (D b F (m + K) (t * b ^ m + k) s) ^ 2
      = ∑ t ∈ Finset.range (b ^ K), ∑ s ∈ Finset.range b,
        (b : ℝ) ^ (m + K + 1) * (D b F (m + K) (t * b ^ m + k) s) ^ 2 :=
    fun k => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun k _ => hswap k), Finset.sum_comm]

/-- The increments telescope into the energy. -/
lemma sum_Var (h : Sys b K C F) (m J : ℕ) :
    ∑ j ∈ Finset.range J, Var b F (m + j) = A b F (m + J) - A b F m := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have := h.A_succ (m + J)
      have harg : m + (J + 1) = m + J + 1 := by omega
      rw [harg, this]
      ring

/-- **Every increment vanishes.** -/
theorem Var_eq_zero (h : Sys b K C F) (m : ℕ) : Var b F m = 0 := by
  by_contra hne
  have hpos : 0 < Var b F m := lt_of_le_of_ne (h.Var_nonneg m) (Ne.symm hne)
  -- `Var` is ≥ `Var m` at every level `m + j*K`
  have hmono : ∀ j : ℕ, Var b F m ≤ Var b F (m + j * K) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        refine ih.trans ?_
        have := h.Var_le_shift (m + j * K)
        have harg : m + j * K + K = m + (j + 1) * K := by ring
        rwa [harg] at this
  -- but they are summable
  obtain ⟨J, hJ⟩ := exists_nat_gt ((C - A b F m) / Var b F m)
  have hsum : ∑ j ∈ Finset.range J, Var b F (m + j * K) ≤ A b F (m + J * K) - A b F m := by
    have hsub : (Finset.range J).image (fun j => j * K) ⊆ Finset.range (J * K) := by
      intro y hy
      simp only [Finset.mem_image, Finset.mem_range] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      have := h.Kpos
      simp only [Finset.mem_range]
      exact Nat.mul_lt_mul_of_lt_of_le hj (le_refl K) this
    calc ∑ j ∈ Finset.range J, Var b F (m + j * K)
        = ∑ y ∈ (Finset.range J).image (fun j => j * K), Var b F (m + y) := by
          rw [Finset.sum_image]
          intro i _ j _ hij
          have := h.Kpos
          exact Nat.eq_of_mul_eq_mul_right this hij
      _ ≤ ∑ y ∈ Finset.range (J * K), Var b F (m + y) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => h.Var_nonneg _)
      _ = A b F (m + J * K) - A b F m := h.sum_Var m (J * K)
  have hJv : (J : ℝ) * Var b F m ≤ ∑ j ∈ Finset.range J, Var b F (m + j * K) := by
    have : ∑ j ∈ Finset.range J, Var b F m ≤ ∑ j ∈ Finset.range J, Var b F (m + j * K) :=
      Finset.sum_le_sum fun j _ => hmono j
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hCle : A b F (m + J * K) ≤ C := h.A_le _
  have : (J : ℝ) * Var b F m ≤ C - A b F m := by linarith
  rw [div_lt_iff₀ hpos] at hJ
  linarith

/-- The energy never moves. -/
theorem A_eq_one (h : Sys b K C F) (m : ℕ) : A b F m = 1 := by
  induction m with
  | zero => exact h.A_zero
  | succ m ih => rw [h.A_succ m, ih, h.Var_eq_zero m]; ring

/-- 🎯 **Block rigidity.**  A shift-invariant density system dominated by the uniform one *is*
the uniform one. -/
theorem eq_uniform (h : Sys b K C F) (m k : ℕ) (hk : k < b ^ m) :
    F m k = 1 / (b : ℝ) ^ m := by
  have hb := h.bR_pos
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  have hcard : ((Finset.range (b ^ m)).card : ℝ) = (b : ℝ) ^ m := by
    rw [Finset.card_range]; push_cast; ring
  have hzero : ∑ k' ∈ Finset.range (b ^ m), (F m k' - 1 / (b : ℝ) ^ m) ^ 2 = 0 := by
    have hexp : ∀ k', (F m k' - 1 / (b : ℝ) ^ m) ^ 2
        = (F m k') ^ 2 - 2 * (1 / (b : ℝ) ^ m) * F m k' + (1 / (b : ℝ) ^ m) ^ 2 := by
      intro k'; ring
    simp only [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h.sum_eq_one m,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hA := h.A_eq_one m
    have hsq : ∑ k' ∈ Finset.range (b ^ m), (F m k') ^ 2 = 1 / (b : ℝ) ^ m := by
      have h2 : (b : ℝ) ^ m * ∑ k' ∈ Finset.range (b ^ m), (F m k') ^ 2 = 1 := by
        rw [Finset.mul_sum]
        rw [A] at hA
        exact hA
      field_simp at h2 ⊢
      linarith
    rw [hsq]
    push_cast
    field_simp
    ring
  have hterm : ∀ k' ∈ Finset.range (b ^ m), (F m k' - 1 / (b : ℝ) ^ m) ^ 2 = 0 := by
    intro k' hk'
    by_contra hcon
    have hpos : 0 < (F m k' - 1 / (b : ℝ) ^ m) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hcon)
    have hle : (0 : ℝ) < ∑ k'' ∈ Finset.range (b ^ m), (F m k'' - 1 / (b : ℝ) ^ m) ^ 2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨k', hk', hpos⟩
    linarith
  have := hterm k (Finset.mem_range.2 hk)
  have hsq0 : F m k - 1 / (b : ℝ) ^ m = 0 := by
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

end Sys

end NormalNumbers.BlockRigidity
