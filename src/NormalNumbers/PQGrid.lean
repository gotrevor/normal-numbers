/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitOmegaK

/-!
# Exact natural-number arithmetic for the `P`/`Q` approximation

Primitive recursive helpers for `ExplicitPQ`: evaluation of an integer coefficient list at a dyadic
`N / 2^T` as a difference of two naturals (`evP`, `evM`), and a monotone grid count (`gcount`).
-/

open Polynomial

namespace NormalNumbers.PQGrid

open ExplicitOmegaK OmegaKApprox

/-- Positive part of `2^{T·len} · l(N/2^T)`. -/
def evP (l : List ℤ) (N T : ℕ) : ℕ :=
  rsum l.length fun j => (l.getD j 0).toNat * N ^ j * 2 ^ (T * (l.length - j))

/-- Negative part of `2^{T·len} · l(N/2^T)`. -/
def evM (l : List ℤ) (N T : ℕ) : ℕ :=
  rsum l.length fun j => (-l.getD j 0).toNat * N ^ j * 2 ^ (T * (l.length - j))

theorem evP_sub_evM (l : List ℤ) (N T : ℕ) :
    (evP l N T : ℝ) - evM l N T = 2 ^ (T * l.length) * aeval ((N : ℝ) / 2 ^ T) (polyOfList l) := by
  rw [evP, evM, rsum_eq, rsum_eq, aeval_polyOfList]; push_cast
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h := congrArg (Int.cast (R := ℝ)) (Int.toNat_sub_toNat_neg (l.getD j 0))
  push_cast at h
  have e : (2 : ℝ) ^ (T * l.length) = 2 ^ (T * (l.length - j)) * 2 ^ (T * j) := by
    rw [← pow_add]; congr 1; rw [← mul_add, Nat.sub_add_cancel hj.le]
  rw [e, div_pow, ← pow_mul, ← h]
  field_simp

theorem primrec_evPM (f : ℤ → ℕ) (hf : Primrec f) :
    Primrec fun x : List ℤ × ℕ × ℕ => rsum x.1.length fun j =>
      f (x.1.getD j 0) * x.2.1 ^ j * 2 ^ (x.2.2 * (x.1.length - j)) := by
  refine primrec_rsum (Primrec.list_length.comp Primrec.fst) ?_
  exact (Primrec.nat_mul.comp (Primrec.nat_mul.comp
    (hf.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
    (ComputableNormal.primrec_pow.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      Primrec.snd))
    (ComputableNormal.primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)))).to₂

theorem primrec_evP : Primrec fun x : List ℤ × ℕ × ℕ => evP x.1 x.2.1 x.2.2 :=
  primrec_evPM _ primrec_toNat

theorem primrec_evM : Primrec fun x : List ℤ × ℕ × ℕ => evM x.1 x.2.1 x.2.2 :=
  primrec_evPM _ primrec_negPart

/-- Number of `j ∈ [1, n]` passing a test. -/
def gcount (C : ℕ → Prop) [DecidablePred C] (n : ℕ) : ℕ := rsum n fun j => if C (j + 1) then 1 else 0

/-- **Monotone grid count = clamped floor.**  If `C j ↔ j ≤ z` (with `z ≥ 0`) then the count over
`[1, n]` is `min n ⌊z⌋`. -/
theorem gcount_eq (C : ℕ → Prop) [DecidablePred C] {z : ℝ} (hz : 0 ≤ z)
    (hC : ∀ j, C j ↔ (j : ℝ) ≤ z) (n : ℕ) : gcount C n = min n ⌊z⌋₊ := by
  induction n with
  | zero => simp [gcount, rsum]
  | succ n ih =>
    have : gcount C (n + 1) = gcount C n + if C (n + 1) then 1 else 0 := by
      simp only [gcount, rsum_eq, Finset.sum_range_succ]
    rw [this, ih]
    by_cases h : C (n + 1)
    · rw [if_pos h]
      have : n + 1 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast (hC _).1 h)
      omega
    · rw [if_neg h]
      have : ⌊z⌋₊ ≤ n := by
        have h' : z < ((n + 1 : ℕ) : ℝ) := by
          by_contra hc; push Not at hc; exact h ((hC _).2 hc)
        have := Nat.floor_lt hz |>.2 h'
        omega
      omega

theorem primrec_gcount {α : Type*} [Primcodable α] (C : α → ℕ → Prop) [∀ a, DecidablePred (C a)]
    (hC : PrimrecRel C) {f : α → ℕ} (hf : Primrec f) :
    Primrec fun a => gcount (C a) (f a) :=
  primrec_rsum hf (Primrec.ite (hC.comp Primrec.fst (Primrec.succ.comp Primrec.snd))
    (Primrec.const 1) (Primrec.const 0)).to₂

/-! ### Integers as pairs of naturals -/

/-- `(a.1 − a.2) − (b.1 − b.2)` as a pair. -/
def psub (a b : ℕ × ℕ) : ℕ × ℕ := (a.1 + b.2, a.2 + b.1)

/-- `(a)(b) = (c)(d)` for pair-integers. -/
def pmulEq (a b c d : ℕ × ℕ) : Prop :=
  a.1 * b.1 + a.2 * b.2 + c.1 * d.2 + c.2 * d.1 = a.1 * b.2 + a.2 * b.1 + c.1 * d.1 + c.2 * d.2

instance (a b c d : ℕ × ℕ) : Decidable (pmulEq a b c d) := by unfold pmulEq; infer_instance

/-- Real value of a pair. -/
def pval (a : ℕ × ℕ) : ℝ := (a.1 : ℝ) - a.2

theorem pval_psub (a b : ℕ × ℕ) : pval (psub a b) = pval a - pval b := by
  simp only [pval, psub]; push_cast; ring

theorem pmulEq_iff (a b c d : ℕ × ℕ) :
    pmulEq a b c d ↔ pval a * pval b = pval c * pval d := by
  unfold pmulEq pval
  constructor
  · intro h
    have h' : ((a.1 * b.1 + a.2 * b.2 + c.1 * d.2 + c.2 * d.1 : ℕ) : ℝ) =
        ((a.1 * b.2 + a.2 * b.1 + c.1 * d.1 + c.2 * d.2 : ℕ) : ℝ) := by rw [h]
    push_cast at h'; linarith
  · intro h
    have : ((a.1 * b.1 + a.2 * b.2 + c.1 * d.2 + c.2 * d.1 : ℕ) : ℝ) =
        ((a.1 * b.2 + a.2 * b.1 + c.1 * d.1 + c.2 * d.2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

theorem primrec_psub : Primrec₂ psub :=
  (Primrec.pair (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))).to₂

theorem primrec_pmulEq : PrimrecPred fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) =>
    pmulEq x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  unfold pmulEq
  have a1 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 :=
    Primrec.fst.comp Primrec.fst
  have a2 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.1.2 :=
    Primrec.snd.comp Primrec.fst
  have b1 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have b2 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have c1 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.2.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have c2 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.2.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have d1 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have d2 : Primrec fun x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) => x.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have m := fun {f g : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) → ℕ} (hf : Primrec f) (hg : Primrec g) =>
    Primrec.nat_mul.comp hf hg
  have ad := fun {f g : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) → ℕ} (hf : Primrec f) (hg : Primrec g) =>
    Primrec.nat_add.comp hf hg
  exact Primrec.eq.comp (ad (ad (ad (m a1 b1) (m a2 b2)) (m c1 d2)) (m c2 d1))
    (ad (ad (ad (m a1 b2) (m a2 b1)) (m c1 d1)) (m c2 d2))

/-- Value of a coefficient list at a natural point, as a pair. -/
def evN (l : List ℤ) (m : ℕ) : ℕ × ℕ := (evP l m 0, evM l m 0)

theorem pval_evN (l : List ℤ) (m : ℕ) : pval (evN l m) = aeval (m : ℝ) (polyOfList l) := by
  have := evP_sub_evM l m 0
  simp only [zero_mul, pow_zero, div_one, one_mul] at this
  exact this

theorem primrec_evN : Primrec₂ evN :=
  (Primrec.pair (primrec_evP.comp (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd
    (Primrec.const 0)))) (primrec_evM.comp (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd
    (Primrec.const 0))))).to₂

/-- The affine-dependence test at the point `m` (base points `k₀`, `k₁`):
`(P(m) − P(k₀))(Q(k₁) − Q(k₀)) = (P(k₁) − P(k₀))(Q(m) − Q(k₀))`. -/
def affTest (lQ : List ℤ) (k₀ k₁ : ℕ) (l : List ℤ) (m : ℕ) : Prop :=
  pmulEq (psub (evN l m) (evN l k₀)) (psub (evN lQ k₁) (evN lQ k₀))
    (psub (evN l k₁) (evN l k₀)) (psub (evN lQ m) (evN lQ k₀))

instance (lQ : List ℤ) (k₀ k₁ : ℕ) (l : List ℤ) : DecidablePred (affTest lQ k₀ k₁ l) :=
  fun m => by unfold affTest; infer_instance

theorem primrec_affTest (lQ : List ℤ) (k₀ k₁ : ℕ) :
    PrimrecRel (affTest lQ k₀ k₁) := by
  have e : Primrec₂ fun (l : List ℤ) (m : ℕ) => evN l m := primrec_evN
  have eQ : Primrec fun m : ℕ => evN lQ m := e.comp (Primrec.const lQ) Primrec.id
  have s := primrec_psub
  have h1 : Primrec₂ fun (l : List ℤ) (m : ℕ) => psub (evN l m) (evN l k₀) :=
    (s.comp e (e.comp Primrec.fst (Primrec.const k₀))).to₂
  have h2 : Primrec₂ fun (_ : List ℤ) (_ : ℕ) => psub (evN lQ k₁) (evN lQ k₀) :=
    (Primrec.const _).to₂
  have h3 : Primrec₂ fun (l : List ℤ) (_ : ℕ) => psub (evN l k₁) (evN l k₀) :=
    (s.comp (e.comp Primrec.fst (Primrec.const k₁)) (e.comp Primrec.fst (Primrec.const k₀))).to₂
  have h4 : Primrec₂ fun (_ : List ℤ) (m : ℕ) => psub (evN lQ m) (evN lQ k₀) :=
    (s.comp (eQ.comp Primrec.snd) (Primrec.const _)).to₂
  exact primrec_pmulEq.comp (Primrec.pair h1 (Primrec.pair h2 (Primrec.pair h3 h4)))

/-- Number of failing points among `m < n`. -/
def affFail (lQ : List ℤ) (k₀ k₁ : ℕ) (l : List ℤ) (n : ℕ) : ℕ :=
  rsum n fun m => if affTest lQ k₀ k₁ l m then 0 else 1

theorem affFail_eq_zero_iff (lQ : List ℤ) (k₀ k₁ : ℕ) (l : List ℤ) (n : ℕ) :
    affFail lQ k₀ k₁ l n = 0 ↔ ∀ m < n, affTest lQ k₀ k₁ l m := by
  rw [affFail, rsum_eq, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_range, ite_eq_left_iff, one_ne_zero, imp_false, not_not]

theorem primrec_affFail (lQ : List ℤ) (k₀ k₁ : ℕ) {n : List ℤ → ℕ} (hn : Primrec n) :
    Primrec fun l => affFail lQ k₀ k₁ l (n l) :=
  primrec_rsum hn (Primrec.ite ((primrec_affTest lQ k₀ k₁).comp Primrec.fst Primrec.snd)
    (Primrec.const 0) (Primrec.const 1)).to₂

end NormalNumbers.PQGrid
