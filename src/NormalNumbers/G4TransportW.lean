/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Transport
import NormalNumbers.G4SubsetWeight

/-!
# §4A transport for a general additive weight (`TWeight`)

`G4Transport` proves the exact affine Lambert transport identity for the weight `ω` and the
constant `G_b = ∑ ω(n)/bⁿ`.  Campaign A needs the same identity for the *prime-subset* weight
`ω_S`, and campaign G5 needs it for `w_c = ω + excess c`.  Every step of §4A uses only four
properties of the weight, so this module isolates them into a structure `TWeight` and re-proves
§4A once, generically:

* `wN : ℕ → ℕ` — the weight is integer valued (so `bᵏ·x` is an integer plus a tail);
* `ov : ℕ → ℕ → ℕ` with `wN (d*m) + ov d m = wN m + wN d` (`d, m ≠ 0`) — the exact affine
  transport identity;
* `ov d m ≤ ω(d)` and `ov d m = ov d m'` when `m ≡ m'` modulo every prime of `d` — so the
  correction is bounded and periodic;
* summability of `wN n / bⁿ` at every base `b ≥ 2`.

Instances: `TWeight.omega` (`ω`, `TWeight.lambert_omega`) and `TWeight.subset S` (`ω_S`,
`TWeight.lambert_subset`).  The output is `Frame.propA_of_progressionW`, the weight-generic
form of `Frame.propA_of_progression`; the latter is recovered by `TWeight.omega`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-- The interface of §4A: an integer-valued additive weight with an exact transport identity
whose correction is bounded by `ω(d)` and periodic modulo `rad d`. -/
structure TWeight where
  /-- the weight, integer valued -/
  wN : ℕ → ℕ
  /-- the transport correction `overlap` -/
  ov : ℕ → ℕ → ℕ
  /-- exact transport: `w(dm) + ov(d,m) = w(m) + w(d)` -/
  mul_eq : ∀ d m : ℕ, d ≠ 0 → m ≠ 0 → wN (d * m) + ov d m = wN m + wN d
  /-- the correction is bounded by the number of prime factors of `d` -/
  ov_le : ∀ d m : ℕ, ov d m ≤ d.primeFactors.card
  /-- the correction is periodic in `m` modulo every prime of `d` -/
  ov_congr : ∀ d m m' : ℕ, (∀ p ∈ d.primeFactors, m ≡ m' [MOD p]) → ov d m = ov d m'
  /-- the Lambert series converges at every base `b ≥ 2` -/
  summable : ∀ b : ℕ, 2 ≤ b → Summable (fun n : ℕ => (wN n : ℝ) / (b : ℝ) ^ n)

namespace TWeight

variable (W : TWeight) {b : ℕ}

/-- The constant under test, `x_W(b) = ∑_n w(n)/bⁿ`. -/
noncomputable def lambert (W : TWeight) (b : ℕ) : ℝ := ∑' n : ℕ, (W.wN n : ℝ) / (b : ℝ) ^ n

/-- `T_b(k) = ∑_{j ≥ 1} w(k + j) b^{-j}`. -/
noncomputable def tailB (W : TWeight) (b k : ℕ) : ℝ :=
  ∑' i : ℕ, (W.wN (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

/-- The integer `∑_{m ≤ k} b^{k-m} w(m)`. -/
def tailIntB (W : TWeight) (b k : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (k + 1), b ^ (k - m) * W.wN m

lemma summable_tailB (hb : 2 ≤ b) (k : ℕ) :
    Summable (fun i : ℕ => (W.wN (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    positivity
  have := ((summable_nat_add_iff (k + 1)).mpr (W.summable b hb)).mul_left ((b : ℝ) ^ k)
  refine this.congr (fun i => ?_)
  rw [show i + (k + 1) = k + i + 1 by ring, pow_add, pow_add]
  field_simp
  ring

/-- `T_b(k) = b^k · x_W − (integer)`. -/
theorem tailB_eq (hb : 2 ≤ b) (k : ℕ) :
    W.tailB b k = (b : ℝ) ^ k * W.lambert b - W.tailIntB b k := by
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    positivity
  have hs : Summable (fun n : ℕ => (b : ℝ) ^ k * ((W.wN n : ℝ) / (b : ℝ) ^ n)) :=
    (W.summable b hb).mul_left _
  have h := hs.sum_add_tsum_nat_add (k + 1)
  have hfin : ∑ i ∈ Finset.range (k + 1), (b : ℝ) ^ k * ((W.wN i : ℝ) / (b : ℝ) ^ i)
      = W.tailIntB b k := by
    rw [tailIntB]; push_cast
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [pow_sub₀ (b : ℝ) hb0 hm']
    field_simp
  have htail : ∑' i : ℕ, (b : ℝ) ^ k * ((W.wN (i + (k + 1)) : ℝ) / (b : ℝ) ^ (i + (k + 1)))
      = W.tailB b k := by
    rw [tailB]
    refine tsum_congr (fun i => ?_)
    rw [show i + (k + 1) = k + i + 1 by ring, pow_add, pow_add]
    field_simp
    ring
  rw [lambert, ← tsum_mul_left, ← h, hfin, htail]
  ring

/-- `E_{d,b}(k) = ∑_{j ≥ 1} b^{-j} ov(d, k + j)`. -/
noncomputable def corrB (W : TWeight) (b d k : ℕ) : ℝ :=
  ∑' i : ℕ, (W.ov d (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

lemma summable_corrB (hb : 2 ≤ b) (d k : ℕ) :
    Summable (fun i : ℕ => (W.ov d (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_inv_pow_succ hb).mul_left (d.primeFactors.card : ℝ))
  rw [← mul_div_assoc, mul_one]
  gcongr
  exact_mod_cast W.ov_le d _

/-- The dilated tail `∑_{j ≥ 1} b^{-j} w(d(k + j))`. -/
noncomputable def dilatedTailB (W : TWeight) (b d k : ℕ) : ℝ :=
  ∑' i : ℕ, (W.wN (d * (k + i + 1)) : ℝ) / (b : ℝ) ^ (i + 1)

lemma dilatedTailB_term (d k : ℕ) (hd : d ≠ 0) (i : ℕ) :
    (W.wN (d * (k + i + 1)) : ℝ) / (b : ℝ) ^ (i + 1) =
      (W.wN (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) + (W.wN d : ℝ) * (1 / (b : ℝ) ^ (i + 1))
        - (W.ov d (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
  have h := W.mul_eq d (k + i + 1) hd (by omega)
  have h' : (W.wN (d * (k + i + 1)) : ℝ)
      = (W.wN (k + i + 1) : ℝ) + (W.wN d : ℝ) - (W.ov d (k + i + 1) : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at this
    linarith
  rw [h']
  ring

/-- **Exact transport in base `b`** for a `TWeight`. -/
theorem dilatedTailB_eq (hb : 2 ≤ b) (d k : ℕ) (hd : d ≠ 0) :
    W.dilatedTailB b d k = W.tailB b k + (W.wN d : ℝ) / ((b : ℝ) - 1) - W.corrB b d k := by
  rw [dilatedTailB, tsum_congr (W.dilatedTailB_term (b := b) d k hd), Summable.tsum_sub,
    Summable.tsum_add, tsum_mul_left, tsum_inv_pow_succ hb, tailB, corrB, mul_one_div]
  · exact W.summable_tailB hb k
  · exact (summable_inv_pow_succ hb).mul_left _
  · exact (W.summable_tailB hb k).add ((summable_inv_pow_succ hb).mul_left _)
  · exact W.summable_corrB hb d k

/-- **Periodicity of the correction**. -/
theorem corrB_congr (d k k' : ℕ) (h : ∀ p ∈ d.primeFactors, k ≡ k' [MOD p]) :
    W.corrB b d k = W.corrB b d k' := by
  unfold corrB
  refine tsum_congr (fun i => ?_)
  rw [W.ov_congr d (k + i + 1) (k' + i + 1) (fun p hp => ((h p hp).add_right i).add_right 1)]

/-- The tail equals the orbit point of `x_W` modulo one. -/
lemma coe_tailB (hb : 2 ≤ b) (k : ℕ) :
    ((W.tailB b k : ℝ) : UnitAddCircle)
      = ((orbit b (W.lambert b) k : ℝ) : UnitAddCircle) := by
  rw [W.tailB_eq hb k, QuotientAddGroup.mk_sub, coe_pow_mul_eq_coe_orbit]
  have : ((W.tailIntB b k : ℝ) : UnitAddCircle) = 0 := by
    have := coe_int_eq_zero (W.tailIntB b k : ℤ)
    push_cast at this
    exact this
  rw [this, sub_zero]

/-! ### Instances -/

/-- The weight `ω`. -/
def omega : TWeight where
  wN := fun m => ArithmeticFunction.cardDistinctFactors m
  ov := overlap
  mul_eq := fun d m hd hm => omega_mul_eq d m hd hm
  ov_le := overlap_le
  ov_congr := fun d m m' h => overlap_congr d m m' h
  summable := fun b hb => (summable_omegaR_div_pow hb).congr (fun n => by rw [omegaR])

@[simp] lemma omega_wN (m : ℕ) : (omega.wN m : ℝ) = omegaR m := by rw [omegaR]; rfl

lemma lambert_omega (hb : 2 ≤ b) : omega.lambert b = primeLambertAtBase b := by
  unfold lambert primeLambertAtBase
  exact tsum_congr fun n => by rw [omega_wN]

/-- The prime-subset weight `ω_S`. -/
def subset (S : ℕ → Prop) [DecidablePred S] : TWeight where
  wN := omegaSN S
  ov := overlapS S
  mul_eq := fun d m hd hm => omegaSN_mul_eq (S := S) d m hd hm
  ov_le := fun d m => le_trans (overlapS_le (S := S) d m) (overlap_le d m)
  ov_congr := fun d m m' h => overlapS_congr (S := S) d m m' h
  summable := fun b hb => (summable_omegaS_div_pow (S := S) hb).congr (fun n => by rw [omegaS])

@[simp] lemma subset_wN (S : ℕ → Prop) [DecidablePred S] (m : ℕ) :
    ((subset S).wN m : ℝ) = omegaS S m := by rw [omegaS]; rfl

lemma lambert_subset (S : ℕ → Prop) [DecidablePred S] :
    (subset S).lambert b = subsetLambert S b := by
  unfold lambert subsetLambert
  exact tsum_congr fun n => by rw [subset_wN]

end TWeight

/-! ### `PropA` for a frame carrying a general weight -/

namespace Frame

variable (fr : Frame) (W : TWeight)

/-- The inner tail of `Ffull` at atom `α`, for a general weight. -/
lemma tsum_eq_dilatedTailBW (α : Fin fr.H) (k : ℕ) :
    ∑' j : ℕ, (W.wN (fr.t α + fr.d α * k + fr.shift α (j + 1)) : ℝ) / (fr.bse : ℝ) ^ (j + 1)
      = W.dilatedTailB fr.bse (fr.d α) k := by
  unfold TWeight.dilatedTailB
  refine tsum_congr fun j => ?_
  rw [fr.add_shift_eq α k j]

/-- The transport translate for a general weight. -/
noncomputable def transportThetaW (c : Fin fr.H → ℕ) : Torus fr.r :=
  fun ν => (((∑ α, (fr.A ν α : ℝ)
      * ((W.wN (fr.d α) : ℝ) / ((fr.bse : ℝ) - 1) - W.corrB fr.bse (fr.d α) (c α)) : ℝ) :
    UnitAddCircle))

/-- The exact transported vector on the progression, before subtracting `γ`. -/
lemma coe_sum_dilatedTailBW (c k : Fin fr.H → ℕ) (hd : ∀ α, fr.d α ≠ 0)
    (hk : ∀ α, ∀ p ∈ (fr.d α).primeFactors, k α ≡ c α [MOD p]) (ν : Fin fr.r) :
    ((∑ α, (fr.A ν α : ℝ) * W.dilatedTailB fr.bse (fr.d α) (k α) : ℝ) : UnitAddCircle)
      = mulVecT fr.A
          (fun α => ((orbit fr.bse (W.lambert fr.bse) (k α) : ℝ) : UnitAddCircle)) ν
        + fr.transportThetaW W c ν := by
  have hterm : ∀ α, (fr.A ν α : ℝ) * W.dilatedTailB fr.bse (fr.d α) (k α)
      = (fr.A ν α : ℝ) * W.tailB fr.bse (k α)
        + (fr.A ν α : ℝ)
            * ((W.wN (fr.d α) : ℝ) / ((fr.bse : ℝ) - 1)
              - W.corrB fr.bse (fr.d α) (c α)) := by
    intro α
    rw [W.dilatedTailB_eq fr.hbse _ _ (hd α), W.corrB_congr (fr.d α) (k α) (c α) (hk α)]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, QuotientAddGroup.mk_add]
  unfold transportThetaW
  congr 1
  unfold mulVecT
  rw [coe_finset_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  show (((fr.A ν α : ℝ) * W.tailB fr.bse (k α) : ℝ) : UnitAddCircle)
    = fr.A ν α • ((orbit fr.bse (W.lambert fr.bse) (k α) : ℝ) : UnitAddCircle)
  rw [← W.coe_tailB fr.hbse, ← zsmul_eq_mul, AddCircle.coe_zsmul]

/-- **`PropA` for a frame with frozen multiplier residues, general weight.** -/
theorem propA_of_progressionW (hw : fr.w = fun m => (W.wN m : ℝ))
    (hx : fr.x = W.lambert fr.bse)
    (c : Fin fr.H → ℕ) (hd : ∀ α, fr.d α ≠ 0)
    (hθ : fr.θ = fr.transportThetaW W c)
    (hP : ∀ n ∈ fr.P, ∃ k : Fin fr.H → ℕ, (∀ α, n = fr.t α + fr.d α * k α) ∧
      ∀ α, ∀ p ∈ (fr.d α).primeFactors, k α ≡ c α [MOD p]) :
    fr.PropA := by
  intro n hn
  obtain ⟨k, hnk, hk⟩ := hP n hn
  refine ⟨fun α => ((orbit fr.bse (W.lambert fr.bse) (k α) : ℝ) : UnitAddCircle),
    fun α => by rw [hx]; exact subset_closure (Set.mem_range_self _), ?_⟩
  funext ν
  unfold Ffull
  rw [hw]
  have hsum : (∑ α, (fr.A ν α : ℝ)
        * ∑' j : ℕ, (W.wN (n + fr.shift α (j + 1)) : ℝ) / (fr.bse : ℝ) ^ (j + 1))
      = ∑ α, (fr.A ν α : ℝ) * W.dilatedTailB fr.bse (fr.d α) (k α) :=
    Finset.sum_congr rfl fun α _ => by rw [hnk α, fr.tsum_eq_dilatedTailBW]
  rw [hsum, fr.coe_sum_dilatedTailBW W c k hd hk ν, hθ]
  simp only [Pi.add_apply, Pi.sub_apply]

end Frame

end NormalNumbers.G4
