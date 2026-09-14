/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Wiring
import NormalNumbers.G4TorusProjection

/-!
# G4 disjunctivity, §4A: exact affine Lambert transport in base `b`, and `PropA`

Fixed-base §1 / draft §4, for a general base `b ≥ 2` (the campaign uses `b = 4`).

* `tailB b k = ∑_{j≥1} ω(k+j) b^{−j}` and `tailB_eq`: `tailB b k = b^k G_b − tailIntB b k`, an
  integer translate of the dilate (`tailIntB` is the integer `∑_{m≤k} b^{k−m} ω(m)`).
* `corrB b d k = ∑_{j≥1} b^{−j} · #{p ∣ d : p ∣ k+j}`, periodic in `k` modulo `rad d`
  (`corrB_congr`).
* **`dilatedTailB_eq`** — the exact transport identity
  `∑_{j≥1} b^{−j} ω(d(k+j)) = tailB b k + ω(d)/(b−1) − corrB b d k`.

Then for the wiring's `Frame`: on a progression where every `n` is `t_α + d_α k_α(n)` with
`k_α(n)` frozen modulo `rad d_α`, and with the transport translate
`θ_ν = ∑_α A_{να} (ω(d_α)/3 − E_α)`, the exact transported vector is `A·x(n) + θ − γ` with
`x_α(n) = orbit 4 G₄ (k_α n)` — **`Frame.propA_of_progression`**.  This discharges `PropA`
for any frame whose progression freezes the multiplier residues; building that progression
(draft §3) is the remaining input.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-! ### The base-`b` tail and its integer translate -/

section base

variable {b : ℕ}

lemma summable_inv_pow_succ (hb : 2 ≤ b) : Summable (fun i : ℕ => (1 : ℝ) / (b : ℝ) ^ (i + 1)) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have := (summable_geometric_of_lt_one (r := 1 / (b : ℝ)) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith)).mul_left (1 / (b : ℝ))
  refine this.congr (fun i => ?_)
  rw [pow_succ, one_div_pow]; field_simp

lemma tsum_inv_pow_succ (hb : 2 ≤ b) : ∑' i : ℕ, (1 : ℝ) / (b : ℝ) ^ (i + 1) = 1 / ((b : ℝ) - 1) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h : ∑' i : ℕ, (1 : ℝ) / (b : ℝ) ^ (i + 1) = (1 / (b : ℝ)) * ∑' i : ℕ, (1 / (b : ℝ)) ^ i := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    rw [pow_succ, one_div_pow]; field_simp
  rw [h, tsum_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; linarith)]
  have : (b : ℝ) - 1 ≠ 0 := by linarith
  have : (b : ℝ) ≠ 0 := by linarith
  field_simp

/-- `T_b(k) = ∑_{j ≥ 1} ω(k + j) b^{-j}`, indexed by `j = i + 1`. -/
noncomputable def tailB (b k : ℕ) : ℝ := ∑' i : ℕ, omegaR (k + i + 1) / (b : ℝ) ^ (i + 1)

/-- The integer `∑_{m ≤ k} b^{k-m} ω(m)`. -/
def tailIntB (b k : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (k + 1), b ^ (k - m) * ArithmeticFunction.cardDistinctFactors m

lemma summable_tailB (hb : 2 ≤ b) (k : ℕ) :
    Summable (fun i : ℕ => omegaR (k + i + 1) / (b : ℝ) ^ (i + 1)) := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have := ((summable_nat_add_iff (k + 1)).mpr (summable_omegaR_div_pow hb)).mul_left ((b : ℝ) ^ k)
  refine this.congr (fun i => ?_)
  rw [show i + (k + 1) = k + i + 1 by ring, pow_add, pow_add]
  field_simp
  ring

/-- `T_b(k) = b^k · G_b − (integer)`. -/
theorem tailB_eq (hb : 2 ≤ b) (k : ℕ) :
    tailB b k = (b : ℝ) ^ k * primeLambertAtBase b - tailIntB b k := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hs : Summable (fun n : ℕ => (b : ℝ) ^ k * (omegaR n / (b : ℝ) ^ n)) :=
    (summable_omegaR_div_pow hb).mul_left _
  have h := hs.sum_add_tsum_nat_add (k + 1)
  have hfin : ∑ i ∈ Finset.range (k + 1), (b : ℝ) ^ k * (omegaR i / (b : ℝ) ^ i) = tailIntB b k := by
    rw [tailIntB]; push_cast
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [omegaR, pow_sub₀ (b : ℝ) hb0 hm']
    field_simp
  have htail : ∑' i : ℕ, (b : ℝ) ^ k * (omegaR (i + (k + 1)) / (b : ℝ) ^ (i + (k + 1))) = tailB b k := by
    rw [tailB]
    refine tsum_congr (fun i => ?_)
    rw [show i + (k + 1) = k + i + 1 by ring, pow_add, pow_add]
    field_simp
    ring
  rw [primeLambertAtBase, ← tsum_mul_left, ← h, hfin, htail]
  ring

/-! ### The correction and the exact transport identity -/

/-- `E_{d,b}(k) = ∑_{j ≥ 1} b^{-j} · #{p ∣ d : p ∣ k + j}`. -/
noncomputable def corrB (b d k : ℕ) : ℝ := ∑' i : ℕ, (overlap d (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

lemma summable_corrB (hb : 2 ≤ b) (d k : ℕ) :
    Summable (fun i : ℕ => (overlap d (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_inv_pow_succ hb).mul_left (d.primeFactors.card : ℝ))
  rw [← mul_div_assoc, mul_one]
  gcongr
  exact_mod_cast overlap_le d _

/-- The dilated tail `∑_{j ≥ 1} b^{-j} ω(d(k + j))`. -/
noncomputable def dilatedTailB (b d k : ℕ) : ℝ :=
  ∑' i : ℕ, omegaR (d * (k + i + 1)) / (b : ℝ) ^ (i + 1)

lemma dilatedTailB_term (d k : ℕ) (hd : d ≠ 0) (i : ℕ) :
    omegaR (d * (k + i + 1)) / (b : ℝ) ^ (i + 1) =
      omegaR (k + i + 1) / (b : ℝ) ^ (i + 1) + omegaR d * (1 / (b : ℝ) ^ (i + 1))
        - (overlap d (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
  rw [omegaR_mul_eq d _ hd (by omega)]
  ring

/-- **Exact transport in base `b`**: `∑_{j≥1} b^{-j} ω(d(k+j)) = T_b(k) + ω(d)/(b−1) − E_{d,b}(k)`. -/
theorem dilatedTailB_eq (hb : 2 ≤ b) (d k : ℕ) (hd : d ≠ 0) :
    dilatedTailB b d k = tailB b k + omegaR d / ((b : ℝ) - 1) - corrB b d k := by
  rw [dilatedTailB, tsum_congr (dilatedTailB_term (b := b) d k hd), Summable.tsum_sub,
    Summable.tsum_add, tsum_mul_left, tsum_inv_pow_succ hb, tailB, corrB, mul_one_div]
  · exact summable_tailB hb k
  · exact (summable_inv_pow_succ hb).mul_left _
  · exact (summable_tailB hb k).add ((summable_inv_pow_succ hb).mul_left _)
  · exact summable_corrB hb d k

/-- **Periodicity of the correction**: `E_{d,b}(k) = E_{d,b}(k')` when `k ≡ k'` modulo every
prime dividing `d`. -/
theorem corrB_congr (d k k' : ℕ) (h : ∀ p ∈ d.primeFactors, k ≡ k' [MOD p]) :
    corrB b d k = corrB b d k' := by
  unfold corrB
  refine tsum_congr (fun i => ?_)
  rw [overlap_congr d (k + i + 1) (k' + i + 1) (fun p hp => ((h p hp).add_right i).add_right 1)]

end base

/-! ### Modulo one: the dilate is the orbit point -/

/-- `b^k G_b` and `orbit b G_b k` agree modulo one. -/
lemma coe_pow_mul_eq_coe_orbit (b : ℕ) (x : ℝ) (k : ℕ) :
    (((b : ℝ) ^ k * x : ℝ) : UnitAddCircle) = ((orbit b x k : ℝ) : UnitAddCircle) := by
  unfold orbit
  rw [Int.fract, mul_comm]
  rw [AddCircle.coe_sub, coe_int_eq_zero, sub_zero]

/-- The tail `T_b(k)` equals the orbit point modulo one, in any base `b ≥ 2`. -/
lemma coe_tailB {bb : ℕ} (hb : 2 ≤ bb) (k : ℕ) :
    ((tailB bb k : ℝ) : UnitAddCircle)
      = ((orbit bb (primeLambertAtBase bb) k : ℝ) : UnitAddCircle) := by
  rw [tailB_eq hb k, QuotientAddGroup.mk_sub, coe_pow_mul_eq_coe_orbit]
  have : ((tailIntB bb k : ℝ) : UnitAddCircle) = 0 := by
    have := coe_int_eq_zero (tailIntB bb k : ℤ)
    push_cast at this
    exact this
  rw [this, sub_zero]

/-- The base-four instance. -/
lemma coe_tailB_four (k : ℕ) :
    ((tailB 4 k : ℝ) : UnitAddCircle) = ((orbit 4 primeLambertFour k : ℝ) : UnitAddCircle) :=
  coe_tailB (by norm_num) k

/-! ### `PropA` for a frame whose progression freezes the multiplier residues -/

namespace Frame

variable (fr : Frame)

/-- `n + ρ_{α,j+1} = d_α (k + j + 1)` on `n = t_α + d_α k`. -/
lemma add_shift_eq (α : Fin fr.H) (k j : ℕ) :
    fr.t α + fr.d α * k + fr.shift α (j + 1) = fr.d α * (k + j + 1) := by
  unfold shift
  have h1 : fr.t α ≤ (j + 1) * fr.d α := by
    have := fr.ht α
    nlinarith
  zify [h1]
  ring

/-- The inner tail of `Ffull` at atom `α` is the dilated tail. -/
lemma tsum_eq_dilatedTailB (α : Fin fr.H) (k : ℕ) :
    ∑' j : ℕ, omegaR (fr.t α + fr.d α * k + fr.shift α (j + 1)) / (fr.bse : ℝ) ^ (j + 1)
      = dilatedTailB fr.bse (fr.d α) k := by
  unfold dilatedTailB
  refine tsum_congr fun j => ?_
  rw [fr.add_shift_eq α k j]

/-- The transport translate `θ_ν = ∑_α A_{να} (ω(d_α)/(b−1) − E_{d_α,b}(c_α))` built from frozen
residues `c`. -/
noncomputable def transportTheta (c : Fin fr.H → ℕ) : Torus fr.r :=
  fun ν => (((∑ α, (fr.A ν α : ℝ)
      * (omegaR (fr.d α) / ((fr.bse : ℝ) - 1) - corrB fr.bse (fr.d α) (c α)) : ℝ) :
    UnitAddCircle))

/-- The coercion `ℝ → ℝ/ℤ` commutes with finite sums. -/
lemma coe_finset_sum {ι : Type*} (T : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ T, f i : ℝ) : UnitAddCircle) = ∑ i ∈ T, ((f i : ℝ) : UnitAddCircle) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih => rw [Finset.sum_insert haT, Finset.sum_insert haT, AddCircle.coe_add, ih]

/-- The exact transported vector on the progression, before subtracting `γ`. -/
lemma coe_sum_dilatedTailB (c k : Fin fr.H → ℕ) (hd : ∀ α, fr.d α ≠ 0)
    (hk : ∀ α, ∀ p ∈ (fr.d α).primeFactors, k α ≡ c α [MOD p]) (ν : Fin fr.r) :
    ((∑ α, (fr.A ν α : ℝ) * dilatedTailB fr.bse (fr.d α) (k α) : ℝ) : UnitAddCircle)
      = mulVecT fr.A
          (fun α => ((orbit fr.bse (primeLambertAtBase fr.bse) (k α) : ℝ) : UnitAddCircle)) ν
        + fr.transportTheta c ν := by
  have hterm : ∀ α, (fr.A ν α : ℝ) * dilatedTailB fr.bse (fr.d α) (k α)
      = (fr.A ν α : ℝ) * tailB fr.bse (k α)
        + (fr.A ν α : ℝ)
            * (omegaR (fr.d α) / ((fr.bse : ℝ) - 1) - corrB fr.bse (fr.d α) (c α)) := by
    intro α
    rw [dilatedTailB_eq fr.hbse _ _ (hd α), corrB_congr (fr.d α) (k α) (c α) (hk α)]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, QuotientAddGroup.mk_add]
  unfold transportTheta
  congr 1
  unfold mulVecT
  rw [coe_finset_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  show (((fr.A ν α : ℝ) * tailB fr.bse (k α) : ℝ) : UnitAddCircle)
    = fr.A ν α • ((orbit fr.bse (primeLambertAtBase fr.bse) (k α) : ℝ) : UnitAddCircle)
  rw [← coe_tailB fr.hbse, ← zsmul_eq_mul, AddCircle.coe_zsmul]

/-- **`PropA` for a frame with frozen multiplier residues** (draft (4.3)).  If every sample
point is `t_α + d_α k_α` with `k_α ≡ c_α` modulo every prime of `d_α`, and `θ` is the transport
translate of `c`, then `Ffull n ∈ image`. -/
theorem propA_of_progression (hw : fr.w = omegaR) (hx : fr.x = primeLambertAtBase fr.bse)
    (c : Fin fr.H → ℕ) (hd : ∀ α, fr.d α ≠ 0)
    (hθ : fr.θ = fr.transportTheta c)
    (hP : ∀ n ∈ fr.P, ∃ k : Fin fr.H → ℕ, (∀ α, n = fr.t α + fr.d α * k α) ∧
      ∀ α, ∀ p ∈ (fr.d α).primeFactors, k α ≡ c α [MOD p]) :
    fr.PropA := by
  intro n hn
  obtain ⟨k, hnk, hk⟩ := hP n hn
  refine ⟨fun α => ((orbit fr.bse (primeLambertAtBase fr.bse) (k α) : ℝ) : UnitAddCircle),
    fun α => by rw [hx]; exact subset_closure (Set.mem_range_self _), ?_⟩
  funext ν
  unfold Ffull
  rw [hw]
  have hsum : (∑ α, (fr.A ν α : ℝ)
        * ∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (fr.bse : ℝ) ^ (j + 1))
      = ∑ α, (fr.A ν α : ℝ) * dilatedTailB fr.bse (fr.d α) (k α) :=
    Finset.sum_congr rfl fun α _ => by rw [hnk α, fr.tsum_eq_dilatedTailB]
  rw [hsum, fr.coe_sum_dilatedTailB c k hd hk ν, hθ]
  simp only [Pi.add_apply, Pi.sub_apply]

end Frame

end NormalNumbers.G4
