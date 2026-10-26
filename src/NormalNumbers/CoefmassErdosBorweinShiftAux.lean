/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinEndpoint

/-!
# Shifted growing-moment criterion: collision layer

This file generalizes the collision bookkeeping from
`CoefmassErdosBorweinEndpoint.lean` from one fixed anchor to an interval of anchors.  It is kept
separate so the packet-verbatim definitions and headline in `CoefmassErdosBorweinShift.lean`
remain easy to audit.
-/

namespace NormalNumbers.ErdosBorweinShift

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint
open NormalNumbers.RandomLambertMoment

/-- No divisor above `P` anchored at a shift in `[j₀,J]` of one tuple coordinate divides any of
the protected shifts `[1,K]` of a different coordinate. -/
def ShiftTupleCollisionFree (j₀ J K P k : ℕ) (n : Fin (2 * k) → ℕ) : Prop :=
  ∀ (i i' : Fin (2 * k)) (j r p : ℕ), i ≠ i' → j ∈ Finset.Icc j₀ J →
    r ∈ Finset.Icc 1 K → P < p → p ∣ n i + j → ¬ p ∣ n i' + r

/-- The finite union of all cross-coordinate collisions whose anchor lies in `[j₀,J]`. -/
def shiftTupleCollisionSet (j₀ J K P N k : ℕ) : Finset (Fin (2 * k) → Fin N) :=
  (Finset.univ : Finset (Fin (2 * k))).biUnion fun i =>
    (Finset.univ.erase i).biUnion fun i' =>
      (Finset.Icc j₀ J).biUnion fun j =>
        (Finset.Icc 1 K).biUnion fun r =>
          (Finset.Ioc P (N + K)).biUnion fun p => tupleCollisionFiber j r p N k i i'

/-- Membership in the shifted collision union is exactly failure of shifted collision freedom.
The second protected shift supplies the upper bound `p ≤ N + K`. -/
theorem mem_shiftTupleCollisionSet_iff_not_collisionFree
    {j₀ J K P N k : ℕ} {n : Fin (2 * k) → Fin N} :
    n ∈ shiftTupleCollisionSet j₀ J K P N k ↔
      ¬ ShiftTupleCollisionFree j₀ J K P k (fun t => (n t).val) := by
  classical
  constructor
  · intro hn hfree
    rcases Finset.mem_biUnion.mp hn with ⟨i, hi, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨i', hi', hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨j, hj, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨r, hr, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨p, hp, hn⟩
    have hii' : i ≠ i' := fun h => (Finset.mem_erase.mp hi').1 h.symm
    rcases Finset.mem_filter.mp hn with ⟨_, hpi, hpi'⟩
    exact (hfree i i' j r p hii' hj hr (Finset.mem_Ioc.mp hp).1 hpi) hpi'
  · intro hfree
    rw [ShiftTupleCollisionFree] at hfree
    push Not at hfree
    rcases hfree with ⟨i, i', j, r, p, hii', hj, hr, hPp, hpi, hpi'⟩
    have hp_le : p ≤ N + K := by
      have hp_nir : p ≤ (n i').val + r := Nat.le_of_dvd (by
        rcases Finset.mem_Icc.mp hr with ⟨hr1, _⟩
        omega) hpi'
      have hrK := (Finset.mem_Icc.mp hr).2
      omega
    rw [shiftTupleCollisionSet]
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.mem_biUnion.mpr
      ⟨i', Finset.mem_erase.mpr ⟨hii'.symm, Finset.mem_univ i'⟩, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨r, hr, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_Ioc.mpr ⟨hPp, hp_le⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ n, hpi, hpi'⟩

/-- Union-bound form of the shifted collision count. -/
theorem card_shiftTupleCollisionSet_le_sum (j₀ J K P N k : ℕ) :
    (shiftTupleCollisionSet j₀ J K P N k).card ≤
      ∑ i ∈ (Finset.univ : Finset (Fin (2 * k))),
        ∑ i' ∈ Finset.univ.erase i, ∑ j ∈ Finset.Icc j₀ J,
          ∑ r ∈ Finset.Icc 1 K, ∑ p ∈ Finset.Ioc P (N + K),
            (N / p + 1) ^ 2 * N ^ (2 * k - 2) := by
  classical
  unfold shiftTupleCollisionSet
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro i hi
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro i' hi'
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro r hr
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro p hp
  exact card_tupleCollisionFiber_le (Finset.ne_of_mem_erase hi').symm
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hp).1)

/-- The shifted collision union has one factor for each possible anchor and protected shift. -/
theorem card_shiftTupleCollisionSet_le (j₀ J K P N k : ℕ) :
    (shiftTupleCollisionSet j₀ J K P N k).card ≤
      (2 * k) * (2 * k - 1) * (Finset.Icc j₀ J).card * K *
        ∑ p ∈ Finset.Ioc P (N + K), (N / p + 1) ^ 2 * N ^ (2 * k - 2) := by
  refine (card_shiftTupleCollisionSet_le_sum j₀ J K P N k).trans_eq ?_
  classical
  have hcardK : (Finset.Icc 1 K).card = K := by simp [Nat.card_Icc]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem,
    Finset.mem_univ, Finset.card_univ, Fintype.card_fin, hcardK]
  norm_cast
  ring

/-- Normalized shifted collision density, before replacing the anchor interval cardinality by
the simpler upper bound `J`. -/
theorem shiftCollisionDensity_le (j₀ J K P N k : ℕ)
    (hP : 1 ≤ P) (hN : 1 ≤ N) (hK : K ≤ N) (hk : 1 ≤ k) :
    ((shiftTupleCollisionSet j₀ J K P N k).card : ℝ) / (N : ℝ) ^ (2 * k) ≤
      4 * (k : ℝ) ^ 2 * (Finset.Icc j₀ J).card * K *
        (3 / (P : ℝ) + 4 / (N : ℝ)) := by
  let S := Finset.Ioc P (N + K)
  let C : ℕ := (2 * k) * (2 * k - 1) * (Finset.Icc j₀ J).card * K
  have hcardNat := card_shiftTupleCollisionSet_le j₀ J K P N k
  have hcard : ((shiftTupleCollisionSet j₀ J K P N k).card : ℝ) ≤
      (C : ℝ) * ∑ p ∈ S,
        (((N / p + 1) ^ 2 * N ^ (2 * k - 2) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hsum : (∑ p ∈ S,
        (((N / p + 1) ^ 2 * N ^ (2 * k - 2) : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (2 * k) *
        ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 := by
    calc
      (∑ p ∈ S, (((N / p + 1) ^ 2 * N ^ (2 * k - 2) : ℕ) : ℝ)) ≤
          ∑ p ∈ S, (N : ℝ) ^ (2 * k) *
            ((1 : ℝ) / p + 1 / N) ^ 2 := by
        exact Finset.sum_le_sum fun p _ => cast_collision_fiber_bound_le N p k hN hk
      _ = (N : ℝ) ^ (2 * k) *
          ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 := by rw [Finset.mul_sum]
  have hcount : ((shiftTupleCollisionSet j₀ J K P N k).card : ℝ) ≤
      (C : ℝ) * ((N : ℝ) ^ (2 * k) *
        ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2) :=
    hcard.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hNpow : 0 < (N : ℝ) ^ (2 * k) := by positivity
  have htail : ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 ≤
      3 / (P : ℝ) + 4 / (N : ℝ) := by
    simpa only [S] using sum_divisor_collision_density_le P N K hP hN hK
  have hcoeffNat : C ≤ 4 * k ^ 2 * (Finset.Icc j₀ J).card * K := by
    dsimp only [C]
    calc
      (2 * k) * (2 * k - 1) * (Finset.Icc j₀ J).card * K ≤
          (2 * k) * (2 * k) * (Finset.Icc j₀ J).card * K := by gcongr; omega
      _ = 4 * k ^ 2 * (Finset.Icc j₀ J).card * K := by ring
  have hcoeff : (C : ℝ) ≤
      4 * (k : ℝ) ^ 2 * (Finset.Icc j₀ J).card * K := by exact_mod_cast hcoeffNat
  have htail0 : 0 ≤ 3 / (P : ℝ) + 4 / (N : ℝ) := by positivity
  calc
    ((shiftTupleCollisionSet j₀ J K P N k).card : ℝ) / (N : ℝ) ^ (2 * k) ≤
        ((C : ℝ) * ((N : ℝ) ^ (2 * k) *
          ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2)) /
            (N : ℝ) ^ (2 * k) := div_le_div_of_nonneg_right hcount hNpow.le
    _ = (C : ℝ) * ∑ p ∈ S, ((1 : ℝ) / p + 1 / N) ^ 2 := by
      field_simp [ne_of_gt hNpow]
    _ ≤ (C : ℝ) * (3 / (P : ℝ) + 4 / (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ (4 * (k : ℝ) ^ 2 * (Finset.Icc j₀ J).card * K) *
        (3 / (P : ℝ) + 4 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff htail0
    _ = 4 * (k : ℝ) ^ 2 * (Finset.Icc j₀ J).card * K *
        (3 / (P : ℝ) + 4 / (N : ℝ)) := by ring

/-- With a positive lower endpoint, the anchor interval has at most `J` elements. -/
theorem shiftCollisionDensity_le_four (j₀ J K P N k : ℕ)
    (hj₀ : 1 ≤ j₀) (hP : 1 ≤ P) (hN : 1 ≤ N) (hK : K ≤ N) (hk : 1 ≤ k) :
    ((shiftTupleCollisionSet j₀ J K P N k).card : ℝ) / (N : ℝ) ^ (2 * k) ≤
      4 * (k : ℝ) ^ 2 * J * K * (3 / (P : ℝ) + 4 / (N : ℝ)) := by
  have hmain := shiftCollisionDensity_le j₀ J K P N k hP hN hK hk
  have hcardNat : (Finset.Icc j₀ J).card ≤ J := by
    rw [Nat.card_Icc]
    omega
  have hcard : ((Finset.Icc j₀ J).card : ℝ) ≤ J := by exact_mod_cast hcardNat
  have hnonneg : 0 ≤ 4 * (k : ℝ) ^ 2 := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have htail0 : 0 ≤ 3 / (P : ℝ) + 4 / (N : ℝ) := by positivity
  exact hmain.trans (by gcongr)

/-! ## The shifted phase gap -/

/-- A non-anchor residue below the protected tail contributes at most its relative share of the
shifted anchor phase.  This is `scaled_residuePhase_le` with the anchor scale `b⁻ʲ` retained. -/
theorem scaled_residuePhase_le_shift (b H L j K p t : ℕ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hlarge : 16 * L * b ^ j ≤ b ^ K) (hp : 2 * K < p) (ht : t < p - K) :
    (H : ℝ) * residuePhase b p t ≤
      (H : ℝ) / (8 * (L : ℝ) * (b : ℝ) ^ j) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have htK : t + (K + 1) ≤ p := by omega
  have hpow2 : (2 : ℝ) ≤ (b : ℝ) ^ p := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ = (b : ℝ) ^ 1 := by ring
      _ ≤ (b : ℝ) ^ p := pow_le_pow_right₀ (by linarith) (by omega)
  have hdenpos : 0 < (b : ℝ) ^ p - 1 := by linarith
  have hdenhalf : (b : ℝ) ^ p / 2 ≤ (b : ℝ) ^ p - 1 := by linarith
  have hpowmono : (b : ℝ) ^ t * (b : ℝ) ^ (K + 1) ≤ (b : ℝ) ^ p := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ b) htK
  have hlargeR : (16 : ℝ) * L * (b : ℝ) ^ j ≤ (b : ℝ) ^ K := by
    exact_mod_cast hlarge
  have hpowK : (b : ℝ) ^ (K + 1) = (b : ℝ) ^ K * b := by rw [pow_succ]
  rw [hpowK] at hpowmono
  have hmain : (16 : ℝ) * b * L * (b : ℝ) ^ j * (b : ℝ) ^ t ≤
      (b : ℝ) ^ p := by
    calc
      (16 : ℝ) * b * L * (b : ℝ) ^ j * (b : ℝ) ^ t =
          (b : ℝ) ^ t * ((16 : ℝ) * L * (b : ℝ) ^ j) * b := by ring
      _ ≤ (b : ℝ) ^ t * (b : ℝ) ^ K * b := by gcongr
      _ ≤ (b : ℝ) ^ p := by simpa [mul_assoc] using hpowmono
  have hcross : (8 : ℝ) * L * (b : ℝ) ^ j * (b : ℝ) ^ t ≤
      (b : ℝ) ^ p - 1 := by nlinarith
  by_cases hH : H = 0
  · subst H
    simp
  have hHR : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  unfold residuePhase
  rw [show (H : ℝ) * ((b : ℝ) ^ t / ((b : ℝ) ^ p - 1)) =
    ((H : ℝ) * (b : ℝ) ^ t) / ((b : ℝ) ^ p - 1) by ring]
  rw [div_le_div_iff₀ hdenpos
    (by positivity : (0 : ℝ) < 8 * (L : ℝ) * (b : ℝ) ^ j)]
  calc
    (H : ℝ) * (b : ℝ) ^ t * (8 * (L : ℝ) * (b : ℝ) ^ j) =
        (H : ℝ) * (8 * (L : ℝ) * (b : ℝ) ^ j * (b : ℝ) ^ t) := by ring
    _ ≤ (H : ℝ) * ((b : ℝ) ^ p - 1) :=
      mul_le_mul_of_nonneg_left hcross hHR.le

/-- The finite-period correction at a shifted anchor is small relative to `H b⁻ʲ`. -/
theorem scaled_shift_anchor_phase_error (b H L j K p : ℕ) (hb : 2 ≤ b)
    (hL : 1 ≤ L) (hjK : j ≤ K) (hlarge : 16 * L * b ^ j ≤ b ^ K)
    (hp : 2 * K < p) :
    |(H : ℝ) * residuePhase b p (p - j) - (H : ℝ) / (b : ℝ) ^ j| ≤
      (H : ℝ) / (8 * (L : ℝ) * (b : ℝ) ^ j) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hjp : j ≤ p := by omega
  have hpow2 : (2 : ℝ) ≤ (b : ℝ) ^ p := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ = (b : ℝ) ^ 1 := by ring
      _ ≤ (b : ℝ) ^ p := pow_le_pow_right₀ (by linarith) (by omega)
  have hdenpos : 0 < (b : ℝ) ^ p - 1 := by linarith
  have hlargeR : (16 : ℝ) * L * (b : ℝ) ^ j ≤ (b : ℝ) ^ K := by
    exact_mod_cast hlarge
  have hKp : K + 1 ≤ p := by omega
  have hpowKp : (b : ℝ) ^ (K + 1) ≤ (b : ℝ) ^ p :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ b) hKp
  have hpowK1 : (b : ℝ) ^ (K + 1) = (b : ℝ) ^ K * b := by rw [pow_succ]
  have hdenlarge : (8 : ℝ) * L ≤ (b : ℝ) ^ p - 1 := by
    have hbig : (16 : ℝ) * L ≤ (b : ℝ) ^ p := by
      calc
        (16 : ℝ) * L ≤ (16 : ℝ) * L * (b : ℝ) ^ j := by
          have : (1 : ℝ) ≤ (b : ℝ) ^ j := one_le_pow₀ (by linarith)
          nlinarith
        _ ≤ (b : ℝ) ^ K := hlargeR
        _ ≤ (b : ℝ) ^ (K + 1) := by
          rw [hpowK1]
          exact le_mul_of_one_le_right (by positivity) (by linarith)
        _ ≤ (b : ℝ) ^ p := hpowKp
    nlinarith
  have herr :
      (H : ℝ) * residuePhase b p (p - j) - (H : ℝ) / (b : ℝ) ^ j =
        ((H : ℝ) / (b : ℝ) ^ j) / ((b : ℝ) ^ p - 1) := by
    unfold residuePhase
    have hpowsub : (b : ℝ) ^ (p - j) * (b : ℝ) ^ j = (b : ℝ) ^ p := by
      rw [← pow_add, Nat.sub_add_cancel hjp]
    field_simp [ne_of_gt hbpos, ne_of_gt hdenpos]
    nlinarith
  rw [herr, abs_of_nonneg (by positivity)]
  by_cases hH : H = 0
  · subst H
    simp
  have hHR : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  rw [div_div]
  rw [div_le_div_iff₀
    (by positivity : (0 : ℝ) < (b : ℝ) ^ j * ((b : ℝ) ^ p - 1))
    (by positivity : (0 : ℝ) < 8 * (L : ℝ) * (b : ℝ) ^ j)]
  calc
    (H : ℝ) * (8 * (L : ℝ) * (b : ℝ) ^ j) =
        (H : ℝ) * (b : ℝ) ^ j * (8 * (L : ℝ)) := by ring
    _ ≤ (H : ℝ) * (b : ℝ) ^ j * ((b : ℝ) ^ p - 1) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hdenlarge
        (mul_nonneg (Nat.cast_nonneg H) (by positivity : 0 ≤ (b : ℝ) ^ j))
    _ = (H : ℝ) * ((b : ℝ) ^ j * ((b : ℝ) ^ p - 1)) := by ring

/-- After orienting by the anchor sign, the whole shifted residue phase stays within one quarter
of its main term `H b⁻ʲ`. -/
theorem signed_tuple_shift_phase_error (b H j K k p : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hjK : j ≤ K) (hlarge : 16 * (2 * k) * b ^ j ≤ b ^ K) (hp : 2 * K < p)
    (t : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (hti : t i = p - j) (htail : ∀ i', i' ≠ i → t i' < p - K) :
    |(tupleSign k i : ℝ) *
        ((H : ℝ) * ∑ i', (tupleSign k i' : ℝ) * residuePhase b p (t i')) -
          (H : ℝ) / (b : ℝ) ^ j| ≤
      (H : ℝ) / (4 * (b : ℝ) ^ j) := by
  classical
  have hL : 1 ≤ 2 * k := by omega
  have hsabs (i' : Fin (2 * k)) : |(tupleSign k i' : ℝ)| = 1 := by
    by_cases hi' : i'.val < k <;> simp [tupleSign, hi']
  have hssq : (tupleSign k i : ℝ) * (tupleSign k i : ℝ) = 1 := by
    by_cases hi : i.val < k <;> simp [tupleSign, hi]
  have hres0 (r : ℕ) : 0 ≤ residuePhase b p r := by
    unfold residuePhase
    have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀
      (by exact_mod_cast (by omega : 1 < b)) (by omega)
    positivity
  have hanchor := scaled_shift_anchor_phase_error b H (2 * k) j K p hb hL hjK hlarge hp
  have htail_each (i' : Fin (2 * k)) (hi'i : i' ≠ i) :
      (H : ℝ) * residuePhase b p (t i') ≤
        (H : ℝ) / (8 * ((2 * k : ℕ) : ℝ) * (b : ℝ) ^ j) :=
    scaled_residuePhase_le_shift b H (2 * k) j K p (t i') hb hL hlarge hp
      (htail i' hi'i)
  let S : ℝ := ∑ i' ∈ Finset.univ.erase i,
    (tupleSign k i' : ℝ) * residuePhase b p (t i')
  have hsum :
      (∑ i', (tupleSign k i' : ℝ) * residuePhase b p (t i')) =
        (tupleSign k i : ℝ) * residuePhase b p (t i) + S := by
    rw [show (∑ i', (tupleSign k i' : ℝ) * residuePhase b p (t i')) =
        ∑ i' ∈ Finset.univ, (tupleSign k i' : ℝ) * residuePhase b p (t i') by simp]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [S]
    ring
  have hother : |(tupleSign k i : ℝ) * (H : ℝ) * S| ≤
      (H : ℝ) / (8 * (b : ℝ) ^ j) := by
    calc
      |(tupleSign k i : ℝ) * (H : ℝ) * S| = (H : ℝ) * |S| := by
        rw [abs_mul, abs_mul, hsabs, abs_of_nonneg (Nat.cast_nonneg H)]
        ring
      _ ≤ (H : ℝ) * ∑ i' ∈ Finset.univ.erase i,
          |(tupleSign k i' : ℝ) * residuePhase b p (t i')| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i' ∈ Finset.univ.erase i, (H : ℝ) * residuePhase b p (t i') := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i' hi'
        rw [abs_mul, hsabs, one_mul, abs_of_nonneg]
        exact hres0 (t i')
      _ ≤ ∑ _i' ∈ Finset.univ.erase i,
          (H : ℝ) / (8 * ((2 * k : ℕ) : ℝ) * (b : ℝ) ^ j) := by
        apply Finset.sum_le_sum
        intro i' hi'
        exact htail_each i' (Finset.ne_of_mem_erase hi')
      _ ≤ (H : ℝ) / (8 * (b : ℝ) ^ j) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc : (Finset.univ.erase i).card ≤ 2 * k := by
          calc
            (Finset.univ.erase i).card ≤ (Finset.univ : Finset (Fin (2 * k))).card :=
              Finset.card_le_card (Finset.erase_subset i _)
            _ = 2 * k := Fintype.card_fin (2 * k)
        have hconst : 0 ≤
            (H : ℝ) / (8 * ((2 * k : ℕ) : ℝ) * (b : ℝ) ^ j) := by positivity
        calc
          ((Finset.univ.erase i).card : ℝ) *
              ((H : ℝ) / (8 * ((2 * k : ℕ) : ℝ) * (b : ℝ) ^ j)) ≤
              ((2 * k : ℕ) : ℝ) *
                ((H : ℝ) / (8 * ((2 * k : ℕ) : ℝ) * (b : ℝ) ^ j)) := by
            gcongr
          _ = (H : ℝ) / (8 * (b : ℝ) ^ j) := by field_simp
  have hdecomp :
      (tupleSign k i : ℝ) *
          ((H : ℝ) * ∑ i', (tupleSign k i' : ℝ) * residuePhase b p (t i')) -
            (H : ℝ) / (b : ℝ) ^ j =
        ((H : ℝ) * residuePhase b p (t i) - (H : ℝ) / (b : ℝ) ^ j) +
          (tupleSign k i : ℝ) * (H : ℝ) * S := by
    calc
      _ = ((tupleSign k i : ℝ) * (tupleSign k i : ℝ)) *
            ((H : ℝ) * residuePhase b p (t i)) - (H : ℝ) / (b : ℝ) ^ j +
          (tupleSign k i : ℝ) * (H : ℝ) * S := by rw [hsum]; ring
      _ = _ := by rw [hssq]; ring
  rw [hdecomp, hti]
  calc
    |(H : ℝ) * residuePhase b p (p - j) - (H : ℝ) / (b : ℝ) ^ j +
        (tupleSign k i : ℝ) * (H : ℝ) * S| ≤
        |(H : ℝ) * residuePhase b p (p - j) - (H : ℝ) / (b : ℝ) ^ j| +
          |(tupleSign k i : ℝ) * (H : ℝ) * S| := abs_add_le _ _
    _ ≤ (H : ℝ) / (8 * ((2 * k : ℕ) : ℝ) * (b : ℝ) ^ j) +
        (H : ℝ) / (8 * (b : ℝ) ^ j) := add_le_add hanchor hother
    _ ≤ (H : ℝ) / (4 * (b : ℝ) ^ j) := by
      have hbpow : (0 : ℝ) < (b : ℝ) ^ j := by positivity
      have hLR : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hL
      have hH0 : (0 : ℝ) ≤ H := by positivity
      rw [div_eq_mul_inv (H : ℝ), div_eq_mul_inv (H : ℝ),
        div_eq_mul_inv (H : ℝ)]
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ hH0
      field_simp
      nlinarith

/-- A good divisor anchored at shift `j` has a cosine gap of size at least
`(1/2) b⁻²ʲ`.  The harmless constant is uniform in the Fourier frequency because `j` is chosen
above a fixed frequency-dependent lower cutoff. -/
theorem tupleGoodModuli_shift_cos_le (b H j K P k p : ℕ) (h : ℤ)
    (n : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hh : h ≠ 0) (hH : h.natAbs = H)
    (hj : 1 ≤ j) (hjK : j ≤ K) (hfreq : 4 * H ≤ b ^ j)
    (hlarge : 16 * (2 * k) * b ^ j ≤ b ^ K) (hKP : 2 * K ≤ P)
    (hgood : p ∈ tupleGoodModuli j K P k n i) :
    Real.cos (2 * Real.pi * tuplePhase b h k p n) ≤
      1 - (1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹ := by
  classical
  rcases (mem_tupleGoodModuli (a₀ := j) (K := K) (P₀ := P)
    (k := k) (p := p) (n := n) (i := i) hj).mp hgood with ⟨hpi, hPp, hsep⟩
  have hpK : 2 * K < p := lt_of_le_of_lt hKP hPp
  have hjp : j < p := by omega
  have hp1 : 1 ≤ p := by omega
  have hti : n i % p = p - j := anchor_residue_of_dvd hj hjp hpi
  have herr := signed_tuple_shift_phase_error b H j K k p hb hk hjK hlarge hpK
    (fun i' => n i' % p) i hti hsep
  let S : ℝ := ∑ i', (tupleSign k i' : ℝ) * residuePhase b p (n i' % p)
  let A : ℝ := (H : ℝ) / (b : ℝ) ^ j
  let y : ℝ := (tupleSign k i : ℝ) * (H : ℝ) * S
  have hApos : 0 < A := by
    dsimp only [A]
    have hHpos : 0 < H := by simpa [← hH] using Int.natAbs_pos.mpr hh
    positivity
  have herr' : |y - A| ≤ A / 4 := by
    convert herr using 1 <;> dsimp only [S, A, y] <;> ring
  have herrbounds := abs_le.mp herr'
  have hylo : A / 2 ≤ y := by nlinarith [hApos]
  have hAle : A ≤ 1 / 4 := by
    dsimp only [A]
    have hfreqR : (4 : ℝ) * H ≤ (b : ℝ) ^ j := by exact_mod_cast hfreq
    have hbpow : (0 : ℝ) < (b : ℝ) ^ j := by positivity
    apply (div_le_iff₀ hbpow).2
    nlinarith
  have hy0 : 0 ≤ y := le_trans (by positivity : 0 ≤ A / 2) hylo
  have hyhalf : y ≤ 1 / 2 := by nlinarith [herrbounds.2, hAle]
  have hphase : tuplePhase b h k p (fun i' => n i' % p) = (h : ℝ) * S := by
    simp only [tuplePhase, residuePhase, S]
  have hcosS :
      Real.cos (2 * Real.pi * tuplePhase b h k p (fun i' => n i' % p)) =
        Real.cos (2 * Real.pi * y) := by
    rw [hphase]
    by_cases hhpos : 0 ≤ h
    · have hcast : (h : ℝ) = (H : ℝ) := by
        rw [← hH, ← Int.cast_natCast, Int.natAbs_of_nonneg hhpos]
      rw [hcast]
      by_cases hi : i.val < k
      · simp [y, tupleSign, hi]
      · simp only [y, tupleSign, hi, if_false, Int.cast_neg, Int.cast_one, neg_mul]
        rw [show 2 * Real.pi * -(1 * (H : ℝ) * S) =
          -(2 * Real.pi * ((H : ℝ) * S)) by ring, Real.cos_neg]
    · have hhneg : h < 0 := lt_of_not_ge hhpos
      have hcast : (h : ℝ) = -(H : ℝ) := by
        rw [← hH]
        have habs : (h.natAbs : ℝ) = -(h : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg]
          exact_mod_cast hhneg
        linarith
      rw [hcast]
      by_cases hi : i.val < k
      · simp only [y, tupleSign, hi, if_true, Int.cast_one, one_mul]
        rw [show 2 * Real.pi * (-(H : ℝ) * S) =
          -(2 * Real.pi * ((H : ℝ) * S)) by ring, Real.cos_neg]
      · simp [y, tupleSign, hi]
  have harg : |2 * Real.pi * y| ≤ Real.pi := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) hy0)]
    nlinarith [Real.pi_pos]
  have hquad := Real.cos_le_one_sub_mul_cos_sq harg
  have hHone : (1 : ℝ) ≤ H := by
    exact_mod_cast (show 1 ≤ H by
      rw [← hH]
      exact Int.natAbs_pos.mpr hh)
  have hbinv : 0 < ((b : ℝ) ^ j)⁻¹ := by positivity
  have hylower : ((b : ℝ) ^ j)⁻¹ / 2 ≤ y := by
    apply le_trans _ hylo
    have hmul : ((b : ℝ) ^ j)⁻¹ ≤ (H : ℝ) * ((b : ℝ) ^ j)⁻¹ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hHone hbinv.le
    dsimp only [A]
    rw [div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hysq : (((b : ℝ) ^ j)⁻¹ / 2) ^ 2 ≤ y ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hylower 2
  have hgap : (1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹ ≤
      2 / Real.pi ^ 2 * (2 * Real.pi * y) ^ 2 := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    rw [show (b : ℝ) ^ (2 * j) = ((b : ℝ) ^ j) ^ 2 by
      rw [← pow_mul]; congr 1; ring]
    field_simp [hpi, ne_of_gt (show (0 : ℝ) < (b : ℝ) ^ j by positivity)] at hysq ⊢
    nlinarith [sq_nonneg y]
  calc
    Real.cos (2 * Real.pi * tuplePhase b h k p n) =
        Real.cos (2 * Real.pi * tuplePhase b h k p (fun i' => n i' % p)) :=
      cos_tuplePhase_mod b hb h k p hp1 n
    _ = Real.cos (2 * Real.pi * y) := hcosS
    _ ≤ 1 - 2 / Real.pi ^ 2 * (2 * Real.pi * y) ^ 2 := hquad
    _ ≤ 1 - (1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹ := by linarith

/-! ## Shift-window good moduli -/

/-- Shifted collision freedom identifies every anchor's good set with all large divisors at that
anchor. -/
theorem tupleGoodModuli_eq_large_divisors_of_shiftCollisionFree
    {j₀ J K P k : ℕ} {n : Fin (2 * k) → ℕ} (i : Fin (2 * k)) {j : ℕ}
    (hj₀ : 1 ≤ j₀) (hj : j ∈ Finset.Icc j₀ J) (hKP : K ≤ P)
    (hfree : ShiftTupleCollisionFree j₀ J K P k n) :
    tupleGoodModuli j K P k n i = (n i + j).divisors.filter (fun p => P < p) := by
  apply tupleGoodModuli_eq_large_divisors_of_collisionFree i (by
    have := (Finset.mem_Icc.mp hj).1
    omega) hKP
  intro i₁ i₂ r p hi₁i₂ hr hPp hpi
  exact hfree i₁ i₂ j r p hi₁i₂ hj hr hPp hpi

/-- Distinct coordinate-shift anchors have disjoint good-modulus sets.  For equal coordinates a
common divisor would divide the nonzero shift difference, which is smaller than the cutoff; for
distinct coordinates this is exactly shifted collision freedom. -/
theorem disjoint_tupleGoodModuli_shift
    {j₀ J K P k : ℕ} {n : Fin (2 * k) → ℕ}
    (hj₀ : 1 ≤ j₀) (hJK : J ≤ K) (hJP : J ≤ P)
    (hfree : ShiftTupleCollisionFree j₀ J K P k n)
    (i i' : Fin (2 * k)) {j j' : ℕ}
    (hj : j ∈ Finset.Icc j₀ J) (hj' : j' ∈ Finset.Icc j₀ J)
    (hpair : (i, j) ≠ (i', j')) :
    Disjoint (tupleGoodModuli j K P k n i) (tupleGoodModuli j' K P k n i') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hj'1 := (Finset.mem_Icc.mp hj').1
  rcases (mem_tupleGoodModuli (a₀ := j) (K := K) (P₀ := P)
    (k := k) (p := p) (n := n) (i := i) (by omega)).mp hp with ⟨hpi, hPp, _⟩
  rcases (mem_tupleGoodModuli (a₀ := j') (K := K) (P₀ := P)
    (k := k) (p := p) (n := n) (i := i') (by omega)).mp hp' with ⟨hpi', _, _⟩
  by_cases hii' : i = i'
  · subst i'
    have hjne : j ≠ j' := by
      intro hjj'
      exact hpair (Prod.ext rfl hjj')
    rcases lt_or_gt_of_ne hjne with hjlt | hjgt
    · have hdvd : p ∣ j' - j := by
        have := Nat.dvd_sub hpi' hpi
        simpa only [Nat.add_sub_add_left] using this
      have hpos : 0 < j' - j := by omega
      have hple : p ≤ j' - j := Nat.le_of_dvd hpos hdvd
      have hj'J := (Finset.mem_Icc.mp hj').2
      omega
    · have hdvd : p ∣ j - j' := by
        have := Nat.dvd_sub hpi hpi'
        simpa only [Nat.add_sub_add_left] using this
      have hpos : 0 < j - j' := by omega
      have hple : p ≤ j - j' := Nat.le_of_dvd hpos hdvd
      have hjJ := (Finset.mem_Icc.mp hj).2
      omega
  · have hj'protected : j' ∈ Finset.Icc 1 K := by
      rcases Finset.mem_Icc.mp hj' with ⟨hj'low, hj'high⟩
      exact Finset.mem_Icc.mpr ⟨by omega, hj'high.trans hJK⟩
    exact (hfree i i' j j' p hii' hj hj'protected hPp hpi) hpi'

/-- Union of the good-modulus sets over all tuple coordinates and all shifted anchors. -/
def shiftAllGoodModuli (j₀ J K P k : ℕ) (n : Fin (2 * k) → ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin (2 * k))).biUnion fun i =>
    (Finset.Icc j₀ J).biUnion fun j => tupleGoodModuli j K P k n i

/-- The shifted good-modulus union factors without multiplicity on collision-free tuples. -/
theorem prod_shiftAllGoodModuli {j₀ J K P k : ℕ} {n : Fin (2 * k) → ℕ}
    (hj₀ : 1 ≤ j₀) (hJK : J ≤ K) (hJP : J ≤ P)
    (hfree : ShiftTupleCollisionFree j₀ J K P k n) (f : ℕ → ℝ) :
    (∏ p ∈ shiftAllGoodModuli j₀ J K P k n, f p) =
      ∏ i : Fin (2 * k), ∏ j ∈ Finset.Icc j₀ J,
        ∏ p ∈ tupleGoodModuli j K P k n i, f p := by
  classical
  unfold shiftAllGoodModuli
  rw [Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.prod_biUnion]
    intro j hj j' hj' hjj'
    exact disjoint_tupleGoodModuli_shift hj₀ hJK hJP hfree i i hj hj'
      (fun hp => hjj' (congrArg Prod.snd hp))
  · intro i hi i' hi' hii'
    change Disjoint
      ((Finset.Icc j₀ J).biUnion fun j => tupleGoodModuli j K P k n i)
      ((Finset.Icc j₀ J).biUnion fun j => tupleGoodModuli j K P k n i')
    rw [Finset.disjoint_left]
    intro p hp hp'
    rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hpj⟩
    rcases Finset.mem_biUnion.mp hp' with ⟨j', hj', hpj'⟩
    exact (Finset.disjoint_left.mp
      (disjoint_tupleGoodModuli_shift hj₀ hJK hJP hfree i i' hj hj'
        (fun hp => hii' (congrArg Prod.fst hp)))) hpj hpj'

/-- On a shifted-collision-free tuple, the characteristic product contracts by the complete
weighted divisor-variance mass over the shift window. -/
theorem global_bernMod_product_le_shiftedMass_of_collisionFree
    (delta : ℕ → ℝ) (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (b H j₀ J K P k N : ℕ) (h : ℤ) (n : Fin (2 * k) → Fin N)
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hh : h ≠ 0) (hH : h.natAbs = H)
    (hj₀ : 1 ≤ j₀) (hfreq : 4 * H ≤ b ^ j₀) (hJK : J ≤ K) (hP : 1 ≤ P)
    (hlarge : 16 * (2 * k) * b ^ J ≤ b ^ K) (hKP : 2 * K ≤ P)
    (hfree : ShiftTupleCollisionFree j₀ J K P k (fun i => (n i).val)) :
    ∏ r ∈ Finset.range (N + K),
        bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun i => (n i).val)) ≤
      Real.exp (-(1 / 2 : ℝ) *
        ∑ i : Fin (2 * k), ∑ j ∈ Finset.Icc j₀ J,
          ((b : ℝ) ^ (2 * j))⁻¹ *
            divisorVarianceMass (fun p => delta p * (1 - delta p))
              P ((n i).val + j)) := by
  classical
  let A := shiftAllGoodModuli j₀ J K P k (fun i => (n i).val)
  let G := A.image (fun p => p - 1)
  have hJP : J ≤ P := by omega
  have hp_two (p : ℕ) (hp : p ∈ A) : 2 ≤ p := by
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hp⟩
    rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hpj⟩
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hcut := ((mem_tupleGoodModuli (a₀ := j) (K := K) (P₀ := P)
      (k := k) (p := p) (n := fun i => (n i).val) (i := i) (by omega)).mp hpj).2.1
    omega
  have hsubset : G ⊆ Finset.range (N + K) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hp⟩
    rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hpj⟩
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hpdiv := ((mem_tupleGoodModuli (a₀ := j) (K := K) (P₀ := P)
      (k := k) (p := p) (n := fun i => (n i).val) (i := i) (by omega)).mp hpj).1
    have hple : p ≤ (n i).val + j := Nat.le_of_dvd (by omega) hpdiv
    have hjK := (Finset.mem_Icc.mp hj).2.trans hJK
    rw [Finset.mem_range]
    omega
  have hglobal :
      (∏ r ∈ Finset.range (N + K),
          bernMod (delta (r + 1))
            (tuplePhase b h k (r + 1) (fun i => (n i).val))) ≤
        ∏ r ∈ G, bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun i => (n i).val)) := by
    apply Finset.prod_le_prod_of_subset_of_le_one hsubset
    · intro r hr
      exact bernMod_nonneg _ _
    · intro r hr hrG
      exact bernMod_le_one (hdelta (r + 1)).1 (hdelta (r + 1)).2 _
  have hinj : Set.InjOn (fun p : ℕ => p - 1) ↑A := by
    intro p hp q hq hpq
    have hp1 : 1 ≤ p := le_trans (by omega) (hp_two p hp)
    have hq1 : 1 ≤ q := le_trans (by omega) (hp_two q hq)
    change p - 1 = q - 1 at hpq
    omega
  have hreindex :
      (∏ r ∈ G, bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun i => (n i).val))) =
        ∏ p ∈ A, bernMod (delta p)
          (tuplePhase b h k p (fun i => (n i).val)) := by
    dsimp only [G]
    rw [Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.sub_add_cancel (by have := hp_two p hp; omega : 1 ≤ p)]
  have hpair (i : Fin (2 * k)) (j : ℕ) (hj : j ∈ Finset.Icc j₀ J) :
      (∏ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
          bernMod (delta p) (tuplePhase b h k p (fun i => (n i).val))) ≤
        Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹ *
          ∑ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
            delta p * (1 - delta p)) := by
    calc
      (∏ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
          bernMod (delta p) (tuplePhase b h k p (fun i => (n i).val))) ≤
        ∏ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
          Real.exp (-((1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹) *
            (delta p * (1 - delta p))) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact bernMod_nonneg _ _
        · intro p hp
          apply bernMod_le_exp_of_cos_le (hdelta p).1 (hdelta p).2
          have hjbounds := Finset.mem_Icc.mp hj
          have hfreqj : 4 * H ≤ b ^ j :=
            hfreq.trans (Nat.pow_le_pow_right (by omega : 0 < b) hjbounds.1)
          have hlargej : 16 * (2 * k) * b ^ j ≤ b ^ K := by
            exact (Nat.mul_le_mul_left (16 * (2 * k))
              (Nat.pow_le_pow_right (by omega : 0 < b) hjbounds.2)).trans hlarge
          exact tupleGoodModuli_shift_cos_le b H j K P k p h
            (fun i => (n i).val) i hb hk hh hH (hj₀.trans hjbounds.1)
            (hjbounds.2.trans hJK) hfreqj hlargej hKP hp
      _ = Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹ *
          ∑ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
            delta p * (1 - delta p)) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
        ring
  have hall :
      (∏ p ∈ A, bernMod (delta p)
          (tuplePhase b h k p (fun i => (n i).val))) ≤
        Real.exp (-(1 / 2 : ℝ) *
          ∑ i : Fin (2 * k), ∑ j ∈ Finset.Icc j₀ J,
            ((b : ℝ) ^ (2 * j))⁻¹ *
              divisorVarianceMass (fun p => delta p * (1 - delta p))
                P ((n i).val + j)) := by
    rw [prod_shiftAllGoodModuli hj₀ hJK hJP hfree]
    calc
      (∏ i : Fin (2 * k), ∏ j ∈ Finset.Icc j₀ J,
          ∏ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
            bernMod (delta p) (tuplePhase b h k p (fun i => (n i).val))) ≤
        ∏ i : Fin (2 * k), ∏ j ∈ Finset.Icc j₀ J,
          Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹ *
            ∑ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
              delta p * (1 - delta p)) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact Finset.prod_nonneg fun j hj =>
            Finset.prod_nonneg fun p hp => bernMod_nonneg _ _
        · intro i hi
          apply Finset.prod_le_prod
          · intro j hj
            exact Finset.prod_nonneg fun p hp => bernMod_nonneg _ _
          · intro j hj
            exact hpair i j hj
      _ = Real.exp (∑ i : Fin (2 * k), ∑ j ∈ Finset.Icc j₀ J,
          (-(1 / 2 : ℝ) * ((b : ℝ) ^ (2 * j))⁻¹ *
            ∑ p ∈ tupleGoodModuli j K P k (fun i => (n i).val) i,
              delta p * (1 - delta p))) := by
        simp_rw [← Real.exp_sum]
      _ = Real.exp (-(1 / 2 : ℝ) *
          ∑ i : Fin (2 * k), ∑ j ∈ Finset.Icc j₀ J,
            ((b : ℝ) ^ (2 * j))⁻¹ *
              divisorVarianceMass (fun p => delta p * (1 - delta p))
                P ((n i).val + j)) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [tupleGoodModuli_eq_large_divisors_of_shiftCollisionFree i hj₀ hj
          (by omega) hfree]
        unfold divisorVarianceMass
        ring
  exact hglobal.trans (hreindex.le.trans hall)

end NormalNumbers.ErdosBorweinShift
