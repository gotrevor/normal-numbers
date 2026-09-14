/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyAtomFreq

/-!
# Entropy expedition — the scale bands

`certified_granule_exceeds_previous_scale` forbids *normality* of any concatenation of certified
granules.  What it does not forbid is convergence of the prefix frequencies **along a
subsequence of cutoffs** — at the end of each scale's contribution, where the history is
negligible and the new content is certified as a whole.

Reading a scale "as a whole" in position order requires the scales to occupy *ordered* bands.
They do not: scale `i`'s sampled positions start near `0`.  The fix is to drop, at each scale,
the windows below the previous scale's ceiling.  This module proves that this drops almost
nothing: the multiplier `d_α` is at most `gridDm`, which is `exp(logP₀Nat K) ≤ 2^{2·2^{21K²}}`,
while the sample range jumps from `X(K_i) = 2^{100·2^{m(K_i)}}` to `X(K_{i+1})` with
`2^{m(K_{i+1})} ≥ 2·2^{m(K_i)}` and `m(K) ≥ K³`.  So

    `6 · gridDm(K_{i+1}) · X(K_i)  <  X(K_{i+1})`,

i.e. the previous scale's entire position range, inflated by the largest possible multiplier, is
a vanishing part of the next scale's.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-- **`gridDm ≤ 2^{2·2^{21K²}}`**, from `log P₀ ≤ logP₀Nat K ≤ 2^{21K²}`. -/
lemma gridDm_le_two_pow {K : ℕ} (hK : 100 ≤ K) :
    gridDm K (N K) ≤ 2 ^ (2 * 2 ^ (21 * K ^ 2)) := by
  have h1 : gridDm K (N K) ≤ gridP₀Bound K (N K) := gridDm_le_gridP₀Bound K (N K) (by omega)
  have hpos : (0 : ℝ) < gridP₀Bound K (N K) := by
    have := gridDm_pos K (N K)
    exact_mod_cast (by omega : 0 < gridP₀Bound K (N K))
  have h2 : (gridP₀Bound K (N K) : ℝ) ≤ Real.exp (logP₀Nat K) := by
    calc (gridP₀Bound K (N K) : ℝ) = Real.exp (Real.log (gridP₀Bound K (N K))) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.2 (log_gridP₀Bound_le (by omega))
  have h3 : Real.exp (logP₀Nat K) ≤ (2 : ℝ) ^ (2 * logP₀Nat K) := exp_nat_le_two_pow _
  have h4 : (2 : ℝ) ^ (2 * logP₀Nat K) ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * K ^ 2)) := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    have := logP₀Nat_le_two_pow hK
    omega
  have h5 : (gridDm K (N K) : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * K ^ 2)) := by
    have hcast : (gridDm K (N K) : ℝ) ≤ (gridP₀Bound K (N K) : ℝ) := by exact_mod_cast h1
    linarith
  have : (gridDm K (N K) : ℝ) ≤ ((2 ^ (2 * 2 ^ (21 * K ^ 2)) : ℕ) : ℝ) := by
    push_cast
    exact h5
  exact_mod_cast this

/-- The exponent gap: `m(K_i) ≥ K_i³` already dwarfs `21·K_{i+1}² + 2`. -/
lemma exponent_gap (i : ℕ) :
    3 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i) < 100 * 2 ^ m (KK (i + 1)) := by
  have hK : 160000 ≤ KK i := KK_ge i
  have hsucc : KK (i + 1) = KK i + 4 := KK_succ i
  -- `m (KK i) ≥ KK i ³ ≥ 21·KK (i+1)² + 2`
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by omega)
    unfold m
    omega
  have hbig : 21 * KK (i + 1) ^ 2 + 2 ≤ KK i ^ 3 := by
    rw [hsucc]
    nlinarith [hK]
  have hstep : 2 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := two_pow_m_step i
  have hmono : 2 ^ (21 * KK (i + 1) ^ 2 + 2) ≤ 2 ^ m (KK i) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (21 * KK (i + 1) ^ 2 + 2) = 4 * 2 ^ (21 * KK (i + 1) ^ 2) := by
    rw [pow_add]; ring
  have hone : 1 ≤ 2 ^ (21 * KK (i + 1) ^ 2) := Nat.one_le_two_pow
  omega

/-- The strengthened exponent gap, with room for the modulus term. -/
lemma exponent_gap_strong (i : ℕ) :
    4 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i) ≤ 99 * 2 ^ m (KK (i + 1)) := by
  have hK : 160000 ≤ KK i := KK_ge i
  have hsucc : KK (i + 1) = KK i + 4 := KK_succ i
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by omega)
    unfold m
    omega
  have hbig : 21 * KK (i + 1) ^ 2 + 2 ≤ KK i ^ 3 := by
    rw [hsucc]
    nlinarith [hK]
  have hstep : 2 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := two_pow_m_step i
  have hmono : 2 ^ (21 * KK (i + 1) ^ 2 + 2) ≤ 2 ^ m (KK i) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (21 * KK (i + 1) ^ 2 + 2) = 4 * 2 ^ (21 * KK (i + 1) ^ 2) := by
    rw [pow_add]; ring
  have hone : 1 ≤ 2 ^ (21 * KK (i + 1) ^ 2) := Nat.one_le_two_pow
  omega

/-- The modulus is tiny against the sample range. -/
lemma P₀_le_two_pow_band (i : ℕ) :
    ((gridAt (i + 1)).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m (KK (i + 1))) :=
  P₀_le_two_pow (show 100 ≤ KK (i + 1) by have := KK_ge (i + 1); omega)

/-- **The band gap.**  The previous scale's whole position range, inflated by the largest
multiplier the next scale's grid admits, is still a vanishing part of the next scale's range. -/
theorem band_gap (i : ℕ) :
    6 * gridDm (KK (i + 1)) (N (KK (i + 1))) * X (KK i) < X (KK (i + 1)) := by
  have hK1 : 100 ≤ KK (i + 1) := by have := KK_ge (i + 1); omega
  have hDm := gridDm_le_two_pow hK1
  have hX : ∀ j : ℕ, X (KK j) = 2 ^ (100 * 2 ^ m (KK j)) := fun _ => rfl
  have hgap := exponent_gap i
  calc 6 * gridDm (KK (i + 1)) (N (KK (i + 1))) * X (KK i)
      ≤ 2 ^ 3 * 2 ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) * 2 ^ (100 * 2 ^ m (KK i)) := by
        rw [hX i]
        refine Nat.mul_le_mul_right _ (Nat.mul_le_mul ?_ hDm)
        norm_num
    _ = 2 ^ (3 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i)) := by
        rw [← pow_add, ← pow_add]
    _ < 2 ^ (100 * 2 ^ m (KK (i + 1))) := Nat.pow_lt_pow_right (by norm_num) hgap
    _ = X (KK (i + 1)) := (hX (i + 1)).symm


/-! ### The band-gap inequality in the form the count consumes -/

set_option maxHeartbeats 1000000 in
/-- `12·gridDm(K_{i+1})·X(K_i) + 4·P₀_{i+1} ≤ X(K_{i+1})`. -/
theorem band_gap_strong (i : ℕ) :
    (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
        + 4 * ((gridAt (i + 1)).P₀ : ℝ)
      ≤ (X (KK (i + 1)) : ℝ) := by
  have hK1 : 100 ≤ KK (i + 1) := by have := KK_ge (i + 1); omega
  have hgap := exponent_gap_strong i
  have hstep := two_pow_m_step i
  have hXv : ∀ j : ℕ, ((X (KK j) : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m (KK j)) := by
    intro j
    show ((2 ^ (100 * 2 ^ m (KK j)) : ℕ) : ℝ) = _
    push_cast; ring
  -- first term
  have hA : (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
      ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := by
    have hDm : (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ)
        ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) := by
      have h := gridDm_le_two_pow hK1
      have : ((gridDm (KK (i + 1)) (N (KK (i + 1))) : ℕ) : ℝ)
          ≤ ((2 ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      exact this
    have h12 : (12 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
    have hpos1 : (0 : ℝ) < (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) := by positivity
    calc (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
        ≤ (2 : ℝ) ^ 4 * (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2))
            * (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by
          rw [hXv i]
          have hXpos : (0 : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by positivity
          have hDmpos : (0 : ℝ) ≤ (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) :=
            Nat.cast_nonneg _
          have h1 : (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ)
              ≤ (2 : ℝ) ^ 4 * (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) :=
            mul_le_mul h12 hDm hDmpos (by positivity)
          exact mul_le_mul_of_nonneg_right h1 hXpos
      _ = (2 : ℝ) ^ (4 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i)) := by
          rw [← pow_add, ← pow_add]
      _ ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := pow_le_pow_right₀ (by norm_num) hgap
  -- second term
  have hB : 4 * ((gridAt (i + 1)).P₀ : ℝ) ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := by
    have hP := P₀_le_two_pow_band i
    have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    have hsum : 2 + 2 * 2 ^ m (KK (i + 1)) ≤ 99 * 2 ^ m (KK (i + 1)) := by
      have hone : 1 ≤ 2 ^ m (KK (i + 1)) := Nat.one_le_two_pow
      omega
    calc 4 * ((gridAt (i + 1)).P₀ : ℝ)
        ≤ (2 : ℝ) ^ 2 * (2 : ℝ) ^ (2 * 2 ^ m (KK (i + 1))) := by
          rw [← h4]
          exact mul_le_mul_of_nonneg_left hP (by norm_num)
      _ = (2 : ℝ) ^ (2 + 2 * 2 ^ m (KK (i + 1))) := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := pow_le_pow_right₀ (by norm_num) hsum
  have hfin : (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) + (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1)))
      ≤ (X (KK (i + 1)) : ℝ) := by
    rw [hXv (i + 1)]
    have h2 : (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) + (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1)))
        = (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1)) + 1) := by rw [pow_succ]; ring
    rw [h2]
    refine pow_le_pow_right₀ (by norm_num) ?_
    have hone : 1 ≤ 2 ^ m (KK (i + 1)) := Nat.one_le_two_pow
    omega
  linarith


/-! ### The band set -/

/-- Scale `i`'s sampled positions all lie below `bandTop i`. -/
noncomputable def bandTop (i : ℕ) : ℕ := 2 * X (KK i) + kk i

/-- The floor of band `i`: at scale `i+1` only the windows above scale `i`'s ceiling are read. -/
noncomputable def bandLo : ℕ → ℕ
  | 0 => 0
  | (i + 1) => bandTop i

/-- The orbit index never exceeds the sample time. -/
lemma kIdx_le_self (G : GridParams) (n : ℕ) (α : G.Atom) : kIdx G n α ≤ n :=
  le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)

/-- Every scale-`i` sampled position is below `bandTop i`. -/
lemma pos_lt_bandTop (i : ℕ) {n : ℕ} (hn : n ∈ PK i) (α : (gridAt i).Atom) {p : ℕ}
    (hp : p < kk i) : 2 * kIdx (gridAt i) n α + p < bandTop i := by
  have hnX : n < X (KK i) := Finset.mem_range.1 (Finset.mem_filter.1 hn).1
  have := kIdx_le_self (gridAt i) n α
  unfold bandTop
  omega

open Classical in
/-- An arithmetic progression of modulus `P₀` meets `[0, M)` at most `M/P₀ + 1` times. -/
lemma card_filter_lt_apSample_le (Xb P₀ a M : ℕ) (hP₀ : 0 < P₀) :
    (((apSample Xb P₀ a).filter (fun n => n < M)).card) ≤ M / P₀ + 1 := by
  classical
  have hcard : (((apSample Xb P₀ a).filter (fun n => n < M)).card)
      ≤ (Finset.range (M / P₀ + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / P₀) ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hn
      have h1 : n < M := hn.2
      have h2 : n / P₀ ≤ M / P₀ := Nat.div_le_div_right (le_of_lt h1)
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro n hn n' hn' heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hn hn'
      have h1 : n % P₀ = a := (Finset.mem_filter.1 hn.1).2
      have h2 : n' % P₀ = a := (Finset.mem_filter.1 hn'.1).2
      have e1 := Nat.div_add_mod n P₀
      have e2 := Nat.div_add_mod n' P₀
      rw [h1] at e1
      rw [h2] at e2
      simp only at heq
      rw [heq] at e1
      omega
  simpa using hcard

open Classical in
/-- The band-`i` sample times at the chosen good atom. -/
noncomputable def bandS (i : ℕ) : Finset ℕ :=
  (PK i).filter (fun n => bandLo i ≤ 2 * kIdx (gridAt i) n (goodAtom i))

lemma bandS_subset (i : ℕ) : bandS i ⊆ PK i := Finset.filter_subset _ _

/-- Every band-`i` window opens at or above the band floor. -/
lemma bandLo_le_of_mem_bandS (i : ℕ) {n : ℕ} (hn : n ∈ bandS i) :
    bandLo i ≤ 2 * kIdx (gridAt i) n (goodAtom i) := (Finset.mem_filter.1 hn).2

/-- `kk i + 1 ≤ X (KK i)`: the window length is nothing against the sample range. -/
lemma kk_succ_le_X (i : ℕ) : kk i + 1 ≤ X (KK i) := by
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by have := KK_ge i; omega)
    unfold m
    omega
  have h2 : m (KK i) < 2 ^ m (KK i) := Nat.lt_two_pow_self
  have hkKK : kk i ≤ KK i := by unfold KK; omega
  have hKcube : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
  have hstep : kk i + 1 ≤ 100 * 2 ^ m (KK i) := by omega
  calc kk i + 1 ≤ 2 ^ (kk i + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ 2 ^ (100 * 2 ^ m (KK i)) := Nat.pow_le_pow_right (by norm_num) hstep
    _ = X (KK i) := rfl

open Classical in
/-- **The band keeps at least half of the sample.**  The dropped sample times are those whose
orbit index is below the previous scale's ceiling; each is smaller than
`3·gridDm(K_{i+1})·X(K_i)`, and `band_gap_strong` makes that a quarter of the range. -/
theorem card_bandS_ge (i : ℕ) : ((PK (i + 1)).card : ℝ) ≤ 2 * ((bandS (i + 1)).card : ℝ) := by
  classical
  set j := i + 1 with hj
  set Dm : ℕ := gridDm (KK j) (N (KK j)) with hDm
  set M : ℕ := 3 * Dm * X (KK i) with hM
  -- the dropped times are small
  have hdrop : (PK j).filter (fun n => ¬ bandLo j ≤ 2 * kIdx (gridAt j) n (goodAtom j))
      ⊆ (PK j).filter (fun n => n < M) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    have hlt : 2 * kIdx (gridAt j) n (goodAtom j) < bandLo j := by
      have := hn.2; omega
    have hbl : bandLo j = bandTop i := rfl
    obtain ⟨hk, -⟩ := kIdx_spec (gridAt j) (X := X (KK j)) hn.1 (goodAtom j)
    have hd : (gridAt j).d (goodAtom j) ≤ Dm := by
      rw [hDm]
      exact gridOf.d_le (K := KK j) (N := N (KK j)) (hK := KK_one_le j) (goodAtom j)
    have ht : (gridAt j).t (goodAtom j) < (gridAt j).d (goodAtom j) :=
      (gridAt j).t_lt_d (goodAtom j)
    have hkk := kk_succ_le_X i
    have hbt : bandTop i = 2 * X (KK i) + kk i := rfl
    have hdpos : 0 < (gridAt j).d (goodAtom j) := (gridAt j).d_pos _
    -- `n = t + d·k < d·(k+1) ≤ Dm·(X_i + kk i + 1) ≤ 3·Dm·X_i`
    have hkbound : kIdx (gridAt j) n (goodAtom j) < X (KK i) + kk i := by
      rw [hbl, hbt] at hlt; omega
    have hnlt : n < (gridAt j).d (goodAtom j) * (X (KK i) + kk i + 1) := by
      have : n = (gridAt j).t (goodAtom j)
          + (gridAt j).d (goodAtom j) * kIdx (gridAt j) n (goodAtom j) := hk
      have hmul : (gridAt j).d (goodAtom j) * kIdx (gridAt j) n (goodAtom j)
          + (gridAt j).d (goodAtom j)
          = (gridAt j).d (goodAtom j) * (kIdx (gridAt j) n (goodAtom j) + 1) := by ring
      have hmono : (gridAt j).d (goodAtom j) * (kIdx (gridAt j) n (goodAtom j) + 1)
          ≤ (gridAt j).d (goodAtom j) * (X (KK i) + kk i + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hfin : (gridAt j).d (goodAtom j) * (X (KK i) + kk i + 1) ≤ M := by
      rw [hM]
      have h1 : X (KK i) + kk i + 1 ≤ 3 * X (KK i) := by omega
      calc (gridAt j).d (goodAtom j) * (X (KK i) + kk i + 1)
          ≤ Dm * (3 * X (KK i)) := Nat.mul_le_mul hd h1
        _ = 3 * Dm * X (KK i) := by ring
    omega
  -- count them
  have hPpos : (0 : ℝ) < ((gridAt j).P₀ : ℝ) := by
    have := (gridAt j).P₀_pos
    exact_mod_cast this
  have hcount : (((PK j).filter (fun n => n < M)).card : ℝ) ≤ (M : ℝ) / ((gridAt j).P₀ : ℝ) + 1 := by
    have h := card_filter_lt_apSample_le (X (KK j)) (gridAt j).P₀ (gridAt j).b₀ M
      (gridAt j).P₀_pos
    have hR : ((((PK j).filter (fun n => n < M)).card : ℕ) : ℝ)
        ≤ ((M / (gridAt j).P₀ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    refine hR.trans ?_
    push_cast
    have : ((M / (gridAt j).P₀ : ℕ) : ℝ) ≤ (M : ℝ) / ((gridAt j).P₀ : ℝ) := Nat.cast_div_le
    linarith
  -- the sample is big
  have hbig : (X (KK j) : ℝ) / (2 * ((gridAt j).P₀ : ℝ)) ≤ ((PK j).card : ℝ) :=
    card_apSample_ge_half (X (KK j)) (gridAt j).P₀ (gridAt j).b₀ (gridAt j).P₀_pos
      (gridAt j).b₀_lt_P₀ (two_mul_P₀_le_X (show 100 ≤ KK j by have := KK_ge j; omega))
  -- the gate
  have hgate : (12 : ℝ) * (Dm : ℝ) * (X (KK i) : ℝ) + 4 * ((gridAt j).P₀ : ℝ)
      ≤ (X (KK j) : ℝ) := band_gap_strong i
  have hMR : (M : ℝ) = 3 * (Dm : ℝ) * (X (KK i) : ℝ) := by rw [hM]; push_cast; ring
  have hhalf : 2 * ((M : ℝ) / ((gridAt j).P₀ : ℝ) + 1) ≤ ((PK j).card : ℝ) := by
    refine le_trans ?_ hbig
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * ((gridAt j).P₀ : ℝ))]
    have hexp : 2 * ((M : ℝ) / ((gridAt j).P₀ : ℝ) + 1) * (2 * ((gridAt j).P₀ : ℝ))
        = 4 * (M : ℝ) + 4 * ((gridAt j).P₀ : ℝ) := by
      field_simp
      ring
    rw [hexp, hMR]
    linarith [hgate]
  -- assemble
  have hsplit : ((PK j).card : ℝ)
      = ((bandS j).card : ℝ)
        + (((PK j).filter (fun n => ¬ bandLo j ≤ 2 * kIdx (gridAt j) n (goodAtom j))).card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not
      (s := PK j) (p := fun n => bandLo j ≤ 2 * kIdx (gridAt j) n (goodAtom j))
    have hb : bandS j = (PK j).filter (fun n => bandLo j ≤ 2 * kIdx (gridAt j) n (goodAtom j)) :=
      rfl
    rw [hb]
    exact_mod_cast this.symm
  have hdropR : ((((PK j).filter
      (fun n => ¬ bandLo j ≤ 2 * kIdx (gridAt j) n (goodAtom j))).card : ℕ) : ℝ)
      ≤ (((PK j).filter (fun n => n < M)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hdrop
  linarith

open Classical in
/-- The band keeps at least half the sample, at every scale (at `i = 0` it keeps all of it). -/
theorem card_bandS_ge' (i : ℕ) : ((PK i).card : ℝ) ≤ 2 * ((bandS i).card : ℝ) := by
  classical
  rcases i with _ | j
  · have hb : bandS 0 = PK 0 := by
      refine Finset.filter_true_of_mem fun n _ => ?_
      simp [bandLo]
    rw [hb]
    have : (0 : ℝ) ≤ ((PK 0).card : ℝ) := by positivity
    linarith
  · exact card_bandS_ge j

end NormalNumbers.G4.Sched
