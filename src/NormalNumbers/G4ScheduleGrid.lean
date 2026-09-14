/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FarTail

/-!
# G4 §5: the explicit grid — `GridParams` from `(K, N)`, and every size bound

The §5 schedule needs one concrete `GridParams` for each `(K, N)`, together with explicit
sizes for the quantities the four remaining witness inequalities see: `Dm ≥ every d_α`,
`Mx ≥ every n + ρ_i`, and above all the progression modulus `P₀`, which controls the sample
size `|P| ≈ X/P₀` and hence `farC`, `hbig`, `hbudget`.

* `gridOf K N` — `s = K²`, `B = K²(K+N) + 1`, `U = K² ∑_{i<K} B^{i+1}` (the `gridU_le` bound),
  `D₀ = K·U` (the `gridV_le` bound), and **`Q = (U + K + N + 2)!`**: every `m ≤ U` divides `Q`
  by `Nat.dvd_factorial`, and `K + N < Q`, `1 < Q` are `Nat.self_le_factorial`.  No `lcm`.
* `gridDm K N = 1 + Q(D₀ + U)` bounds every multiplier `d_α`;
  `(K+N)·gridDm` bounds every shift `ρ_i`.
* **`P₀_le_gridP₀Bound`**: `P₀ ≤ Dm^{2H} · (2T+1)^{2T+1} · ((K+N)Dm)^{T²}`, `H = (K²+1)^K`,
  `T = H·N` — the three factors are the CRT modulus `∏ d_α²`, the primorial of `2T`, and the
  shift differences.  Everything is a natural number; the real-log asymptotics live in the
  schedule module.
-/

open Finset
open scoped BigOperators Nat

namespace NormalNumbers.G4

/-- `∑_{i<K} B^{i+1}`. -/
def gridSum (K B : ℕ) : ℕ := ∑ i : Fin K, B ^ ((i : ℕ) + 1)

/-- `B = K²(K+N) + 1`. -/
def gridB (K N : ℕ) : ℕ := K ^ 2 * (K + N) + 1

/-- `U = K² ∑ B^{i+1}`, an upper bound for every `u_α`. -/
def gridUmax (K N : ℕ) : ℕ := K ^ 2 * gridSum K (gridB K N)

/-- `D₀ = K·U`, an upper bound for every `v_α`. -/
def gridD₀ (K N : ℕ) : ℕ := K * gridUmax K N

/-- `Q = (U + K + N + 2)!`. -/
def gridQ (K N : ℕ) : ℕ := (gridUmax K N + K + N + 2)!

lemma gridQ_gt (K N : ℕ) : gridUmax K N + K + N + 2 ≤ gridQ K N := Nat.self_le_factorial _

/-- **The explicit grid parameters.** -/
def gridOf (K N : ℕ) (hK : 1 ≤ K) : GridParams where
  K := K
  s := K ^ 2
  B := gridB K N
  Q := gridQ K N
  D₀ := gridD₀ K N
  N := N
  U := gridUmax K N
  hB := by unfold gridB; omega
  hsB := by
    unfold gridB
    have : K ^ 2 ≤ K ^ 2 * (K + N) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  hJQ := by have := gridQ_gt K N; omega
  hQ := by have := gridQ_gt K N; omega
  hD := fun α => by
    have := gridV_le (K := K) (s := K ^ 2) (gridB K N) α
    unfold gridD₀ gridUmax gridSum
    simpa [mul_assoc] using this
  hU := fun α => by
    have := gridU_le (K := K) (s := K ^ 2) (gridB K N) α
    unfold gridUmax gridSum
    exact this
  hQdvd := fun m hm hmU => Nat.dvd_factorial hm (by omega)

namespace gridOf

variable {K N : ℕ} (hK : 1 ≤ K)

@[simp] lemma K_eq : (gridOf K N hK).K = K := rfl
@[simp] lemma s_eq : (gridOf K N hK).s = K ^ 2 := rfl
@[simp] lemma N_eq : (gridOf K N hK).N = N := rfl
@[simp] lemma B_eq : (gridOf K N hK).B = gridB K N := rfl
@[simp] lemma Q_eq : (gridOf K N hK).Q = gridQ K N := rfl
@[simp] lemma D₀_eq : (gridOf K N hK).D₀ = gridD₀ K N := rfl
@[simp] lemma U_eq : (gridOf K N hK).U = gridUmax K N := rfl

lemma rDim_eq : (gridOf K N hK).rDim = (K ^ 2) ^ K := rfl
lemma hDim_eq : (gridOf K N hK).hDim = (K ^ 2 + 1) ^ K := rfl

lemma card_Idx : Fintype.card (gridOf K N hK).Idx = (K ^ 2 + 1) ^ K * N := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; rfl

end gridOf

/-! ### Size bounds -/

/-- `Dm = 1 + Q(D₀ + U)`, an upper bound for every `d_α`. -/
def gridDm (K N : ℕ) : ℕ := 1 + gridQ K N * (gridD₀ K N + gridUmax K N)

lemma gridDm_pos (K N : ℕ) : 0 < gridDm K N := by unfold gridDm; omega

namespace gridOf

variable {K N : ℕ} (hK : 1 ≤ K)

lemma d_le (α : (gridOf K N hK).Atom) : (gridOf K N hK).d α ≤ gridDm K N := by
  unfold GridParams.d mult gridDm
  have hU : gridU (gridB K N) α ≤ gridUmax K N := (gridOf K N hK).hU α
  simp only [B_eq, Q_eq, D₀_eq]
  have h2 : gridD₀ K N + gridU (gridB K N) α ≤ gridD₀ K N + gridUmax K N := by omega
  have := Nat.mul_le_mul_left (gridQ K N) h2
  omega

lemma shiftAL_le (i : (gridOf K N hK).Idx) :
    shiftAL (gridOf K N hK).B (gridOf K N hK).Q (gridOf K N hK).D₀ i ≤ (K + N) * gridDm K N := by
  unfold shiftAL shiftG
  refine (Nat.sub_le _ _).trans ?_
  have h1 : layer K i.2 ≤ K + N := layer_le K i.2
  have h2 : mult (gridOf K N hK).B (gridOf K N hK).Q (gridOf K N hK).D₀ i.1 ≤ gridDm K N :=
    d_le hK i.1
  exact Nat.mul_le_mul h1 h2

/-- The `Mx` bound: every sample point plus every shift is at most `X + (K+N)·Dm`. -/
lemma add_shiftAL_le {X : ℕ} {n : ℕ} (hn : n ∈ apSample X (gridOf K N hK).P₀ (gridOf K N hK).b₀)
    (i : (gridOf K N hK).Idx) :
    n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q (gridOf K N hK).D₀ i
      ≤ X + (K + N) * gridDm K N := by
  have hnX : n < X := Finset.mem_range.1 (Finset.mem_filter.1 hn).1
  have := shiftAL_le hK i
  omega

end gridOf

/-! ### The modulus `P₀` -/

/-- `H = (K²+1)^K`. -/
def gridH (K : ℕ) : ℕ := (K ^ 2 + 1) ^ K

/-- `T = H·N = |Idx|`. -/
def gridT (K N : ℕ) : ℕ := gridH K * N

/-- **The explicit bound on the progression modulus**:
`Dm^{2H} · (2T+1)^{2T+1} · ((K+N)·Dm)^{T²}`. -/
def gridP₀Bound (K N : ℕ) : ℕ :=
  gridDm K N ^ (2 * gridH K) * (2 * gridT K N + 1) ^ (2 * gridT K N + 1)
    * ((K + N) * gridDm K N) ^ (gridT K N ^ 2)

namespace gridOf

variable {K N : ℕ} (hK : 1 ≤ K)

lemma Mprod_le : (gridOf K N hK).Mprod ≤ gridDm K N ^ (2 * gridH K) := by
  unfold GridParams.Mprod
  calc ∏ α : (gridOf K N hK).Atom, (gridOf K N hK).d α ^ 2
      ≤ ∏ _α : (gridOf K N hK).Atom, gridDm K N ^ 2 :=
        Finset.prod_le_prod' fun α _ => Nat.pow_le_pow_left (d_le hK α) 2
    _ = (gridDm K N ^ 2) ^ Fintype.card (gridOf K N hK).Atom := by
        rw [Finset.prod_const, Finset.card_univ]
    _ = gridDm K N ^ (2 * gridH K) := by
        rw [(gridOf K N hK).card_atom, hDim_eq, ← pow_mul, gridH, mul_comm]

lemma primorial_le :
    (∏ p ∈ (2 * Fintype.card (gridOf K N hK).Idx + 1).primesBelow, p)
      ≤ (2 * gridT K N + 1) ^ (2 * gridT K N + 1) := by
  rw [card_Idx]
  set T := (K ^ 2 + 1) ^ K * N
  have hT : gridT K N = T := rfl
  rw [hT]
  calc (∏ p ∈ (2 * T + 1).primesBelow, p)
      ≤ ∏ _p ∈ (2 * T + 1).primesBelow, (2 * T + 1) :=
        Finset.prod_le_prod' fun p hp => (Nat.mem_primesBelow.1 hp).1.le
    _ = (2 * T + 1) ^ (2 * T + 1).primesBelow.card := Finset.prod_const _
    _ ≤ (2 * T + 1) ^ (2 * T + 1) := by
        apply Nat.pow_le_pow_right (by omega)
        calc (2 * T + 1).primesBelow.card ≤ (Finset.range (2 * T + 1)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 * T + 1 := Finset.card_range _

lemma ρ_le (i : (gridOf K N hK).Idx) : (gridOf K N hK).ρ i ≤ (K + N) * gridDm K N :=
  shiftAL_le hK i

lemma distProd_le :
    (∏ i : (gridOf K N hK).Idx, ∏ i' : (gridOf K N hK).Idx,
        (if i = i' then 1 else Nat.dist ((gridOf K N hK).ρ i) ((gridOf K N hK).ρ i')))
      ≤ ((K + N) * gridDm K N) ^ (gridT K N ^ 2) := by
  have hDm := gridDm_pos K N
  have hM : 1 ≤ (K + N) * gridDm K N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hle : ∀ i i' : (gridOf K N hK).Idx,
      (if i = i' then 1 else Nat.dist ((gridOf K N hK).ρ i) ((gridOf K N hK).ρ i'))
        ≤ (K + N) * gridDm K N := by
    intro i i'
    split_ifs
    · exact hM
    · unfold Nat.dist
      have := ρ_le hK i
      have := ρ_le hK i'
      omega
  calc (∏ i : (gridOf K N hK).Idx, ∏ i' : (gridOf K N hK).Idx,
        (if i = i' then 1 else Nat.dist ((gridOf K N hK).ρ i) ((gridOf K N hK).ρ i')))
      ≤ ∏ _i : (gridOf K N hK).Idx, ∏ _i' : (gridOf K N hK).Idx, (K + N) * gridDm K N :=
        Finset.prod_le_prod' fun i _ => Finset.prod_le_prod' fun i' _ => hle i i'
    _ = ((K + N) * gridDm K N) ^ (gridT K N ^ 2) := by
        simp only [Finset.prod_const, Finset.card_univ, card_Idx, ← pow_mul]
        congr 1
        rw [gridT, gridH]; ring

/-- **`P₀ ≤ gridP₀Bound K N`.** -/
theorem P₀_le : (gridOf K N hK).P₀ ≤ gridP₀Bound K N := by
  unfold GridParams.P₀ GridParams.freezeQ gridP₀Bound
  rw [mul_assoc]
  exact Nat.mul_le_mul (Mprod_le hK) (Nat.mul_le_mul (primorial_le hK) (distProd_le hK))

end gridOf

/-! ### The sample size -/

/-- `|{n < X : n ≡ a (P₀)}| ≥ X/P₀ − 1`. -/
lemma card_apSample_ge (X P₀ a : ℕ) (hP₀ : 0 < P₀) (ha : a < P₀) :
    (X : ℝ) / P₀ - 1 ≤ ((apSample X P₀ a).card : ℝ) := by
  rw [apSample_eq_filter_modEq X P₀ a ha]
  have := abs_card_filter_modEq_sub_le X P₀ a hP₀
  rw [abs_le] at this
  linarith [this.1]

/-- The same, at most `X/P₀ + 1`. -/
lemma card_apSample_le (X P₀ a : ℕ) (hP₀ : 0 < P₀) (ha : a < P₀) :
    ((apSample X P₀ a).card : ℝ) ≤ (X : ℝ) / P₀ + 1 := by
  rw [apSample_eq_filter_modEq X P₀ a ha]
  have := abs_card_filter_modEq_sub_le X P₀ a hP₀
  rw [abs_le] at this
  linarith [this.2]

/-- The sample is nonempty as soon as `P₀ < X` (indeed `2P₀ ≤ X` suffices for the real bound). -/
lemma apSample_nonempty_of_le (X P₀ a : ℕ) (hP₀ : 0 < P₀) (ha : a < P₀) (hX : 2 * P₀ ≤ X) :
    (apSample X P₀ a).Nonempty := by
  rw [← Finset.card_pos]
  have h := card_apSample_ge X P₀ a hP₀ ha
  have hP : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hX' : (2 : ℝ) * P₀ ≤ X := by exact_mod_cast hX
  have : (1 : ℝ) ≤ (X : ℝ) / P₀ - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hP]; linarith
  have : (0 : ℝ) < (apSample X P₀ a).card := by linarith
  exact_mod_cast this

end NormalNumbers.G4
