/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyLevels
import NormalNumbers.G4EntropyScales

/-!
# Measuring the wall

`qForces_normal_iff_density_one` says a quantized sampler forces binary normality **iff** the
positions it reads have density one.  The implemented base-four schedule reads density `≤ 1/4`
(`card_isSampledAt_le`), so it does not — and `not_qForces_normal_of_levels` extends that to
every level function inside the budget.  A negative result's value is its constant, so this
module measures the gap.

* `quartic_le_gridB` — the schedule's own parameters (`N = 100K²`) give `100K⁴ ≤ B`; the bound
  `K³ ≤ B` used elsewhere is not tight.
* `density_le_pow` / `density_le_pow_real` — **the density of scale `i`'s own sampled positions
  is at most `⅛·(2/K⁶)^K`**, not merely `≤ 1/4`.  (The reflection's estimate was `½(3/K⁴)^K`;
  the schedule's `N` is quartic, not linear, so the true exponent is `K⁶`.)  Against the
  density **one** that `qForces_normal_iff_density_one` demands, this is the whole wall, in one
  number.
* `levelBudget_of_le_superpow`, `window_needed_ge`, `not_qForces_normal_at_superpow` — the same
  wall read as a window length: every level function reading fewer than `K^{4K}·m_K` digits per
  sampled time still lands under density `1/4`, so **a level function has to read `K^{4K}` times
  the implemented window `m_K` before the counting argument can even fail** — and failing it is
  only necessary, not sufficient.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy

/-! ### The schedule's `B` is quartic -/

/-- `100K⁴ ≤ B` at the schedule's `N = 100K²`.  (`cube_le_gridB` gives only `K³ ≤ B`, which
is what the earlier counting used; the schedule is far more generous than that.) -/
lemma quartic_le_gridB (K : ℕ) : 100 * K ^ 4 ≤ gridB K (N K) := by
  unfold gridB N
  nlinarith [Nat.zero_le (K ^ 3), Nat.zero_le K]

/-! ### The density of one scale's sampled positions -/

/-- **The wall, as a density.**  Scale `i` reads at most an `A_K/(8·(B²)^K)` fraction of the
positions below any `L`, where `A_K = (K²+1)^K`. -/
theorem density_le_pow (i L : ℕ) :
    8 * (gridB (KK i) (N (KK i)) ^ 2) ^ KK i
        * ((sampledPos (gridAt i) (X (KK i)) (kk i)).filter (fun j => j < L)).card
      ≤ (KK i ^ 2 + 1) ^ KK i * L := by
  set K := KK i with hK
  set m := kk i with hm
  set B := gridB K (N K) with hB
  set P := (B ^ 2) ^ K with hP
  set A := (K ^ 2 + 1) ^ K with hA
  have hKm : K = 4 * m := rfl
  have hmpos : 0 < m := by rw [hm]; unfold kk; omega
  have hBpos : 0 < B := by
    have h := quartic_le_gridB K
    have hKp : 0 < 100 * K ^ 4 := by
      have hK1 : 1 ≤ K := KK_one_le i
      positivity
    rw [hB]; omega
  have hPpos : 0 < P := Nat.pow_pos (Nat.pow_pos hBpos)
  have hcount := card_sampledPos_gridOf_le (K := K) (N := N K) (KK_one_le i) (X K) m L
  have hPK : P * K ≤ gridQ K (N K) * gridD₀ K (N K) :=
    pow_sq_gridB_mul_le K (KK_one_le i)
  have hden : 8 * P * m ≤ 2 * (1 + gridQ K (N K) * gridD₀ K (N K)) := by
    have h1 : 8 * P * m = 2 * (P * K) := by rw [hKm]; ring
    omega
  have hdivpos : 0 < 8 * P * m := by positivity
  have hdiv : L / (2 * (1 + gridQ K (N K) * gridD₀ K (N K))) ≤ L / (8 * P * m) :=
    Nat.div_le_div_left hden hdivpos
  have hfloor : 8 * P * m * (L / (8 * P * m)) ≤ L := Nat.mul_div_le L (8 * P * m)
  calc 8 * P * ((sampledPos (gridAt i) (X K) m).filter (fun j => j < L)).card
      ≤ 8 * P * (A * m * (L / (2 * (1 + gridQ K (N K) * gridD₀ K (N K))))) :=
        Nat.mul_le_mul_left _ hcount
    _ ≤ 8 * P * (A * m * (L / (8 * P * m))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdiv)
    _ = A * (8 * P * m * (L / (8 * P * m))) := by ring
    _ ≤ A * L := Nat.mul_le_mul_left _ hfloor

/-- **The wall, as a number.**  The positions scale `i` samples have density at most
`⅛·(2/K⁶)^K` — where `qForces_normal_iff_density_one` needs density **one**. -/
theorem density_le_pow_real (i L : ℕ) :
    (((sampledPos (gridAt i) (X (KK i)) (kk i)).filter (fun j => j < L)).card : ℝ)
      ≤ (1 / 8 : ℝ) * (2 / (KK i : ℝ) ^ 6) ^ KK i * (L : ℝ) := by
  set K := KK i with hK
  set B := gridB K (N K) with hB
  have hK1 : 1 ≤ K := KK_one_le i
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hBq : 100 * K ^ 4 ≤ B := quartic_le_gridB K
  have hBpos : 0 < B := by
    have : 0 < K ^ 4 := Nat.pow_pos (by omega)
    omega
  -- the key natural-number comparison `A·K^{6K} ≤ 2^K·(B²)^K`
  have hstep : (K ^ 2 + 1) * K ^ 6 ≤ 2 * B ^ 2 := by
    have h1 : (100 * K ^ 4) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hBq 2
    have h2 : (100 * K ^ 4) ^ 2 = 10000 * K ^ 8 := by ring
    have h3 : (K ^ 2 + 1) * K ^ 6 = K ^ 8 + K ^ 6 := by ring
    have h4 : K ^ 6 ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by omega)
    omega
  have hpow : ((K ^ 2 + 1) ^ K) * (K ^ 6) ^ K ≤ 2 ^ K * (B ^ 2) ^ K := by
    have := Nat.pow_le_pow_left hstep K
    calc ((K ^ 2 + 1) ^ K) * (K ^ 6) ^ K = ((K ^ 2 + 1) * K ^ 6) ^ K := by rw [mul_pow]
      _ ≤ (2 * B ^ 2) ^ K := this
      _ = 2 ^ K * (B ^ 2) ^ K := by rw [mul_pow]
  -- transport to `ℝ`
  have hnat := density_le_pow i L
  have hPR : (0 : ℝ) < (((B ^ 2) ^ K : ℕ) : ℝ) := by
    have : 0 < (B ^ 2) ^ K := Nat.pow_pos (Nat.pow_pos hBpos)
    exact_mod_cast this
  have hR : 8 * (((B ^ 2) ^ K : ℕ) : ℝ)
      * ((((sampledPos (gridAt i) (X K) (kk i)).filter (fun j => j < L)).card : ℕ) : ℝ)
      ≤ (((K ^ 2 + 1) ^ K : ℕ) : ℝ) * (L : ℝ) := by exact_mod_cast hnat
  have hpowR : (((K ^ 2 + 1) ^ K : ℕ) : ℝ) * ((K : ℝ) ^ 6) ^ K
      ≤ (2 : ℝ) ^ K * (((B ^ 2) ^ K : ℕ) : ℝ) := by
    have := hpow
    have hc : (((K ^ 2 + 1) ^ K * (K ^ 6) ^ K : ℕ) : ℝ) ≤ ((2 ^ K * (B ^ 2) ^ K : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc
    push_cast
    linarith [hc]
  have hKpow : (0 : ℝ) < ((K : ℝ) ^ 6) ^ K := by positivity
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  -- `8·P·card ≤ A·L` and `A·K^{6K} ≤ 2^K·P` give `8·card·K^{6K} ≤ 2^K·L`
  have e1 := mul_le_mul_of_nonneg_right hR hKpow.le
  have e2 := mul_le_mul_of_nonneg_right hpowR hLnn
  have e3 : (((B ^ 2) ^ K : ℕ) : ℝ)
      * (((((sampledPos (gridAt i) (X K) (kk i)).filter (fun j => j < L)).card : ℕ) : ℝ)
        * (8 * ((K : ℝ) ^ 6) ^ K))
      ≤ (((B ^ 2) ^ K : ℕ) : ℝ) * ((2 : ℝ) ^ K * (L : ℝ)) := by nlinarith [e1, e2]
  have hfinal := le_of_mul_le_mul_left e3 hPR
  have hgoal : (2 / (K : ℝ) ^ 6) ^ K = (2 : ℝ) ^ K / ((K : ℝ) ^ 6) ^ K := by
    rw [div_pow]
  rw [hgoal, show (1 / 8 : ℝ) * ((2 : ℝ) ^ K / ((K : ℝ) ^ 6) ^ K) * (L : ℝ)
      = ((2 : ℝ) ^ K * (L : ℝ)) / (8 * ((K : ℝ) ^ 6) ^ K) by field_simp,
    le_div_iff₀ (by positivity)]
  exact hfinal

/-! ### The wall as a window length -/

/-- **Every level function below `K^{4K}·m_K` still respects the budget.**  The implemented
schedule reads `m_K = K/4`; a level function must multiply that by `K^{4K}` before the counting
argument can fail at all. -/
theorem levelBudget_of_le_superpow {mm : ℕ → ℕ}
    (h : ∀ i, mm i ≤ KK i ^ (4 * KK i) * kk i) : LevelBudget mm := by
  refine levelBudget_of_le_pow fun i => ?_
  set K := KK i with hK
  have hK1 : 1 ≤ K := KK_one_le i
  have hBq : 100 * K ^ 4 ≤ gridB K (N K) := quartic_le_gridB K
  have h1 : (100 * K ^ 4) ^ K ≤ gridB K (N K) ^ K := Nat.pow_le_pow_left hBq K
  have h2 : (100 * K ^ 4) ^ K = 100 ^ K * (K ^ (4 * K)) := by
    rw [mul_pow, ← pow_mul]
  have h3 : kk i ≤ 100 ^ K := by
    have hkk : kk i ≤ K := by rw [hK]; unfold KK; omega
    have : K < 100 ^ K := Nat.lt_pow_self (by norm_num)
    omega
  have h4 : K ^ (4 * K) * kk i ≤ K ^ (4 * K) * 100 ^ K := Nat.mul_le_mul_left _ h3
  calc mm i ≤ K ^ (4 * K) * kk i := h i
    _ ≤ K ^ (4 * K) * 100 ^ K := h4
    _ = (100 * K ^ 4) ^ K := by rw [h2]; ring
    _ ≤ gridB K (N K) ^ K := h1

/-- **The wall, as a window length.**  If the positions a level function reads ever exceed
density `1/4`, some scale must already be reading at least `K^{4K}·m_K` binary digits per
sampled time — `K^{4K}` times the implemented window. -/
theorem window_needed_ge {mm : ℕ → ℕ} {L : ℕ}
    (hdense : L / 4 < ((Finset.range L).filter (IsSampledAt mm)).card) :
    ∃ i, KK i ^ (4 * KK i) * kk i < mm i := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  exact absurd (card_isSampledAt_le (levelBudget_of_le_superpow hcon) L) (by omega)

/-- **The concrete statement.**  Even reading `K^{4K}·m_K` binary digits at every sampled time,
no satisfiable hypothesis about the quantized sample values implies binary normality.  This is
`not_qForces_normal_at_pow` with the schedule's quartic `B` spent, and it is the sharpest form
of "normality of `G₄` is closed on this mechanism". -/
theorem not_qForces_normal_at_superpow :
    ¬ ∃ P : ℝ → Prop,
        (∀ x y : ℝ,
          qVal (schedWAt (fun i => KK i ^ (4 * KK i) * kk i)) x
            = qVal (schedWAt (fun i => KK i ^ (4 * KK i) * kk i)) y → P x → P y)
        ∧ (∃ x : ℝ, P x)
        ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) :=
  not_qForces_normal_of_levels (levelBudget_of_le_superpow (fun _ => le_rfl))

end NormalNumbers.G4.Sched
