/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPrecision

/-!
# Raising the quantization level does not repair the schedule

`qForces_normal_iff_density_one` (lap 20) reduces every quantized sampler to one number: the
density of the union of its windows.  The implemented schedule reads windows of length
`m_K = K/4` at the times `2·kIdx`, and that union has density `≤ 1/4`.  The obvious remaining
question is whether *longer* windows would help — the times stay where they are, but each one
reads more digits.

They would have to be astronomically longer, and even then: this module redoes the density count
with an arbitrary level function `mm : ℕ → ℕ`, under the single budget inequality

  `2^{i+3} · H_i · mm i ≤ 2 · d_min(i)`     (`LevelBudget`)

which is the same inequality `key_size` proves for `mm = kk`.  Under it the sampled positions
still have density `≤ 1/4` (`card_isSampledAt_le`), so by lap 20 no hypothesis about the sample
values forces normality (`not_qForces_normal_of_levels`).

Since `d_min(i) = 1 + Q·D₀` with `Q = (U + K + N + 2)!`, the budget leaves room for level
functions vastly beyond `K/4`; making that quantitative is the next step.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy

/-- The budget a level function must respect for the schedule's own counting argument. -/
def LevelBudget (mm : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, 2 ^ (i + 3) * ((KK i ^ 2 + 1) ^ KK i * mm i) ≤ 2 * dmin i

lemma levelBudget_kk : LevelBudget kk := fun i => key_size i

/-- A digit position read by some scale, at level `mm`. -/
def IsSampledAt (mm : ℕ → ℕ) (j : ℕ) : Prop :=
  ∃ i, j ∈ sampledPos (gridAt i) (X (KK i)) (mm i)

noncomputable instance (mm : ℕ → ℕ) : DecidablePred (IsSampledAt mm) := Classical.decPred _

/-- Scale `i` never puts a position at or below `i`, at any level. -/
theorem lt_of_mem_sampledPos_level {i m j : ℕ}
    (hj : j ∈ sampledPos (gridAt i) (X (KK i)) m) : i < j := by
  obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (gridAt i)).1 hj
  have hd : (gridAt i).d α ≤ kIdx (gridAt i) n α :=
    kIdx_ge_d (gridAt i) (gridOf_t_nonconstant (KK_one_le i)) hn α
  have hdm : dmin i ≤ (gridAt i).d α := dmin_le_d i α
  have hiQ : i ≤ gridQ (KK i) (N (KK i)) := by
    have h1 := gridQ_gt (KK i) (N (KK i))
    have h2 : i ≤ KK i := by unfold KK kk; omega
    omega
  have hD1 : 1 ≤ gridD₀ (KK i) (N (KK i)) := one_le_gridD₀ (KK_one_le i)
  have hiD : i ≤ gridQ (KK i) (N (KK i)) * gridD₀ (KK i) (N (KK i)) :=
    le_trans hiQ (Nat.le_mul_of_pos_right _ hD1)
  have : i < dmin i := by unfold dmin; omega
  omega

/-- **Scale `i` contributes at most `L/2^{i+3}` positions below `L`, at any budgeted level.** -/
theorem card_sampledPos_level_lt_le {mm : ℕ → ℕ} (hb : LevelBudget mm) (i L : ℕ) :
    ((sampledPos (gridAt i) (X (KK i)) (mm i)).filter (fun j => j < L)).card
      ≤ L / 2 ^ (i + 3) := by
  rcases Nat.eq_zero_or_pos (mm i) with hm | hm
  · have : sampledPos (gridAt i) (X (KK i)) (mm i) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
      obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (gridAt i)).1 hj
      omega
    rw [this]
    simp
  have hApos : 0 < (KK i ^ 2 + 1) ^ KK i * mm i :=
    Nat.mul_pos (pow_pos (by omega) _) hm
  have h2pos : 0 < 2 ^ (i + 3) := pow_pos (by omega) _
  have hkey : (KK i ^ 2 + 1) ^ KK i * mm i * 2 ^ (i + 3) ≤ 2 * dmin i := by
    have hk := hb i
    calc (KK i ^ 2 + 1) ^ KK i * mm i * 2 ^ (i + 3)
        = 2 ^ (i + 3) * ((KK i ^ 2 + 1) ^ KK i * mm i) := by ring
      _ ≤ 2 * dmin i := hk
  have hdiv : L / (2 * dmin i) ≤ L / ((KK i ^ 2 + 1) ^ KK i * mm i * 2 ^ (i + 3)) :=
    Nat.div_le_div_left hkey (Nat.mul_pos hApos h2pos)
  have hcount : ((sampledPos (gridAt i) (X (KK i)) (mm i)).filter (fun j => j < L)).card
      ≤ (KK i ^ 2 + 1) ^ KK i * mm i * (L / (2 * dmin i)) :=
    card_sampledPos_gridOf_le (KK_one_le i) (X (KK i)) (mm i) L
  calc ((sampledPos (gridAt i) (X (KK i)) (mm i)).filter (fun j => j < L)).card
      ≤ (KK i ^ 2 + 1) ^ KK i * mm i * (L / (2 * dmin i)) := hcount
    _ ≤ (KK i ^ 2 + 1) ^ KK i * mm i
          * (L / ((KK i ^ 2 + 1) ^ KK i * mm i * 2 ^ (i + 3))) := Nat.mul_le_mul_left _ hdiv
    _ ≤ L / 2 ^ (i + 3) := mul_div_mul_le _ _ _

/-- **Density `≤ 1/4` at any budgeted level function.** -/
theorem card_isSampledAt_le {mm : ℕ → ℕ} (hb : LevelBudget mm) (L : ℕ) :
    ((Finset.range L).filter (IsSampledAt mm)).card ≤ L / 4 := by
  have hsub : (Finset.range L).filter (IsSampledAt mm)
      ⊆ (Finset.range L).biUnion
        (fun i => (sampledPos (gridAt i) (X (KK i)) (mm i)).filter (fun j => j < L)) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjL, i, hji⟩ := hj
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 ?_, Finset.mem_filter.2 ⟨hji, hjL⟩⟩
    exact lt_trans (lt_of_mem_sampledPos_level hji) hjL
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum fun i _ => card_sampledPos_level_lt_le hb i L) ?_
  have hrw : ∀ i ∈ Finset.range L, L / 2 ^ (i + 3) = (L / 8) / 2 ^ i := by
    intro i _
    rw [Nat.div_div_eq_div_mul, pow_add]
    ring_nf
  rw [Finset.sum_congr rfl hrw]
  have h := sum_div_two_pow_le L (L / 8)
  have h8 : 8 * (L / 8) ≤ L := Nat.mul_div_le L 8
  have h4 : 2 * (L / 8) ≤ L / 4 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  omega

theorem card_isSampledAt_le_real {mm : ℕ → ℕ} (hb : LevelBudget mm) (L : ℕ) :
    ((((Finset.range L).filter (IsSampledAt mm)).card : ℝ)) ≤ (1 / 4 : ℝ) * L := by
  have h := card_isSampledAt_le hb L
  have h4 : 4 * (((Finset.range L).filter (IsSampledAt mm)).card) ≤ L := by
    have := Nat.mul_le_mul_left 4 h
    have h2 : 4 * (L / 4) ≤ L := Nat.mul_div_le L 4
    omega
  have : (4 : ℝ) * ((((Finset.range L).filter (IsSampledAt mm)).card : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast h4
  linarith

/-! ### Through the diagonal theorem -/

/-- The schedule's `(time, level)` family at an arbitrary level function. -/
noncomputable def schedWAt (mm : ℕ → ℕ) : SchedIdx → ℕ × ℕ :=
  fun z => (2 * kIdx (gridAt z.1) z.2.1.1 z.2.2, mm z.1)

lemma qRead_schedWAt_iff (mm : ℕ → ℕ) (j : ℕ) :
    qRead (schedWAt mm) j ↔ IsSampledAt mm j := by
  constructor
  · rintro ⟨⟨i, n, α⟩, h1, h2⟩
    exact ⟨i, (mem_sampledPos (gridAt i)).2
      ⟨n.1, n.2, α, j - 2 * kIdx (gridAt i) n.1 α, by
        simp only [schedWAt] at h1 h2; omega, by
        simp only [schedWAt] at h1 h2; omega⟩⟩
  · rintro ⟨i, hj⟩
    obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (gridAt i)).1 hj
    exact ⟨⟨i, ⟨n, hn⟩, α⟩, by simp only [schedWAt]; omega, by simp only [schedWAt]; omega⟩

/-- **Longer windows do not repair the schedule.**  At *any* level function respecting the
budget, no satisfiable hypothesis about the quantized sample values implies binary normality. -/
theorem not_qForces_normal_of_levels {mm : ℕ → ℕ} (hb : LevelBudget mm) :
    ¬ ∃ P : ℝ → Prop,
        (∀ x y : ℝ, qVal (schedWAt mm) x = qVal (schedWAt mm) y → P x → P y)
        ∧ (∃ x : ℝ, P x)
        ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) := by
  intro h
  have hdens := (qForces_normal_iff_density_one (schedWAt mm)).1 h
  have hset : ∀ L : ℕ, (Finset.range L).filter (qRead (schedWAt mm))
      = (Finset.range L).filter (IsSampledAt mm) := by
    intro L
    apply Finset.filter_congr
    intro j _
    simpa using qRead_schedWAt_iff mm j
  have hev : ∀ᶠ L : ℕ in atTop,
      ((((Finset.range L).filter (qRead (schedWAt mm))).card : ℝ)) / L ≤ 1 / 4 := by
    filter_upwards [Filter.eventually_gt_atTop 0] with L hL
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    rw [div_le_iff₀ hLR, hset L]
    exact card_isSampledAt_le_real hb L
  have := le_of_tendsto hdens hev
  linarith


/-! ### The budget is astronomically generous -/

/-- `2(K²+1) ≤ B` for the schedule's `B = K²(K+N)+1`, at the schedule's scales. -/
lemma two_mul_succ_le_gridB {K N : ℕ} (hK : 3 ≤ K) : 2 * (K ^ 2 + 1) ≤ gridB K N := by
  unfold gridB
  have h1 : K ^ 2 * K ≤ K ^ 2 * (K + N) := Nat.mul_le_mul_left _ (by omega)
  nlinarith [sq_nonneg K]

/-- The size inequality behind `key_size`, isolated: `(B²)^K·K ≤ Q·D₀`. -/
lemma pow_sq_gridB_mul_le (K : ℕ) (hK : 1 ≤ K) :
    (gridB K (N K) ^ 2) ^ K * K ≤ gridQ K (N K) * gridD₀ K (N K) := by
  have hU : gridB K (N K) ^ K ≤ gridUmax K (N K) := pow_le_gridUmax hK
  have hQ : gridUmax K (N K) ≤ gridQ K (N K) := by
    have := gridQ_gt K (N K); omega
  have hD : gridD₀ K (N K) = K * gridUmax K (N K) := rfl
  have h1 : gridB K (N K) ^ K * (K * gridB K (N K) ^ K)
      ≤ gridUmax K (N K) * (K * gridUmax K (N K)) :=
    Nat.mul_le_mul hU (Nat.mul_le_mul_left _ hU)
  have h2 : (gridB K (N K) ^ 2) ^ K * K
      = gridB K (N K) ^ K * (K * gridB K (N K) ^ K) := by
    rw [← pow_mul, mul_comm 2 K, pow_mul]
    ring
  rw [h2, hD]
  exact le_trans h1 (Nat.mul_le_mul_right _ hQ)

/-- **The budget admits every level function below `B^K`.**  At scale `i` the schedule reads
`m = K/4` digits per window; the counting argument survives up to `B^K ≥ K^{3K}` digits — and
it is the *density*, by `qForces_normal_iff_density_one`, that decides everything.  So no
enlargement of the windows within this astronomical range changes the verdict. -/
theorem levelBudget_of_le_pow {mm : ℕ → ℕ}
    (h : ∀ i, mm i ≤ gridB (KK i) (N (KK i)) ^ KK i) : LevelBudget mm := by
  intro i
  set K := KK i with hK
  set B := gridB K (N K) with hB
  have hK12 : 12 ≤ K := by have := KK_ge i; omega
  have hi3 : i + 3 ≤ K := by rw [hK]; unfold KK kk; omega
  have hpow : 2 ^ (i + 3) ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hi3
  have hL : 2 ^ (i + 3) * ((K ^ 2 + 1) ^ K * mm i) ≤ (2 * (K ^ 2 + 1) * B) ^ K := by
    calc 2 ^ (i + 3) * ((K ^ 2 + 1) ^ K * mm i)
        ≤ 2 ^ K * ((K ^ 2 + 1) ^ K * B ^ K) :=
          Nat.mul_le_mul hpow (Nat.mul_le_mul_left _ (h i))
      _ = (2 * (K ^ 2 + 1) * B) ^ K := by rw [mul_pow, mul_pow]; ring
  have hBB : 2 * (K ^ 2 + 1) * B ≤ B ^ 2 := by
    have := two_mul_succ_le_gridB (K := K) (N := N K) (by omega)
    calc 2 * (K ^ 2 + 1) * B ≤ B * B := Nat.mul_le_mul_right _ this
      _ = B ^ 2 := by ring
  have hchain : (2 * (K ^ 2 + 1) * B) ^ K ≤ (B ^ 2) ^ K := Nat.pow_le_pow_left hBB K
  have hR : (B ^ 2) ^ K * K ≤ gridQ K (N K) * gridD₀ K (N K) :=
    pow_sq_gridB_mul_le K (by omega)
  have hK1 : (B ^ 2) ^ K ≤ (B ^ 2) ^ K * K := Nat.le_mul_of_pos_right _ (by omega)
  calc 2 ^ (i + 3) * ((K ^ 2 + 1) ^ K * mm i)
      ≤ (2 * (K ^ 2 + 1) * B) ^ K := hL
    _ ≤ (B ^ 2) ^ K := hchain
    _ ≤ (B ^ 2) ^ K * K := hK1
    _ ≤ gridQ K (N K) * gridD₀ K (N K) := hR
    _ ≤ 2 * dmin i := by unfold dmin; rw [← hK]; omega

/-- **The concrete statement.**  Even reading `B^K ≥ K^{3K}` binary digits at every sampled time
— against the schedule's actual `K/4` — no hypothesis about the quantized sample implies binary
normality. -/
theorem not_qForces_normal_at_pow :
    ¬ ∃ P : ℝ → Prop,
        (∀ x y : ℝ,
          qVal (schedWAt (fun i => gridB (KK i) (N (KK i)) ^ KK i)) x
            = qVal (schedWAt (fun i => gridB (KK i) (N (KK i)) ^ KK i)) y → P x → P y)
        ∧ (∃ x : ℝ, P x)
        ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) :=
  not_qForces_normal_of_levels (levelBudget_of_le_pow (fun _ => le_rfl))

end NormalNumbers.G4.Sched
