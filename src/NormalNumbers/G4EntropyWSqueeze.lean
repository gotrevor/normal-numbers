/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWMediant
import NormalNumbers.G4EntropyWCap

/-!
# The mid-band squeeze — the read ratio at an ARBITRARY read index

`tendsto_fullWRead_freq` controls the read ratio at the band cutoffs `fTW (i+1)`.
`IsNormalSequence 2` quantifies over **all** `n`, so what is owed is the ratio at an arbitrary
read index `n`, uniformly in the band.

Fix a band `j ≥ 1`, write `T := fTW j`, `s := n − T`, `a := s / kk j`, `G := winCount v T` and
`D := winCount v n − G`.  Three ingredients close it.

* **The mediant** (`G4EntropyWMediant`): deviations of `G` from `r·T` and of `D` from `r·s` simply
  add, so `|(G+D)/(T+s) − r| ≤ (|G − rT| + |D − rs|)/(T+s)`.
* **The gated branch.**  With `c := fnthW j (a−1)`, `aLe_fnthW` says the position cutoff `c`
  consumes exactly `a` windows, and `abs_prefix_ratio_sub_le_cap` certifies the prefix count
  `fullGoodWPre j a` against `a·F`, `F = kk j − ℓ + 1`.  The increment `D` differs from
  `fullGoodWPre j a` by at most `a·ℓ + kk j` (word boundaries plus the partial window), and `a·F`
  differs from `s` by at most `kk j + a·ℓ`, so `|D − r·s| ≤ δ_j·s + 2(kk j + a·ℓ)`.
* **The ungated branch.**  `aLe_le_headW` bounds `a` by `headW j`, and `head_frac_tiny` says
  `headW j · kk j · KK j ≤ T`.  So `s < (a+1)·kk j ≤ 2T/KK j` and the *trivial* bound `0 ≤ D ≤ s`
  already gives `|(G+D)/(T+s) − r| ≤ |G/T − r| + 2/KK j`.

The same `head_frac_tiny`, at `a = 1`, gives the sharper fact that drives everything:
**`kk j · KK j ≤ fTW j`** (`kk_mul_KK_le_fTW`) — one window is a `1/KK j` fraction of the history.

Endpoint: `abs_ratio_mid_le`, then `tendsto_winCount_fullDigW` at **every** `n`, then
`IsNormalSequence 2 (fullDigW (primeLambertAtBase 4))`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### `winCount` is monotone -/

lemma winCount_mono (s : ℕ → ℕ) (v : List ℕ) {m n : ℕ} (h : m ≤ n) :
    winCount s v m ≤ winCount s v n := by
  rw [winCount_split s v h]; omega

lemma winCount_sub_le (s : ℕ → ℕ) (v : List ℕ) {m n : ℕ} (h : m ≤ n) :
    winCount s v n ≤ winCount s v m + (n - m) := by
  rw [winCount_split s v h]
  have : ((Finset.Ico m n).filter (MatchesAt s v)).card ≤ (Finset.Ico m n).card :=
    Finset.card_filter_le _ _
  simp only [Nat.card_Ico] at this
  omega

/-! ### One window is a `1/KK` fraction of the history -/

open Classical in
/-- The ungated head consumes at least one window, so `head_frac_tiny` applies at `a = 1`. -/
lemma one_le_headW (i : ℕ) : 1 ≤ headW i := by
  classical
  have hb : (bandWtr i (16 * wFloor i)).Nonempty := by
    refine bandWtr_nonempty (i := i) (X' := 16 * wFloor i) ?_
    have := P₀_le_wFloor i
    omega
  have h1 : 1 ≤ (bandWtr i (16 * wFloor i)).card := Finset.card_pos.2 hb
  have h2 : 1 ≤ Fintype.card (gridAt i).Atom := Fintype.card_pos
  have : 1 * 1 ≤ (bandWtr i (16 * wFloor i)).card * Fintype.card (gridAt i).Atom :=
    Nat.mul_le_mul h1 h2
  simpa [headW] using this

/-- **A single read window is a `1/KK` fraction of the history before it.** -/
theorem kk_mul_KK_le_fTW (i : ℕ) : kk (i + 1) * KK (i + 1) ≤ fTW (i + 1) := by
  have h := head_frac_tiny i
  have hh : (1 : ℝ) ≤ (headW (i + 1) : ℝ) := by exact_mod_cast one_le_headW (i + 1)
  have hkk : (0 : ℝ) ≤ (kk (i + 1) : ℝ) := Nat.cast_nonneg _
  have hKK : (0 : ℝ) ≤ (KK (i + 1) : ℝ) := Nat.cast_nonneg _
  have : (kk (i + 1) : ℝ) * (KK (i + 1) : ℝ) ≤ (fTW (i + 1) : ℝ) := by nlinarith
  exact_mod_cast this

/-! ### The band increment -/

open Classical in
/-- **The increment of the read count across a mid-band stretch.**  Between the band cutoff
`fTW i` and `fTW i + s` with `a·kk i ≤ s < (a+1)·kk i`, the read count grows by
`fullGoodWPre i a` up to `a·ℓ + kk i`. -/
theorem incr_bounds (x : ℝ) (i a s : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) (ha : a ≤ (winStartsW i).card)
    (hs1 : a * kk i ≤ s) (hs2 : s < (a + 1) * kk i) :
    winCount (fullDigW x) v (fTW i) + fullGoodWPre i a x v
        ≤ winCount (fullDigW x) v (fTW i + s) ∧
      winCount (fullDigW x) v (fTW i + s)
        ≤ winCount (fullDigW x) v (fTW i) + fullGoodWPre i a x v + a * v.length + kk i := by
  classical
  have hs2' : s < a * kk i + kk i := by
    rw [add_mul, one_mul] at hs2; exact hs2
  obtain ⟨hlo, hhi⟩ := fullW_band_prefix_winCount_bounds x i a v hv hvm ha
  have hsplit := winCount_split (fullDigW x) v (show fTW i ≤ fTW i + a * kk i by omega)
  have hmono : winCount (fullDigW x) v (fTW i + a * kk i)
      ≤ winCount (fullDigW x) v (fTW i + s) :=
    winCount_mono _ _ (by omega)
  have hsub : winCount (fullDigW x) v (fTW i + s)
      ≤ winCount (fullDigW x) v (fTW i + a * kk i) + kk i := by
    refine le_trans (winCount_sub_le _ _ (show fTW i + a * kk i ≤ fTW i + s by omega)) ?_
    omega
  omega

/-! ### The mid-band error -/

/-- The mid-band error at band `i` for a word of length `ℓ`: the capture error of the prefix
certificate, the sandwich's `128/K`, the word-boundary loss `2ℓ/kk`, and the head/partial-window
loss `2/KK`. -/
noncomputable def midErrW (i ℓ : ℕ) : ℝ :=
  2 * Real.sqrt (808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) + 128 / (KK i : ℝ)
    + 2 * (ℓ : ℝ) / (kk i : ℝ) + 2 / (Nat.sqrt (KK i) : ℝ)

lemma one_le_natSqrt_KK (i : ℕ) : 1 ≤ Nat.sqrt (KK i) := by
  have h : 160000 ≤ KK i := KK_ge i
  have : Nat.sqrt 160000 ≤ Nat.sqrt (KK i) := Nat.sqrt_le_sqrt h
  have h400 : Nat.sqrt 160000 = 400 := by norm_num
  omega

lemma natSqrt_KK_sq_le (i : ℕ) : Nat.sqrt (KK i) * Nat.sqrt (KK i) ≤ KK i := by
  have := Nat.sqrt_le' (KK i); nlinarith [this]

lemma natSqrt_KK_le (i : ℕ) : Nat.sqrt (KK i) ≤ KK i :=
  Nat.sqrt_le_self _

lemma midErrW_nonneg (i ℓ : ℕ) : 0 ≤ midErrW i ℓ := by
  have h1 : (0:ℝ) ≤ 2 * Real.sqrt (808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by positivity
  have h2 : (0:ℝ) ≤ 128 / (KK i : ℝ) := by positivity
  have h3 : (0:ℝ) ≤ 2 * (ℓ : ℝ) / (kk i : ℝ) := by positivity
  have h4 : (0:ℝ) ≤ 2 / (Nat.sqrt (KK i) : ℝ) := by positivity
  unfold midErrW; linarith

/-! ### The two branches, as schedule-free real arithmetic -/

/-- The history's absolute deviation, in terms of its ratio deviation. -/
lemma abs_sub_mul_of_pos {G T r : ℝ} (hT : 0 < T) : |G - r * T| = |G / T - r| * T := by
  have h : |G / T - r| * T = |(G / T - r) * T| := by
    rw [abs_mul, abs_of_pos hT]
  rw [h]
  congr 1
  field_simp

/-- **The gated branch, abstractly.**  `P` is the certified prefix count against `u = a·F`; the
increment `D` sits within `E` of it, and `u` within `E` of the true length `s`. -/
theorem mid_gated_core {G D P T s r δ u E : ℝ}
    (hT : 0 < T) (hs : 0 < s) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hu0 : 0 ≤ u) (hus : u ≤ s) (hsu : s - u ≤ E)
    (hP : |P - r * u| ≤ δ * u)
    (hDlo : P ≤ D) (hDhi : D ≤ P + E) :
    |(G + D) / (T + s) - r| ≤ |G / T - r| + δ + 2 * E / s := by
  have hTs : (0 : ℝ) < T + s := by linarith
  set e₁ : ℝ := |G / T - r| with he₁def
  have he₁ : (0 : ℝ) ≤ e₁ := abs_nonneg _
  have hG : |G - r * T| ≤ e₁ * T := le_of_eq (abs_sub_mul_of_pos hT)
  -- the increment's absolute deviation
  have hPabs := abs_le.1 hP
  have hD : |D - r * s| ≤ δ * s + 2 * E := by
    rw [abs_le]
    have hδus : δ * u ≤ δ * s := by nlinarith
    constructor
    · nlinarith
    · nlinarith
  refine (mediant_abs_le hT hs.le hG hD).trans ?_
  rw [div_le_iff₀ hTs]
  have hEs : 2 * E / s * s = 2 * E := by field_simp
  have hEnn : (0 : ℝ) ≤ 2 * E / s := by positivity
  nlinarith [mul_nonneg he₁ hs.le, mul_nonneg hδ hT.le, mul_nonneg hEnn hT.le]

/-- **The ungated branch, abstractly.**  Nothing is known about the increment beyond
`0 ≤ D ≤ s`; what saves it is that `s ≤ c·T` with `c` tiny. -/
theorem mid_trivial_core {G D T s r c : ℝ}
    (hT : 0 < T) (hs : 0 ≤ s) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hc : 0 ≤ c)
    (hsT : s ≤ c * T) (hD0 : 0 ≤ D) (hDs : D ≤ s) :
    |(G + D) / (T + s) - r| ≤ |G / T - r| + c := by
  set e₁ : ℝ := |G / T - r| with he₁def
  have he₁ : (0 : ℝ) ≤ e₁ := abs_nonneg _
  have hG : |G - r * T| ≤ e₁ * T := le_of_eq (abs_sub_mul_of_pos hT)
  refine (mediant_abs_le_trivial hT hs he₁ hG hD0 hDs hr0 hr1).trans ?_
  have hsc : s / T ≤ c := by
    rw [div_le_iff₀ hT]; exact hsT
  linarith

/-! ### The two branches, assembled abstractly

Everything the schedule contributes is a handful of `ℕ` inequalities; these two lemmas do the
whole real-arithmetic assembly with no schedule term in sight.  `Aj` is the threshold
`⌊√(KK)⌋`: below it the increment is short enough for the trivial bound, above it the certified
bound's leftover `2·kk/s ≤ 2/a ≤ 2/Aj` is already small. -/

/-- **The trivial branch, assembled.**  The increment is at most `2T/Aj` long, so it moves the
ratio by at most `2/Aj`. -/
theorem mid_assemble_trivial {G D T s Aj : ℕ} {r : ℝ}
    (hT0 : 0 < T) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA1 : 1 ≤ Aj)
    (hsA : s * Aj ≤ 2 * T) (hD : D ≤ s) :
    |((G : ℝ) + (D : ℝ)) / ((T : ℝ) + (s : ℝ)) - r|
      ≤ |(G : ℝ) / (T : ℝ) - r| + 2 / (Aj : ℝ) := by
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT0
  have hAR : (0 : ℝ) < (Aj : ℝ) := by exact_mod_cast hA1
  have hsR : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hDs : (D : ℝ) ≤ (s : ℝ) := by exact_mod_cast hD
  have hc : (0 : ℝ) ≤ 2 / (Aj : ℝ) := by positivity
  have hsT : (s : ℝ) ≤ 2 / (Aj : ℝ) * (T : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hAR]
    have h : ((s * Aj : ℕ) : ℝ) ≤ ((2 * T : ℕ) : ℝ) := by exact_mod_cast hsA
    push_cast at h
    linarith
  exact mid_trivial_core hTR hsR hr0 hr1 hc hsT hD0 hDs

/-- **The gated branch, assembled.**  `P` is the certified prefix count against `a·F`, the
increment sits within `a·ℓ + kk` of it, and `a ≥ Aj`. -/
theorem mid_assemble_gated {G D T s P a ℓ kkj Aj Fj : ℕ} {r δ : ℝ}
    (hT0 : 0 < T) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ0 : 0 ≤ δ)
    (hkk : 0 < kkj) (hA1 : 1 ≤ Aj) (hℓ1 : 1 ≤ ℓ) (hℓkk : ℓ ≤ kkj)
    (hF : Fj = kkj - ℓ + 1)
    (haks : a * kkj ≤ s) (hska : s < a * kkj + kkj) (ha : Aj ≤ a)
    (hP : |(P : ℝ) / ((a : ℝ) * (Fj : ℝ)) - r| ≤ δ)
    (hDlo : P ≤ D) (hDhi : D ≤ P + (a * ℓ + kkj)) :
    |((G : ℝ) + (D : ℝ)) / ((T : ℝ) + (s : ℝ)) - r|
      ≤ |(G : ℝ) / (T : ℝ) - r| + δ + (2 * (ℓ : ℝ) / (kkj : ℝ) + 2 / (Aj : ℝ)) := by
  have ha1 : 1 ≤ a := le_trans hA1 ha
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT0
  have hkkR : (0 : ℝ) < (kkj : ℝ) := by exact_mod_cast hkk
  have hAR : (0 : ℝ) < (Aj : ℝ) := by exact_mod_cast hA1
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  -- `s` is positive: it covers at least one window
  have hs0 : 0 < s := by
    have : kkj ≤ a * kkj := Nat.le_mul_of_pos_left _ ha1
    omega
  have hsR0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
  have haksR : (a : ℝ) * (kkj : ℝ) ≤ (s : ℝ) := by exact_mod_cast haks
  have hskaR : (s : ℝ) ≤ (a : ℝ) * (kkj : ℝ) + (kkj : ℝ) := by exact_mod_cast hska.le
  -- the certified length `u = a·F`
  have hF1 : 1 ≤ Fj := by omega
  have hFkk : Fj ≤ kkj := by omega
  have hFR : (1 : ℝ) ≤ (Fj : ℝ) := by exact_mod_cast hF1
  have hFcast : (Fj : ℝ) = (kkj : ℝ) - (ℓ : ℝ) + 1 := by
    have : Fj + ℓ = kkj + 1 := by omega
    have h2 : ((Fj + ℓ : ℕ) : ℝ) = ((kkj + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    linarith
  have hu0 : (0 : ℝ) < (a : ℝ) * (Fj : ℝ) := by nlinarith
  have hus : (a : ℝ) * (Fj : ℝ) ≤ (s : ℝ) := by
    have h : a * Fj ≤ s := le_trans (Nat.mul_le_mul_left _ hFkk) haks
    exact_mod_cast h
  have hEnn : (0 : ℝ) ≤ (a : ℝ) * (ℓ : ℝ) + (kkj : ℝ) := by positivity
  have hsu : (s : ℝ) - (a : ℝ) * (Fj : ℝ) ≤ (a : ℝ) * (ℓ : ℝ) + (kkj : ℝ) := by
    rw [hFcast]; nlinarith
  have hPabs : |(P : ℝ) - r * ((a : ℝ) * (Fj : ℝ))| ≤ δ * ((a : ℝ) * (Fj : ℝ)) := by
    rw [abs_sub_mul_of_pos hu0]
    exact mul_le_mul_of_nonneg_right hP hu0.le
  have hDloR : (P : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDlo
  have hDhiR : (D : ℝ) ≤ (P : ℝ) + ((a : ℝ) * (ℓ : ℝ) + (kkj : ℝ)) := by
    have h : ((D : ℕ) : ℝ) ≤ ((P + (a * ℓ + kkj) : ℕ) : ℝ) := by exact_mod_cast hDhi
    push_cast at h
    linarith
  have hcore := mid_gated_core (G := (G : ℝ)) hTR hsR0 hr0 hr1 hδ0 hEnn hu0.le hus hsu hPabs hDloR hDhiR
  refine hcore.trans ?_
  -- the leftover `2E/s` splits into the word-boundary loss and the head loss
  have hsplit : 2 * ((a : ℝ) * (ℓ : ℝ) + (kkj : ℝ)) / (s : ℝ)
      = 2 * ((a : ℝ) * (ℓ : ℝ)) / (s : ℝ) + 2 * (kkj : ℝ) / (s : ℝ) := by
    field_simp
  have h1 : 2 * ((a : ℝ) * (ℓ : ℝ)) / (s : ℝ) ≤ 2 * (ℓ : ℝ) / (kkj : ℝ) := by
    rw [div_le_div_iff₀ hsR0 hkkR]
    nlinarith [mul_le_mul_of_nonneg_left haksR (by positivity : (0:ℝ) ≤ 2 * (ℓ : ℝ))]
  have h2 : 2 * (kkj : ℝ) / (s : ℝ) ≤ 2 / (Aj : ℝ) := by
    rw [div_le_div_iff₀ hsR0 hAR]
    have hAa : (Aj : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    nlinarith [mul_le_mul_of_nonneg_right hAa hkkR.le]
  linarith [hsplit ▸ (add_le_add h1 h2)]

/-! ### The mid-band estimate -/

set_option maxHeartbeats 1000000 in
open Classical in
/-- 🎯 **MID-BAND PREFIX CONTROL AT AN ARBITRARY READ INDEX.**  For every read index `n` in band
`i+1`, the read's word frequency is within `midErrW (i+1) |v|` of its value at the band cutoff. -/
theorem abs_ratio_mid_le (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) (i : ℕ)
    (hℓm : 2 * v.length ≤ kk (i + 1)) (n : ℕ)
    (hn1 : fTW (i + 1) ≤ n) (hn2 : n < fTW (i + 2)) :
    |(winCount (fullDigW (primeLambertAtBase 4)) v n : ℝ) / (n : ℝ) - 1 / (2 : ℝ) ^ v.length|
      ≤ |(winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)) : ℝ)
            / ((fTW (i + 1) : ℕ) : ℝ) - 1 / (2 : ℝ) ^ v.length|
        + midErrW (i + 1) v.length := by
  classical
  have hkk : 0 < kk (i + 1) := by unfold kk; omega
  have hT0 : 0 < fTW (i + 1) := by have := fTW_lt_succ i; omega
  have hr0 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ v.length := by positivity
  have hr1 : (1 : ℝ) / (2 : ℝ) ^ v.length ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hA1 : 1 ≤ Nat.sqrt (KK (i + 1)) := one_le_natSqrt_KK (i + 1)
  have hAsq : Nat.sqrt (KK (i + 1)) * Nat.sqrt (KK (i + 1)) ≤ KK (i + 1) := natSqrt_KK_sq_le (i + 1)
  have hAle : Nat.sqrt (KK (i + 1)) ≤ KK (i + 1) := natSqrt_KK_le (i + 1)
  have hkkKK : kk (i + 1) * KK (i + 1) ≤ fTW (i + 1) := kk_mul_KK_le_fTW i
  -- the read index, as an offset inside band `i+1`
  obtain ⟨s, rfl⟩ : ∃ s, n = fTW (i + 1) + s := ⟨n - fTW (i + 1), by omega⟩
  have hsfL : s < fLW (i + 1) := by
    have h2 : fTW (i + 2) = fTW (i + 1) + fLW (i + 1) := rfl
    omega
  -- the number of whole windows consumed
  set a : ℕ := s / kk (i + 1) with hadef
  have hdm : kk (i + 1) * a + s % kk (i + 1) = s := Nat.div_add_mod s (kk (i + 1))
  have hmod : s % kk (i + 1) < kk (i + 1) := Nat.mod_lt _ hkk
  have hcomm : kk (i + 1) * a = a * kk (i + 1) := Nat.mul_comm _ _
  have haks : a * kk (i + 1) ≤ s := by omega
  have hska : s < a * kk (i + 1) + kk (i + 1) := by omega
  have haN : a < (winStartsW (i + 1)).card := by
    have hfl : fLW (i + 1) = (winStartsW (i + 1)).card * kk (i + 1) := rfl
    have hfl2 : kk (i + 1) * (winStartsW (i + 1)).card
        = (winStartsW (i + 1)).card * kk (i + 1) := Nat.mul_comm _ _
    rw [hadef]
    exact Nat.div_lt_of_lt_mul (by omega)
  -- the read count, split into history and increment
  have hGN : winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1))
      ≤ winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1) + s) :=
    winCount_mono _ _ (by omega)
  have hDsub : winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1) + s)
      ≤ winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)) + s := by
    have h := winCount_sub_le (fullDigW (primeLambertAtBase 4)) v
      (show fTW (i + 1) ≤ fTW (i + 1) + s by omega)
    simpa using h
  obtain ⟨D, hD⟩ : ∃ D, winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1) + s)
      = winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)) + D :=
    ⟨winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1) + s)
      - winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)), by omega⟩
  have hDs : D ≤ s := by omega
  rw [hD]
  have hcast1 : ((winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)) + D : ℕ) : ℝ)
      = ((winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)) : ℕ) : ℝ) + (D : ℝ) := by
    push_cast; ring
  have hcast2 : (((fTW (i + 1) + s : ℕ)) : ℝ) = ((fTW (i + 1) : ℕ) : ℝ) + (s : ℝ) := by
    push_cast; ring
  rw [hcast1, hcast2]
  -- the trivial branch, packaged once (used for a short increment and for an ungated cutoff)
  have htriv : s * Nat.sqrt (KK (i + 1)) ≤ 2 * fTW (i + 1) →
      |(((winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)) : ℕ) : ℝ) + (D : ℝ))
          / (((fTW (i + 1) : ℕ) : ℝ) + (s : ℝ)) - 1 / (2 : ℝ) ^ v.length|
        ≤ |((winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)) : ℕ) : ℝ)
              / ((fTW (i + 1) : ℕ) : ℝ) - 1 / (2 : ℝ) ^ v.length|
          + midErrW (i + 1) v.length := by
    intro hsA
    refine (mid_assemble_trivial
      (G := winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)))
      hT0 hr0 hr1 hA1 hsA hDs).trans ?_
    have h1 : (0:ℝ) ≤ 2 * Real.sqrt (808 * Real.log 2 * (v.length : ℝ)
        / Real.sqrt (KK (i + 1))) := by positivity
    have h2 : (0:ℝ) ≤ 128 / (KK (i + 1) : ℝ) := by positivity
    have h3 : (0:ℝ) ≤ 2 * (v.length : ℝ) / (kk (i + 1) : ℝ) := by positivity
    have h4 : 2 / ((Nat.sqrt (KK (i + 1)) : ℕ) : ℝ) ≤ midErrW (i + 1) v.length := by
      unfold midErrW; linarith
    linarith
  by_cases hcase : a ≤ Nat.sqrt (KK (i + 1))
  · -- **short increment**: at most `√K` windows, so it is a `2/√K` fraction of the history
    refine htriv ?_
    have key : s * Nat.sqrt (KK (i + 1)) ≤ 2 * (kk (i + 1) * KK (i + 1)) := by
      calc s * Nat.sqrt (KK (i + 1))
          ≤ (a * kk (i + 1) + kk (i + 1)) * Nat.sqrt (KK (i + 1)) :=
            Nat.mul_le_mul (by omega) (le_refl _)
        _ = a * Nat.sqrt (KK (i + 1)) * kk (i + 1) + kk (i + 1) * Nat.sqrt (KK (i + 1)) := by ring
        _ ≤ Nat.sqrt (KK (i + 1)) * Nat.sqrt (KK (i + 1)) * kk (i + 1)
              + kk (i + 1) * KK (i + 1) :=
            Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hcase (le_refl _)) (le_refl _))
              (Nat.mul_le_mul (le_refl _) hAle)
        _ ≤ KK (i + 1) * kk (i + 1) + kk (i + 1) * KK (i + 1) :=
            Nat.add_le_add (Nat.mul_le_mul hAsq (le_refl _)) (le_refl _)
        _ = 2 * (kk (i + 1) * KK (i + 1)) := by ring
    omega
  · push_neg at hcase
    have ha1 : 0 < a := by omega
    have haLe : aLe (i + 1) (fnthW (i + 1) (a - 1)) = a := aLe_fnthW (i + 1) a ha1 haN.le
    by_cases hgate : 8 * wFloor (i + 1) ≤ cutLo (i + 1) (fnthW (i + 1) (a - 1))
    · -- **the gated branch** — the certified mid-band estimate
      have hbound := abs_prefix_ratio_sub_le_cap (i + 1) (fnthW (i + 1) (a - 1)) v hgate hlen hℓm hv
      rw [haLe] at hbound
      set δ : ℝ := 2 * Real.sqrt (808 * Real.log 2 * (v.length : ℝ) / Real.sqrt (KK (i + 1)))
        + 128 / (KK (i + 1) : ℝ) with hδdef
      have hδ0 : (0 : ℝ) ≤ δ := by rw [hδdef]; positivity
      obtain ⟨hlo', hhi'⟩ := incr_bounds (primeLambertAtBase 4) (i + 1) a s v hlen (by omega)
        haN.le haks (by rw [add_mul, one_mul]; omega)
      refine (mid_assemble_gated
        (G := winCount (fullDigW (primeLambertAtBase 4)) v (fTW (i + 1)))
        (Fj := kk (i + 1) - v.length + 1)
        hT0 hr0 hr1 hδ0 hkk hA1 hlen (by omega) rfl haks hska hcase.le hbound
        (by omega) (by omega)).trans (le_of_eq ?_)
      rw [hδdef]; unfold midErrW; ring
    · -- **the ungated branch** — the head, absorbed by `head_frac_tiny`
      refine htriv ?_
      have hhead : a ≤ headW (i + 1) := by
        have h := aLe_le_headW (i + 1) (fnthW (i + 1) (a - 1)) hgate
        omega
      have hft : headW (i + 1) * kk (i + 1) * KK (i + 1) ≤ fTW (i + 1) := by
        exact_mod_cast head_frac_tiny i
      have hakk : a * kk (i + 1) * KK (i + 1) ≤ fTW (i + 1) :=
        le_trans (Nat.mul_le_mul (Nat.mul_le_mul hhead (le_refl _)) (le_refl _)) hft
      calc s * Nat.sqrt (KK (i + 1)) ≤ s * KK (i + 1) := Nat.mul_le_mul (le_refl _) hAle
        _ ≤ (a * kk (i + 1) + kk (i + 1)) * KK (i + 1) := Nat.mul_le_mul (by omega) (le_refl _)
        _ = a * kk (i + 1) * KK (i + 1) + kk (i + 1) * KK (i + 1) := by ring
        _ ≤ fTW (i + 1) + fTW (i + 1) := Nat.add_le_add hakk hkkKK
        _ = 2 * fTW (i + 1) := by ring

/-! ### The limit at every `n`, and the endpoint -/

theorem tendsto_midErrW (ℓ : ℕ) : Tendsto (fun i => midErrW i ℓ) atTop (nhds 0) := by
  sorry

/-- **Every binary word has frequency `2^{−|v|}` in the schedule-only read, at EVERY prefix.** -/
theorem tendsto_winCount_fullDigW (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    Tendsto (fun n => (winCount (fullDigW (primeLambertAtBase 4)) v n : ℝ) / (n : ℝ))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  sorry

end NormalNumbers.G4.Sched
