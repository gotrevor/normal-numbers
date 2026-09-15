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
    + 2 * (ℓ : ℝ) / (kk i : ℝ) + 2 / (KK i : ℝ)

/-! ### The two branches, as schedule-free real arithmetic -/

/-- **The gated branch, abstractly.**  `P` is the certified prefix count against `a·F`. -/
theorem mid_gated_core {G D P T s r δ u E : ℝ}
    (hT : 0 < T) (hs : 0 < s) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hu0 : 0 ≤ u) (hus : u ≤ s) (hsu : s - u ≤ E)
    (hP : |P - r * u| ≤ δ * u)
    (hDlo : P ≤ D) (hDhi : D ≤ P + E) :
    |(G + D) / (T + s) - r| ≤ |G / T - r| + δ + 2 * E / s := by
  sorry

/-- **The ungated branch, abstractly.** -/
theorem mid_trivial_core {G D T s r c : ℝ}
    (hT : 0 < T) (hs : 0 ≤ s) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hc : 0 ≤ c)
    (hsT : s ≤ c * T) (hD0 : 0 ≤ D) (hDs : D ≤ s) :
    |(G + D) / (T + s) - r| ≤ |G / T - r| + c := by
  sorry

/-! ### The mid-band estimate -/

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
  sorry

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
