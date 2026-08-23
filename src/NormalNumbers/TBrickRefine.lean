/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TBrick

/-!
# W5 — from the surviving point to the refined brick (B–Y Lemma 13 proper)

`exists_good_avoiding_bad_of_large` (TBrick.lean) produces an irrational
point `x` in a good-length order-`n` CF extension of the brick that avoids
the CF discrepancy bad zone and every wide d-ary bad zone.  This file turns
that point into the data of a refinement:

* `exists_word_of_mem_goodExtSet` — unpack the good extension: the CF word
  `u` with `x ∈ cfCylinder (B.w ++ u)` and `K(u) ≤ e^{Cn}`;
* `cfDigit_append_eq` / `range_map_cfDigit_eq` — the digit word of `x` at
  offsets `|w|, …, |w|+n−1` *is* `u`;
* `abs_blockCount_lt_of_notMem_cfBadZone` — avoiding the CF bad zone means
  the orbit block frequency of every `v ∈ F` is `δ`-good;
* **the `kmin(n)` link** (step (β)): `4·d^{kmin} < fib(n+1)²` forces
  `|I_{w++u}| < d^{−(m_d + kmin)}`, so the new d-ary order gained in the
  refinement is at least `kmin` — `TBrick.volume_append_lt_dpow`, with the
  threshold `exists_fib_threshold` (`fib(n+1)² → ∞`);
* `mem_daryCell_split` / `TBrick.exists_goodBlock_of_avoid` — the surviving
  point sits in one definite cell of the brick's (1-or-2-cell) block, and
  avoiding the wide zones makes its own new digit block *good* at every
  block length `k ≥ kmin`.

Remaining for Lemma 13 (next): choose the maximal new order `m'_d`, apply
Prop 12 (`interval_subset_daryCell_two`) to get the refined cell block and
ratio, and package everything as a new `TBrick` refining the input.
-/

namespace NormalNumbers

open MeasureTheory

/-- A genuine cylinder has positive Lebesgue measure (discharges the `hpos`
hypothesis of `exists_good_avoiding_bad*`). -/
theorem volume_cfCylinder_ne_zero (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : volume (cfCylinder w) ≠ 0 := by
  rw [volume_cfCylinder w hw hpos]
  have hK : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
  have hK' : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

/-- Unpack membership in the good-length extension set. -/
theorem exists_word_of_mem_goodExtSet {w : List ℕ} {C : ℝ} {n : ℕ} {x : ℝ}
    (hx : x ∈ goodExtSet w C n) :
    ∃ u, u ∈ genWords n ∧ (cfK u : ℝ) ≤ Real.exp (C * n) ∧
      x ∈ cfCylinder (w ++ u) := by
  simp only [goodExtSet, Set.mem_iUnion] at hx
  obtain ⟨u, hu, hxu⟩ := hx
  by_cases h : (cfK u : ℝ) ≤ Real.exp (C * n)
  · exact ⟨u, hu, h, by rwa [if_pos h] at hxu⟩
  · rw [if_neg h] at hxu
    exact absurd hxu (Set.notMem_empty x)

/-- A point of `cfCylinder (w ++ u)` has `u` as its CF digits at offsets
`|w|, …, |w|+|u|−1`. -/
theorem cfDigit_append_eq {w u : List ℕ} {x : ℝ}
    (hx : x ∈ cfCylinder (w ++ u)) :
    ∀ i < u.length, cfDigit x (w.length + i) = u.getD i 0 := by
  intro i hi
  have h1 := hx.2 (w.length + i) (by rw [List.length_append]; omega)
  have h2 : (w ++ u).getD (w.length + i) 0 = u.getD i 0 := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
    congr 1
    omega
  rwa [h2] at h1

/-- The length-`|u|` digit word of `x` starting at offset `|w|` is `u`. -/
theorem range_map_cfDigit_eq {w u : List ℕ} {x : ℝ}
    (hx : x ∈ cfCylinder (w ++ u)) :
    (List.range u.length).map (fun i => cfDigit x (w.length + i)) = u := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [cfDigit_append_eq hx i h2, List.getD_eq_getElem u 0 h2]

/-- **CF-side unpacking**: an irrational point of `I_w` avoiding the CF bad
zone of `v` has `δ`-good orbit block frequency of `v` over the next `n`
steps. -/
theorem abs_blockCount_lt_of_notMem_cfBadZone {w v : List ℕ} {x : ℝ}
    {n : ℕ} {δ : ℝ} (hx : x ∈ cfCylinder w) (hirr : Irrational x)
    (hnot : x ∉ cfBadZone w v n δ) :
    |blockCount (cfCylinder v) n (gaussMap^[w.length] x) / n
      - (gaussMeasure (cfCylinder v)).toReal| < δ := by
  have horb := (irrational_orbit x hirr hx.1 w.length).2
  by_contra hge
  push Not at hge
  exact hnot ⟨hx, horb, hge⟩

/-- The narrow d-ary bad zone is inside the wide one. -/
theorem daryBadZone_subset_wide (d m0 : ℕ) (hd : 1 ≤ d) (j0 : ℤ) (ε : ℝ)
    (k : ℕ) :
    daryBadZone d m0 j0 ε k ⊆ daryBadZoneWide d m0 j0 ε k := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ (m0 + k) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  refine Set.iUnion₂_mono fun β _ => ?_
  intro y hy
  obtain ⟨hl, hr⟩ := hy
  constructor
  · refine le_trans (div_le_div_of_nonneg_right ?_ hdpow.le) hl
    push_cast
    linarith
  · refine lt_of_lt_of_le hr (div_le_div_of_nonneg_right ?_ hdpow.le)
    push_cast
    linarith

/-- A point of an `r`-cell block lies in one definite single cell of it. -/
theorem mem_daryCell_split {d m : ℕ} (hd : 1 ≤ d) {j : ℤ} {r : ℕ} {x : ℝ}
    (hx : x ∈ daryCell d m j r) :
    ∃ i : ℕ, i < r ∧ x ∈ daryCell d m (j + i) 1 := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ m := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  obtain ⟨hl, hr⟩ := hx
  have hFl : j ≤ ⌊x * d ^ m⌋ := by
    apply Int.le_floor.2
    rw [div_le_iff₀ hdpow] at hl
    exact hl
  have hFr : ⌊x * d ^ m⌋ < j + r := by
    apply Int.floor_lt.2
    rw [lt_div_iff₀ hdpow] at hr
    push_cast
    linarith
  refine ⟨(⌊x * d ^ m⌋ - j).toNat, by omega, ?_⟩
  have hj : j + ((⌊x * d ^ m⌋ - j).toNat : ℤ) = ⌊x * d ^ m⌋ := by omega
  rw [daryCell, hj]
  constructor
  · rw [div_le_iff₀ hdpow]
    exact Int.floor_le _
  · rw [lt_div_iff₀ hdpow]
    push_cast
    exact Int.lt_floor_add_one _

/-- **d-ary unpacking**: a point of `I_w` avoiding the aggregate wide bad
zone lies in a definite cell `B.j d + i` (`i < 2`) of the brick's block, and
for every base `2 ≤ d ≤ t` and every block length `k ≥ kmin` its own
order-`(m_d + k)` sub-cell carries a *good* new digit block. -/
theorem TBrick.exists_goodBlock_of_avoid {t : ℕ} (B : TBrick t)
    {ε : ℝ} {kmin : ℕ} {x : ℝ} (hx : x ∈ cfCylinder B.w)
    (havoid : x ∉ ⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
      ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
    {d : ℕ} (hd2 : 2 ≤ d) (hdt : d ≤ t) :
    ∃ i : ℕ, i < 2 ∧ x ∈ daryCell d (B.m d) (B.j d + i) 1 ∧
      ∀ k : ℕ, kmin ≤ k →
        ∃ β : Fin k → Fin d, β ∉ badBlocks d k ε ∧
          x ∈ daryCell d (B.m d + k)
            ((B.j d + i) * d ^ k
              + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1 := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  obtain ⟨i, hir, hxi⟩ := mem_daryCell_split hd1 (B.hsub d hd2 hdt hx)
  have hi2 : i < 2 := lt_of_lt_of_le hir (B.hr2 d hd2 hdt)
  refine ⟨i, hi2, hxi, fun k hk => ?_⟩
  have hnot : x ∉ daryBadZone d (B.m d) (B.j d + i) ε k := by
    intro hmem
    apply havoid
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hd2, hdt⟩) ?_
    refine Set.mem_biUnion (Finset.mem_range.2 hi2) ?_
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ?_⟩⟩
    exact daryBadZone_subset_wide d (B.m d) hd1 (B.j d + i) ε k hmem
  exact exists_goodBlock_of_notMem_badZone d (B.m d) k hd1 (B.j d + i)
    hxi hnot

/-- `fib(n+1)² → ∞`: past some `N` it exceeds any given constant.  (The
quantitative heart of the `kmin(n)` link — log-free.) -/
theorem exists_fib_threshold (a : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a < ((Nat.fib (n + 1) : ℝ)) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_nat_gt a
  refine ⟨M + 5, fun n hn => ?_⟩
  have hfib : n + 1 ≤ Nat.fib (n + 1) := Nat.le_fib_self (by omega)
  have hfib1 : (1 : ℝ) ≤ (Nat.fib (n + 1) : ℝ) := by
    have : 1 ≤ Nat.fib (n + 1) := by omega
    exact_mod_cast this
  have hMn : (M : ℝ) ≤ ((n : ℕ) : ℝ) + 1 := by
    have : M ≤ n + 1 := by omega
    exact_mod_cast this
  have hnfib : ((n : ℕ) : ℝ) + 1 ≤ (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast hfib
  nlinarith

/-- **The `kmin(n)` link** (step (β)): if `4·d^{kmin} < fib(n+1)²`, every
genuine order-`n` extension of the brick's cylinder is shorter than
`d^{−(m_d + kmin)}` — so the maximal new d-ary order beats `m_d + kmin` and
the refinement gains at least `kmin` new digits in base `d`. -/
theorem TBrick.volume_append_lt_dpow {t : ℕ} (B : TBrick t)
    {d : ℕ} (hd2 : 2 ≤ d) (hdt : d ≤ t) {u : List ℕ} (hu_ne : u ≠ [])
    (hupos : ∀ a ∈ u, 1 ≤ a) (kmin : ℕ)
    (hfib : 4 * (d : ℝ) ^ kmin < (Nat.fib (u.length + 1) : ℝ) ^ 2) :
    volume (cfCylinder (B.w ++ u))
      < ENNReal.ofReal ((d : ℝ) ^ (B.m d + kmin))⁻¹ := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hfibpos : 0 < Nat.fib (u.length + 1) :=
    Nat.fib_pos.2 (Nat.succ_pos _)
  have hfibR : (0 : ℝ) < (Nat.fib (u.length + 1) : ℝ) := by
    exact_mod_cast hfibpos
  -- the brick's cylinder is at most the 2-cell block: `|I_w| ≤ 2/d^{m_d}`
  have hIw : volume (cfCylinder B.w)
      ≤ ENNReal.ofReal (2 / (d : ℝ) ^ (B.m d)) := by
    calc volume (cfCylinder B.w)
        ≤ volume (daryCell d (B.m d) (B.j d) (B.r d)) :=
          measure_mono (B.hsub d hd2 hdt)
      _ = ENNReal.ofReal ((B.r d : ℝ) / (d : ℝ) ^ (B.m d)) :=
          volume_daryCell d (B.m d) hd1 (B.j d) (B.r d)
      _ ≤ ENNReal.ofReal (2 / (d : ℝ) ^ (B.m d)) := by
          apply ENNReal.ofReal_le_ofReal
          have hr2 : (B.r d : ℝ) ≤ 2 := by
            exact_mod_cast B.hr2 d hd2 hdt
          have hpm : (0 : ℝ) < (d : ℝ) ^ (B.m d) := pow_pos hdR _
          exact div_le_div_of_nonneg_right hr2 hpm.le
  -- deterministic Fibonacci shrink: `|J|·fib² ≤ 2|I_w| ≤ 4/d^{m_d}`
  have hmul := volume_append_mul_fib_le B.w u B.hw_ne hu_ne B.hw_pos hupos
  have h4 : volume (cfCylinder (B.w ++ u))
      * (Nat.fib (u.length + 1) : ENNReal) ^ 2
      ≤ ENNReal.ofReal (4 / (d : ℝ) ^ (B.m d)) := by
    refine hmul.trans ?_
    calc 2 * volume (cfCylinder B.w)
        ≤ 2 * ENNReal.ofReal (2 / (d : ℝ) ^ (B.m d)) := by gcongr
      _ = ENNReal.ofReal (4 / (d : ℝ) ^ (B.m d)) := by
          rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by simp,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  -- divide out `fib²` and compare real bounds
  have hfibE0 : ((Nat.fib (u.length + 1) : ENNReal)) ^ 2 ≠ 0 := by
    simp [hfibpos.ne']
  have hfibEtop : ((Nat.fib (u.length + 1) : ENNReal)) ^ 2 ≠ ⊤ := by
    simp [(ENNReal.natCast_lt_top _).ne]
  have hJ : volume (cfCylinder (B.w ++ u))
      ≤ ENNReal.ofReal (4 / (d : ℝ) ^ (B.m d))
        / (Nat.fib (u.length + 1) : ENNReal) ^ 2 :=
    (ENNReal.le_div_iff_mul_le (Or.inl hfibE0) (Or.inl hfibEtop)).2 h4
  have hdivE : ENNReal.ofReal (4 / (d : ℝ) ^ (B.m d)
          / (Nat.fib (u.length + 1) : ℝ) ^ 2)
      = ENNReal.ofReal (4 / (d : ℝ) ^ (B.m d))
        / (Nat.fib (u.length + 1) : ENNReal) ^ 2 := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hfibR 2),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  have hreal : 4 / (d : ℝ) ^ (B.m d) / (Nat.fib (u.length + 1) : ℝ) ^ 2
      < ((d : ℝ) ^ (B.m d + kmin))⁻¹ := by
    have hp1 : (0 : ℝ) < (d : ℝ) ^ (B.m d) * (Nat.fib (u.length + 1) : ℝ) ^ 2 :=
      mul_pos (pow_pos hdR _) (pow_pos hfibR 2)
    have hp2 : (0 : ℝ) < (d : ℝ) ^ (B.m d + kmin) := pow_pos hdR _
    rw [div_div, inv_eq_one_div, div_lt_div_iff₀ hp1 hp2]
    have hexp : (d : ℝ) ^ (B.m d + kmin) = (d : ℝ) ^ (B.m d) * d ^ kmin := by
      rw [pow_add]
    rw [hexp, one_mul]
    have hpm : (0 : ℝ) < (d : ℝ) ^ (B.m d) := by positivity
    nlinarith
  calc volume (cfCylinder (B.w ++ u))
      ≤ ENNReal.ofReal (4 / (d : ℝ) ^ (B.m d)
          / (Nat.fib (u.length + 1) : ℝ) ^ 2) := by
        rw [hdivE]; exact hJ
    _ < ENNReal.ofReal ((d : ℝ) ^ (B.m d + kmin))⁻¹ :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hreal

/-- Any cylinder has finite measure (it sits inside `(0,1)`). -/
theorem volume_cfCylinder_ne_top (w : List ℕ) :
    volume (cfCylinder w) ≠ ⊤ := by
  have h1 : volume (cfCylinder w) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
    measure_mono (fun x hx => hx.1)
  rw [Real.volume_Ioo] at h1
  exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne

attribute [local instance] Classical.propDecidable

/-- **Greatest order**: if `L < d^{−m0}`, there is a greatest `m' ≥ m0` with
`L < d^{−m'}`; at that order also `d^{−(m'+1)} ≤ L` — the two-sided window
that Prop 12 turns into the `1/(2d)` brick ratio. -/
theorem exists_greatest_inv_pow_lt {d : ℕ} (hd : 2 ≤ d) {L : ℝ}
    (hL : 0 < L) {m0 : ℕ} (h : L < ((d : ℝ) ^ m0)⁻¹) :
    ∃ m' : ℕ, m0 ≤ m' ∧ L < ((d : ℝ) ^ m')⁻¹ ∧
      ((d : ℝ) ^ (m' + 1))⁻¹ ≤ L := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨M0, hM0⟩ := pow_unbounded_of_one_lt (L⁻¹) hd1
  set P : ℕ → Prop := fun m => L < ((d : ℝ) ^ m)⁻¹ with hP
  set M : ℕ := max M0 m0 with hM
  have hnotPM : ¬ P M := by
    have h1 : ((d : ℝ) ^ M0)⁻¹ < L := inv_lt_of_inv_lt₀ hL hM0
    have h2 : ((d : ℝ) ^ M)⁻¹ ≤ ((d : ℝ) ^ M0)⁻¹ := by
      have hpow : (d : ℝ) ^ M0 ≤ (d : ℝ) ^ M :=
        pow_le_pow_right₀ hd1.le (le_max_left _ _)
      have := one_div_le_one_div_of_le (by positivity) hpow
      simpa [one_div] using this
    exact not_lt.2 (h2.trans h1.le)
  have hm0M : m0 ≤ M := le_max_right _ _
  have hPm0 : P m0 := h
  refine ⟨Nat.findGreatest P M, Nat.le_findGreatest hm0M hPm0,
    Nat.findGreatest_spec hm0M hPm0, ?_⟩
  by_cases hcase : Nat.findGreatest P M = M
  · exact absurd (hcase ▸ Nat.findGreatest_spec hm0M hPm0) hnotPM
  · have hlt : Nat.findGreatest P M < M :=
      lt_of_le_of_ne (Nat.findGreatest_le M) hcase
    have hnot : ¬ P (Nat.findGreatest P M + 1) :=
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (by omega)
    exact not_lt.1 hnot

/-- **The refined d-ary cell block** (Prop-12 step of Lemma 13): for the
survivor's cylinder `J = I_{w++u}`, the greatest order `m'` with
`|J| < d^{−m'}` satisfies `m' ≥ m_d + kmin` (the `kmin(n)` link) and yields a
2-cell block containing `J` with the `1/(2d)` brick ratio — the base-`d`
component of the refined brick. -/
theorem TBrick.exists_refined_cell {t : ℕ} (B : TBrick t)
    {d : ℕ} (hd2 : 2 ≤ d) (hdt : d ≤ t) {u : List ℕ} (hu_ne : u ≠ [])
    (hupos : ∀ a ∈ u, 1 ≤ a) (kmin : ℕ)
    (hfib : 4 * (d : ℝ) ^ kmin < (Nat.fib (u.length + 1) : ℝ) ^ 2) :
    ∃ m' : ℕ, ∃ j' : ℤ, B.m d + kmin ≤ m' ∧
      cfCylinder (B.w ++ u) ⊆ daryCell d m' j' 2 ∧
      ENNReal.ofReal ((d : ℝ) ^ m')⁻¹
        ≤ ENNReal.ofReal (2 * d) * volume (cfCylinder (B.w ++ u)) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hwu_ne : B.w ++ u ≠ [] := by
    simp [B.hw_ne]
  have hwupos : ∀ a ∈ B.w ++ u, 1 ≤ a := fun a ha =>
    (List.mem_append.1 ha).elim (B.hw_pos a) (hupos a)
  have hJ0 : volume (cfCylinder (B.w ++ u)) ≠ 0 :=
    volume_cfCylinder_ne_zero _ hwu_ne hwupos
  have hJtop : volume (cfCylinder (B.w ++ u)) ≠ ⊤ :=
    volume_cfCylinder_ne_top _
  set L : ℝ := (volume (cfCylinder (B.w ++ u))).toReal with hLdef
  have hL0 : 0 < L := ENNReal.toReal_pos hJ0 hJtop
  -- the `kmin(n)` link puts `L` below `d^{−(m_d+kmin)}`
  have hLlt : L < ((d : ℝ) ^ (B.m d + kmin))⁻¹ := by
    have hlt := B.volume_append_lt_dpow hd2 hdt hu_ne hupos kmin hfib
    have := (ENNReal.toReal_lt_toReal hJtop ENNReal.ofReal_ne_top).2 hlt
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  obtain ⟨m', hm0, hPm', hPnext⟩ := exists_greatest_inv_pow_lt hd2 hL0 hLlt
  obtain ⟨a, c, hsub, hlen⟩ :=
    cfCylinder_subset_Icc_length (B.w ++ u) hwu_ne hwupos
  have hprop12 : Set.Icc a c ⊆ daryCell d m' ⌊a * (d : ℝ) ^ m'⌋ 2 := by
    apply interval_subset_daryCell_two d m' hd1
    rw [hlen, ← hLdef, one_div]
    exact hPm'
  refine ⟨m', ⌊a * (d : ℝ) ^ m'⌋, hm0, hsub.trans hprop12, ?_⟩
  -- ratio: `d^{−m'} = d·d^{−(m'+1)} ≤ d·L ≤ 2d·L`
  have hratio : ((d : ℝ) ^ m')⁻¹ ≤ 2 * d * L := by
    have hsplit : ((d : ℝ) ^ m')⁻¹ = d * ((d : ℝ) ^ (m' + 1))⁻¹ := by
      rw [pow_succ]
      field_simp
    rw [hsplit]
    nlinarith
  calc ENNReal.ofReal ((d : ℝ) ^ m')⁻¹
      ≤ ENNReal.ofReal (2 * d * L) := ENNReal.ofReal_le_ofReal hratio
    _ = ENNReal.ofReal (2 * d) * volume (cfCylinder (B.w ++ u)) := by
        rw [ENNReal.ofReal_mul (by positivity), hLdef,
          ENNReal.ofReal_toReal hJtop]

/-- Membership in a single order-`m` cell pins the floor. -/
theorem floor_eq_of_mem_daryCell_one {d m : ℕ} (hd : 1 ≤ d) {j : ℤ} {x : ℝ}
    (hx : x ∈ daryCell d m j 1) : ⌊x * (d : ℝ) ^ m⌋ = j := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ m := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  obtain ⟨hl, hr⟩ := hx
  rw [div_le_iff₀ hdpow] at hl
  rw [lt_div_iff₀ hdpow] at hr
  apply Int.floor_eq_iff.2
  constructor
  · exact hl
  · push_cast
    push_cast at hr
    linarith

/-- **Goodness transfer** (the purpose of the neighbour-widened zones): if
the survivor `x` avoids the wide bad zone based at `y`'s cell, and `x`, `y`
lie in a common 2-cell block at order `m0 + k` (the refined block from
Prop 12), then `y`'s own new digit block is good — even though `y` itself
was never selected. -/
theorem goodBlock_transfer (d m0 k : ℕ) (hd : 1 ≤ d) (jc : ℤ) {j0y : ℤ}
    {ε : ℝ} {x y : ℝ}
    (hy0 : y ∈ daryCell d m0 j0y 1)
    (hxc : x ∈ daryCell d (m0 + k) jc 2)
    (hyc : y ∈ daryCell d (m0 + k) jc 2)
    (havoid : x ∉ daryBadZoneWide d m0 j0y ε k) :
    ∃ β : Fin k → Fin d, β ∉ badBlocks d k ε ∧
      y ∈ daryCell d (m0 + k)
        (j0y * d ^ k + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1 := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ (m0 + k) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  obtain ⟨hlo, hhi, hymem⟩ := floor_subCell_bounds d m0 k hd j0y hy0
  set Fy : ℤ := ⌊y * (d : ℝ) ^ (m0 + k)⌋ with hFy
  have hcast : ((d : ℤ)) ^ k = ((d ^ k : ℕ) : ℤ) := by push_cast; ring
  rw [add_mul, one_mul] at hhi
  have hv : (Fy - j0y * d ^ k).toNat < d ^ k := by omega
  obtain ⟨β, hβ⟩ := exists_block_of_lt d k hv
  have hidx : j0y * d ^ k
      + (blockNatVal d (List.ofFn fun l => (β l : ℕ)) : ℤ) = Fy := by
    rw [hβ]
    omega
  refine ⟨β, ?_, by rwa [hidx]⟩
  intro hbad
  apply havoid
  rw [daryBadZoneWide]
  refine Set.mem_biUnion hbad ?_
  have hidx1 : j0y * d ^ k
      + (blockNatVal d (List.ofFn fun l => (β l : ℕ)) : ℤ) - 1 = Fy - 1 := by
    omega
  rw [hidx1]
  -- `x`'s own cell index is within 1 of `Fy` (both in the 2-cell block)
  obtain ⟨ix, hix2, hxi⟩ := mem_daryCell_split hd hxc
  obtain ⟨iy, hiy2, hyi⟩ := mem_daryCell_split hd hyc
  have hFx : ⌊x * (d : ℝ) ^ (m0 + k)⌋ = jc + ix :=
    floor_eq_of_mem_daryCell_one hd hxi
  have hFy' : Fy = jc + iy := hFy ▸ floor_eq_of_mem_daryCell_one hd hyi
  -- hence `x ∈ [Fy−1, Fy+2)/d^{m0+k}` — the widened 3-cell block
  obtain ⟨hxl, hxr⟩ := hxi
  have hb1 : Fy - 1 ≤ jc + ix := by omega
  have hb2 : jc + ix + 1 ≤ Fy - 1 + 3 := by omega
  constructor
  · refine le_trans (div_le_div_of_nonneg_right ?_ hdpow.le) hxl
    exact_mod_cast hb1
  · refine lt_of_lt_of_le hxr (div_le_div_of_nonneg_right ?_ hdpow.le)
    have hb2R : ((jc + ix + 1 : ℤ) : ℝ) ≤ ((Fy - 1 + 3 : ℤ) : ℝ) := by
      exact_mod_cast hb2
    push_cast
    push_cast at hb2R
    linarith

/-- **B–Y Lemma 13, `t' = t` case (repo form).** Every t-brick admits, for
every sufficiently large block-length floor `kmin` and every sufficiently
large relative CF order `n`, a refined t-brick `B'` whose CF word extends
`B.w` by a genuine order-`n` word `u` such that:

* `u` has controlled continuant (`K(u) ≤ e^{Cn}` — good length);
* for every `v ∈ F`, the window count of `v` in `u` is within `δn + |v|` of
  `n·γ(I_v)` (the CF discrepancy payload, Lemma-7-ready);
* every base `2 ≤ d ≤ t` gains at least `kmin` new d-ary digits;
* **every point** `y` of the refined cylinder lies in a definite cell of the
  old brick's block and its new length-`(B'.m d − B.m d)` digit block is
  `ε`-good (the d-ary discrepancy payload, Lemma-9-ready — transferred from
  the selected survivor via the widened zones). -/
theorem TBrick.exists_refinement {t : ℕ} (B : TBrick t)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a)
    (hFne : ∀ v ∈ F, v ≠ [])
    {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1) :
    ∃ kmin₀ : ℕ, ∀ kmin, kmin₀ ≤ kmin → ∃ N : ℕ, ∀ n, N ≤ n → 0 < n →
      ∃ (B' : TBrick t) (u : List ℕ) (C : ℝ), 0 < C ∧
        B'.w = B.w ++ u ∧ u.length = n ∧ (∀ a ∈ u, 1 ≤ a) ∧
        (cfK u : ℝ) ≤ Real.exp (C * n) ∧
        (∀ v ∈ F, |(countOccurrences v u : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length) ∧
        (∀ d, 2 ≤ d → d ≤ t → B.m d + kmin ≤ B'.m d) ∧
        (∀ d, 2 ≤ d → d ≤ t → ∀ y ∈ cfCylinder B'.w,
          ∃ i : ℕ, i < 2 ∧ y ∈ daryCell d (B.m d) (B.j d + i) 1 ∧
            ∃ β : Fin (B'.m d - B.m d) → Fin d,
              β ∉ badBlocks d (B'.m d - B.m d) ε ∧
              y ∈ daryCell d (B.m d + (B'.m d - B.m d))
                ((B.j d + i) * d ^ (B'.m d - B.m d)
                  + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1) := by
  have hpos := volume_cfCylinder_ne_zero B.w B.hw_ne B.hw_pos
  obtain ⟨N₁, kmin₀, hmain⟩ :=
    exists_good_avoiding_bad_of_large B F hF hδ hε0 hεt hpos
  refine ⟨kmin₀, fun kmin hkmin => ?_⟩
  obtain ⟨N₂, hN₂⟩ := exists_fib_threshold (4 * (t : ℝ) ^ kmin)
  refine ⟨max N₁ N₂, fun n hn hn0 => ?_⟩
  obtain ⟨C, hC, x, hxG, hirr, hnotbad⟩ :=
    hmain n (le_trans (le_max_left _ _) hn) hn0 kmin hkmin
  obtain ⟨u, huGen, hK, hxJ⟩ := exists_word_of_mem_goodExtSet hxG
  obtain ⟨hulen, hupos⟩ := huGen
  have hu_ne : u ≠ [] := by
    intro h
    rw [h] at hulen
    simp at hulen
    omega
  have hwu_ne : B.w ++ u ≠ [] := by simp [B.hw_ne]
  have hwu_pos : ∀ a ∈ B.w ++ u, 1 ≤ a := fun a ha =>
    (List.mem_append.1 ha).elim (B.hw_pos a) (hupos a)
  -- the fib condition holds for every base `d ≤ t`
  have hfib : ∀ d, 2 ≤ d → d ≤ t →
      4 * (d : ℝ) ^ kmin < (Nat.fib (u.length + 1) : ℝ) ^ 2 := by
    intro d hd2 hdt
    have hdt' : (d : ℝ) ≤ t := by exact_mod_cast hdt
    have h1 : (d : ℝ) ^ kmin ≤ (t : ℝ) ^ kmin :=
      pow_le_pow_left₀ (by positivity) hdt' _
    have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [hulen]
    linarith
  -- refined cells for every base
  have hspec : ∀ d, 2 ≤ d → d ≤ t → ∃ m' : ℕ, ∃ j' : ℤ,
      B.m d + kmin ≤ m' ∧
      cfCylinder (B.w ++ u) ⊆ daryCell d m' j' 2 ∧
      ENNReal.ofReal ((d : ℝ) ^ m')⁻¹
        ≤ ENNReal.ofReal (2 * d) * volume (cfCylinder (B.w ++ u)) :=
    fun d hd2 hdt =>
      B.exists_refined_cell hd2 hdt hu_ne hupos kmin (hfib d hd2 hdt)
  choose! m' j' hm hsubJ hrat using hspec
  refine ⟨⟨B.w ++ u, hwu_ne, hwu_pos, m', j', fun _ => 2,
    fun _ _ _ => by norm_num, fun _ _ _ => le_refl 2, hsubJ, hrat⟩,
    u, C, hC, rfl, hulen, hupos, hK, ?_, hm, ?_⟩
  · -- CF discrepancy payload
    intro v hv
    have hxw : x ∈ cfCylinder B.w := cfCylinder_append_subset _ _ hxJ
    have hnotCF : x ∉ cfBadZone B.w v n δ :=
      fun h => hnotbad (Or.inl (Set.mem_biUnion hv h))
    have habs := abs_blockCount_lt_of_notMem_cfBadZone hxw hirr hnotCF
    have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1 :=
      fun j => (irrational_orbit x hirr hxJ.1 j).2
    have hbr := blockCount_sub_countOccurrences_bounds horb v (hFne v hv)
      B.w.length n
    have hword : (List.range n).map (fun i => cfDigit x (B.w.length + i))
        = u := by
      rw [← hulen]
      exact range_map_cfDigit_eq hxJ
    rw [hword] at hbr
    obtain ⟨hbr1, hbr2⟩ := hbr
    set bc : ℝ := blockCount (cfCylinder v) n (gaussMap^[B.w.length] x)
      with hbc
    set γv : ℝ := (gaussMeasure (cfCylinder v)).toReal with hγv
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
    have habs' : |bc - γv * n| < δ * n := by
      have h1 : bc / n - γv = (bc - γv * n) / n := by field_simp
      rw [h1, abs_div, abs_of_pos hn0R, div_lt_iff₀ hn0R] at habs
      linarith [habs]
    rw [abs_lt] at habs' ⊢
    have hv0 : (0 : ℝ) ≤ v.length := by positivity
    constructor
    · linarith
    · linarith
  · -- d-ary goodness payload, transferred from the survivor
    intro d hd2 hdt y hy
    have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
    have hmk : B.m d + (m' d - B.m d) = m' d := by
      have := hm d hd2 hdt
      omega
    have hyw : y ∈ cfCylinder B.w := cfCylinder_append_subset _ _ hy
    obtain ⟨i, hir, hyi⟩ := mem_daryCell_split hd1 (B.hsub d hd2 hdt hyw)
    have hi2 : i < 2 := lt_of_lt_of_le hir (B.hr2 d hd2 hdt)
    have havoid : x ∉ daryBadZoneWide d (B.m d) (B.j d + i) ε
        (m' d - B.m d) := by
      intro hmem
      apply hnotbad
      right
      refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hd2, hdt⟩) ?_
      refine Set.mem_biUnion (Finset.mem_range.2 hi2) ?_
      refine Set.mem_iUnion.2 ⟨m' d - B.m d, Set.mem_iUnion.2 ⟨?_, hmem⟩⟩
      have := hm d hd2 hdt
      omega
    have hxc : x ∈ daryCell d (B.m d + (m' d - B.m d)) (j' d) 2 := by
      rw [hmk]
      exact hsubJ d hd2 hdt hxJ
    have hyc : y ∈ daryCell d (B.m d + (m' d - B.m d)) (j' d) 2 := by
      rw [hmk]
      exact hsubJ d hd2 hdt hy
    obtain ⟨β, hβgood, hymem⟩ := goodBlock_transfer d (B.m d)
      (m' d - B.m d) hd1 (j' d) hyi hxc hyc havoid
    exact ⟨i, hi2, hyi, β, hβgood, hymem⟩

/-- **Standalone Prop-12 cell block**: any genuine cylinder shorter than
`d^{−m0}` sits in a 2-cell block of some order `m' ≥ m0` with the `1/(2d)`
ratio.  (The brick-free core of `exists_refined_cell`; used to adjoin a NEW
base — the `t → t+1` case of Lemma 13 and the seed brick.) -/
theorem exists_cell_block {w : List ℕ} (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    {d : ℕ} (hd : 2 ≤ d) {m0 : ℕ}
    (hlt : volume (cfCylinder w) < ENNReal.ofReal ((d : ℝ) ^ m0)⁻¹) :
    ∃ m' : ℕ, ∃ j' : ℤ, m0 ≤ m' ∧
      cfCylinder w ⊆ daryCell d m' j' 2 ∧
      ENNReal.ofReal ((d : ℝ) ^ m')⁻¹
        ≤ ENNReal.ofReal (2 * d) * volume (cfCylinder w) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hJ0 : volume (cfCylinder w) ≠ 0 := volume_cfCylinder_ne_zero w hw hpos
  have hJtop : volume (cfCylinder w) ≠ ⊤ := volume_cfCylinder_ne_top w
  set L : ℝ := (volume (cfCylinder w)).toReal with hLdef
  have hL0 : 0 < L := ENNReal.toReal_pos hJ0 hJtop
  have hLlt : L < ((d : ℝ) ^ m0)⁻¹ := by
    have := (ENNReal.toReal_lt_toReal hJtop ENNReal.ofReal_ne_top).2 hlt
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  obtain ⟨m', hm0, hPm', hPnext⟩ := exists_greatest_inv_pow_lt hd hL0 hLlt
  obtain ⟨a, c, hsub, hlen⟩ := cfCylinder_subset_Icc_length w hw hpos
  have hprop12 : Set.Icc a c ⊆ daryCell d m' ⌊a * (d : ℝ) ^ m'⌋ 2 := by
    apply interval_subset_daryCell_two d m' hd1
    rw [hlen, ← hLdef, one_div]
    exact hPm'
  refine ⟨m', ⌊a * (d : ℝ) ^ m'⌋, hm0, hsub.trans hprop12, ?_⟩
  have hratio : ((d : ℝ) ^ m')⁻¹ ≤ 2 * d * L := by
    have hsplit : ((d : ℝ) ^ m')⁻¹ = d * ((d : ℝ) ^ (m' + 1))⁻¹ := by
      rw [pow_succ]
      field_simp
    rw [hsplit]
    nlinarith
  calc ENNReal.ofReal ((d : ℝ) ^ m')⁻¹
      ≤ ENNReal.ofReal (2 * d * L) := ENNReal.ofReal_le_ofReal hratio
    _ = ENNReal.ofReal (2 * d) * volume (cfCylinder w) := by
        rw [ENNReal.ofReal_mul (by positivity), hLdef,
          ENNReal.ofReal_toReal hJtop]

/-- A genuine cylinder has measure `< 1` (in fact `≤ ½`). -/
theorem volume_cfCylinder_lt_one (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    volume (cfCylinder w) < ENNReal.ofReal 1 := by
  rw [volume_cfCylinder w hw hpos]
  have hK : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
  have hK' : (1 : ℝ) ≤ (cfK w.dropLast : ℝ) := by
    exact_mod_cast one_le_cfK w.dropLast
      (fun a ha => hpos a (List.dropLast_subset _ ha))
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 ?_
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- **Lemma 13, `t → t+1` step**: any t-brick extends to a `(t+1)`-brick on
the SAME CF word — adjoin base `t+1` by the standalone Prop-12 block (no
goodness required the first time a base appears; B–Y's closing paragraph). -/
theorem TBrick.exists_extend_succ {t : ℕ} (B : TBrick t) :
    ∃ B' : TBrick (t + 1), B'.w = B.w ∧
      ∀ d, 2 ≤ d → d ≤ t → B'.m d = B.m d ∧ B'.j d = B.j d ∧
        B'.r d = B.r d := by
  by_cases ht1 : 2 ≤ t + 1
  · have hlt : volume (cfCylinder B.w)
        < ENNReal.ofReal (((t + 1 : ℕ) : ℝ) ^ (0 : ℕ))⁻¹ := by
      simpa using volume_cfCylinder_lt_one B.w B.hw_ne B.hw_pos
    obtain ⟨m', j', -, hsub', hrat'⟩ :=
      exists_cell_block B.hw_ne B.hw_pos ht1 hlt
    refine ⟨⟨B.w, B.hw_ne, B.hw_pos,
      fun d => if d = t + 1 then m' else B.m d,
      fun d => if d = t + 1 then j' else B.j d,
      fun d => if d = t + 1 then 2 else B.r d,
      ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
    · intro d hd2 hdt
      by_cases h : d = t + 1
      · rw [if_pos h]
        norm_num
      · rw [if_neg h]
        exact B.hr1 d hd2 (by omega)
    · intro d hd2 hdt
      by_cases h : d = t + 1
      · rw [if_pos h]
      · rw [if_neg h]
        exact B.hr2 d hd2 (by omega)
    · intro d hd2 hdt
      by_cases h : d = t + 1
      · subst h
        simpa using hsub'
      · simp only [if_neg h]
        exact B.hsub d hd2 (by omega)
    · intro d hd2 hdt
      by_cases h : d = t + 1
      · subst h
        simpa using hrat'
      · simp only [if_neg h]
        exact B.hratio d hd2 (by omega)
    · intro d hd2 hdt
      have h : d ≠ t + 1 := by omega
      simp [h]
  · -- degenerate `t = 0`: all base constraints on both sides are vacuous
    have ht0 : t = 0 := by omega
    subst ht0
    exact ⟨⟨B.w, B.hw_ne, B.hw_pos, B.m, B.j, B.r,
      fun d hd2 hdt => absurd hdt (by omega),
      fun d hd2 hdt => absurd hdt (by omega),
      fun d hd2 hdt => absurd hdt (by omega),
      fun d hd2 hdt => absurd hdt (by omega)⟩, rfl,
      fun d hd2 hdt => absurd hdt (by omega)⟩

/-- **The seed brick**: a 2-brick on any genuine CF word (start of the B–Y
induction, §2.1's initial step in brick form). -/
theorem exists_seed_brick (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : ∃ B : TBrick 2, B.w = w := by
  have hlt : volume (cfCylinder w)
      < ENNReal.ofReal (((2 : ℕ) : ℝ) ^ (0 : ℕ))⁻¹ := by
    simpa using volume_cfCylinder_lt_one w hw hpos
  obtain ⟨m', j', -, hsub', hrat'⟩ :=
    exists_cell_block hw hpos (le_refl 2) hlt
  refine ⟨⟨w, hw, hpos, fun _ => m', fun _ => j', fun _ => 2,
    fun _ _ _ => by norm_num, fun _ _ _ => le_refl 2, ?_, ?_⟩, rfl⟩
  · intro d hd2 hdt
    have : d = 2 := by omega
    subst this
    exact hsub'
  · intro d hd2 hdt
    have : d = 2 := by omega
    subst this
    simpa using hrat'

end NormalNumbers
