/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadThreshold

/-!
# A counting engine for Bugeaud 10.36, and `c⋆ ≤ 6`

**The engine (Rosenfeld-style counting).**  Fix a predicate `Bad k a` on the dyadic cells
`[a/2ᵏ, (a+1)/2ᵏ]`.  A cell is `Alive` when its parent is alive and it is not `Bad`; `cnt k` counts
the alive cells of level `k`.  Every alive cell has two children, so
`cnt (k+1) = 2 cnt k − #kills`, where the kills are the `Bad` children of alive parents
(`cnt_succ_add_card_kill`).  If every kill at level `k + 1` can be **charged to an alive ancestor**
at an earlier level `j`, with bounded multiplicity, then the kills are at most `Σ mⱼ cnt j`, and an
induction hypothesis `cnt (i+1) ≥ g i · cnt i` turns this into a multiple of `cnt k`
(`growth`).  No Frostman constant is needed: a kill is charged to the ancestor that *sees* it, not
to the mass near it.  The levels are nested compact sets, so a point lies in an alive cell of
every level (`exists_mem_cells`).

**The application: `c⋆ ≤ 6`** (`cStar_le_six`, improving `c⋆ ≤ 12`).  Base `2` is exact: the
last six binary digits of an alive cell are not all equal (`runBad`); such a kill at level `k+1`
is determined by its ancestor at level `k − 5` (multiplicity `≤ 2`).  A base `b ≥ 3` is counted:
the windows of order `n` (radius `b^{−n−6}` around `A/bⁿ`) are resolved at the level
`lv b n = ⌈log₂ b^{n+6}⌉`, meet at most `5` cells there (`card_meets_le`), and an ancestor at lag
`lag b = ⌊log₂(b⁶ − 2)⌋` meets at most one window of order `n` (`meets_unique`).  With
`g ≡ 5/3` the per-level balance is `2(3/5)⁵ + 5 Σ_{b ≥ 3} (3/5)^{lag b − 1} ≤ 1/3`
(`sum_weight_le`: the series is `≤ 0.0299 < 0.0355`).

The probe behind the constants is `scripts/cstar_models/ros3.py` (per-level slack `≈ 0.12` at
`Λ = 1.66` for all bases, `≈ 0` at `c = 5`).  The same engine with an exact joint `{2, 3}` core
and level-averaged charging is the planned route to `c⋆ ≤ 4` (`DIRECTION.md`, review lap
2026-10-07): binary-exact counting alone cannot reach `c = 4`.
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

namespace Count

/-! ## The engine -/

section Engine

variable (Bad : ℕ → ℕ → Prop)

/-- Alive dyadic cells: the root `0` at level `0`; a level-`(k+1)` cell `a` is alive when its
parent `a / 2` is alive and `Bad (k + 1) a` fails. -/
def Alive : ℕ → ℕ → Prop
  | 0, a => a = 0
  | k + 1, a => Alive k (a / 2) ∧ ¬ Bad (k + 1) a

theorem alive_lt : ∀ {k a : ℕ}, Alive Bad k a → a < 2 ^ k
  | 0, a, h => by simp only [Alive] at h; simp [h]
  | k + 1, a, h => by
    have := alive_lt h.1
    rw [pow_succ]; omega

/-- Ancestors of alive cells are alive. -/
theorem alive_anc : ∀ {k a : ℕ} (d : ℕ), Alive Bad (k + d) a → Alive Bad k (a / 2 ^ d)
  | k, a, 0, h => by simpa using h
  | k, a, d + 1, h => by
    have h1 : Alive Bad (k + d) (a / 2) := by
      have e : k + (d + 1) = (k + d) + 1 := by omega
      rw [e] at h; exact h.1
    have := alive_anc d h1
    rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this

open Classical in
/-- The alive cells of level `k`. -/
noncomputable def aliveSet (k : ℕ) : Finset ℕ := (Finset.range (2 ^ k)).filter (Alive Bad k)

/-- The number of alive cells of level `k`. -/
noncomputable def cnt (k : ℕ) : ℕ := (aliveSet Bad k).card

open Classical in
/-- The kills at level `k + 1`: `Bad` children of alive level-`k` cells. -/
noncomputable def killSet (k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ (k + 1))).filter (fun a => Alive Bad k (a / 2) ∧ Bad (k + 1) a)

theorem mem_aliveSet {k a : ℕ} : a ∈ aliveSet Bad k ↔ Alive Bad k a := by
  simp only [aliveSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨alive_lt Bad h, h⟩⟩

theorem mem_killSet {k a : ℕ} : a ∈ killSet Bad k ↔ Alive Bad k (a / 2) ∧ Bad (k + 1) a := by
  simp only [killSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have := alive_lt Bad h.1
  rw [pow_succ]; omega

theorem cnt_zero : cnt Bad 0 = 1 := by
  have : aliveSet Bad 0 = {0} := by
    ext a; rw [mem_aliveSet]; simp [Alive]
  simp [cnt, this]

/-- `cnt (k+1) = 2 cnt k − #kills`. -/
theorem cnt_succ_add_card_kill (k : ℕ) :
    cnt Bad (k + 1) + (killSet Bad k).card = 2 * cnt Bad k := by
  classical
  set C := (Finset.range (2 ^ (k + 1))).filter (fun a => Alive Bad k (a / 2)) with hC
  have hA : aliveSet Bad (k + 1) = C.filter (fun a => ¬ Bad (k + 1) a) := by
    ext a
    rw [mem_aliveSet, hC, Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact ⟨⟨alive_lt Bad h, h.1⟩, h.2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  have hK : killSet Bad k = C.filter (fun a => Bad (k + 1) a) := by
    ext a
    rw [mem_killSet, hC, Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact ⟨⟨by have := alive_lt Bad h.1; rw [pow_succ]; omega, h.1⟩, h.2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  have hCcard : C.card = 2 * cnt Bad k := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a => a / 2) (t := aliveSet Bad k)]
    · rw [cnt, Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (mem_aliveSet Bad).1 hp
      have hplt := alive_lt Bad hp'
      have e : C.filter (fun a => a / 2 = p) = {2 * p, 2 * p + 1} := by
        ext a
        simp only [C, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩; omega
        · rintro (rfl | rfl)
          · refine ⟨⟨by rw [pow_succ]; omega, ?_⟩, by omega⟩
            rwa [show 2 * p / 2 = p by omega]
          · refine ⟨⟨by rw [pow_succ]; omega, ?_⟩, by omega⟩
            rwa [show (2 * p + 1) / 2 = p by omega]
      rw [e, Finset.card_pair_eq_two_iff.2 (by omega)]
      rfl
    · intro a ha
      exact (mem_aliveSet Bad).2 (Finset.mem_filter.1 ha).2
  show (aliveSet Bad (k + 1)).card + (killSet Bad k).card = 2 * cnt Bad k
  rw [hA, hK, ← hCcard, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- Iterating the growth hypothesis below `k`. -/
theorem chain_le {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k) {k : ℕ}
    (h : ∀ i < k, g i * cnt Bad i ≤ cnt Bad (i + 1)) :
    ∀ j ≤ k, (cnt Bad j : ℝ) * ∏ i ∈ Finset.Ico j k, g i ≤ cnt Bad k := by
  suffices H : ∀ d, d ≤ k →
      (cnt Bad (k - d) : ℝ) * ∏ i ∈ Finset.Ico (k - d) k, g i ≤ cnt Bad k by
    intro j hj
    have := H (k - j) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self hj] at this
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have hsucc : k - (d + 1) + 1 = k - d := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : k - (d + 1) < k), hsucc]
    have h2 := h (k - (d + 1)) (by omega)
    rw [hsucc] at h2
    calc (cnt Bad (k - (d + 1)) : ℝ) * (g (k - (d + 1)) * ∏ i ∈ Finset.Ico (k - d) k, g i)
        = (g (k - (d + 1)) * cnt Bad (k - (d + 1))) * ∏ i ∈ Finset.Ico (k - d) k, g i := by
          ring
      _ ≤ cnt Bad (k - d) * ∏ i ∈ Finset.Ico (k - d) k, g i :=
          mul_le_mul_of_nonneg_right h2 (Finset.prod_nonneg fun i _ => hg i)
      _ ≤ cnt Bad k := h1

/-- **Counting engine.**  If, whenever the growth `cnt (i+1) ≥ g i · cnt i` holds below `k`, the
kills at level `k + 1` are at most `(2 − g k) cnt k`, then the growth holds at every level. -/
theorem growth {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k)
    (hkill : ∀ k, (∀ j ≤ k, (cnt Bad j : ℝ) * ∏ i ∈ Finset.Ico j k, g i ≤ cnt Bad k) →
      ((killSet Bad k).card : ℝ) ≤ (2 - g k) * cnt Bad k) :
    ∀ k, g k * cnt Bad k ≤ cnt Bad (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hk := hkill k (chain_le Bad hg fun i hi => ih i hi)
    have e := cnt_succ_add_card_kill Bad k
    have e' : (cnt Bad (k + 1) : ℝ) + (killSet Bad k).card = 2 * cnt Bad k := by
      exact_mod_cast e
    linarith

theorem cnt_pos {g : ℕ → ℝ} (hg : ∀ k, 0 < g k)
    (hgrow : ∀ k, g k * cnt Bad k ≤ cnt Bad (k + 1)) : ∀ k, 0 < cnt Bad k := by
  intro k
  induction k with
  | zero => rw [cnt_zero]; norm_num
  | succ k ih =>
    have h1 : (0 : ℝ) < g k * cnt Bad k := mul_pos (hg k) (by exact_mod_cast ih)
    exact_mod_cast h1.trans_le (hgrow k)

/-- The closed dyadic cell `[a/2ᵏ, (a+1)/2ᵏ]`. -/
def cell (k a : ℕ) : Set ℝ := Set.Icc ((a : ℝ) / 2 ^ k) (((a : ℝ) + 1) / 2 ^ k)

theorem cell_succ_sub (k a : ℕ) : cell (k + 1) a ⊆ cell k (a / 2) := by
  rintro x ⟨h1, h2⟩
  have ha : ((a / 2 : ℕ) : ℝ) * 2 ≤ a := by exact_mod_cast Nat.div_mul_le_self a 2
  have hb : (a : ℝ) + 1 ≤ (((a / 2 : ℕ) : ℝ) + 1) * 2 := by
    have : a + 1 ≤ (a / 2 + 1) * 2 := by omega
    exact_mod_cast this
  have hp : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  constructor
  · calc ((a / 2 : ℕ) : ℝ) / 2 ^ k = ((a / 2 : ℕ) : ℝ) * 2 / 2 ^ (k + 1) := by
          rw [pow_succ]; field_simp
      _ ≤ a / 2 ^ (k + 1) := by gcongr
      _ ≤ x := h1
  · calc x ≤ ((a : ℝ) + 1) / 2 ^ (k + 1) := h2
      _ ≤ (((a / 2 : ℕ) : ℝ) + 1) * 2 / 2 ^ (k + 1) := by gcongr
      _ = (((a / 2 : ℕ) : ℝ) + 1) / 2 ^ k := by rw [pow_succ]; field_simp

/-- **Limit point.**  If every level has an alive cell, some point lies in an alive cell of every
level. -/
theorem exists_mem_cells (hpos : ∀ k, 0 < cnt Bad k) :
    ∃ ξ : ℝ, ∀ k, ∃ a, Alive Bad k a ∧ ξ ∈ cell k a := by
  set t : ℕ → Set ℝ := fun k => ⋃ a ∈ aliveSet Bad k, cell k a with ht
  have hcpt : ∀ k, IsCompact (t k) := fun k =>
    (aliveSet Bad k).isCompact_biUnion fun a _ => isCompact_Icc
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun k x hx => by
      simp only [ht, Set.mem_iUnion] at hx ⊢
      obtain ⟨a, ha, hx⟩ := hx
      have ha' := (mem_aliveSet Bad).1 ha
      exact ⟨a / 2, (mem_aliveSet Bad).2 ha'.1, cell_succ_sub k a hx⟩)
    (fun k => by
      obtain ⟨a, ha⟩ := Finset.card_pos.1 (hpos k)
      refine ⟨(a : ℝ) / 2 ^ k, ?_⟩
      simp only [ht, Set.mem_iUnion]
      exact ⟨a, ha, le_rfl, by gcongr; linarith⟩)
    (hcpt 0) (fun k => (hcpt k).isClosed)
  refine ⟨ξ, fun k => ?_⟩
  have := Set.mem_iInter.1 hξ k
  simp only [ht, Set.mem_iUnion] at this
  obtain ⟨a, ha, hx⟩ := this
  exact ⟨a, (mem_aliveSet Bad).1 ha, hx⟩

/-- Charging: a set of children mapped into the alive cells of level `j` with fibres of size
`≤ m` has at most `m · cnt j` elements. -/
theorem card_le_of_charge (S : Finset ℕ) (f : ℕ → ℕ) (j m : ℕ)
    (hf : ∀ a ∈ S, Alive Bad j (f a)) (hm : ∀ q, (S.filter fun a => f a = q).card ≤ m) :
    S.card ≤ m * cnt Bad j := by
  classical
  exact Finset.card_le_mul_card_image_of_maps_to (fun a ha => (mem_aliveSet Bad).2 (hf a ha)) m
    fun q _ => hm q

end Engine

/-! ## The application: exponent `6` -/

section Six

/-- Base `2`: the last six binary digits of a level-`k` cell agree (`k ≥ 6`). -/
def runBad (k a : ℕ) : Prop := 6 ≤ k ∧ (a % 64 = 0 ∨ a % 64 = 63)

/-- The resolution level of the base-`b` windows of order `n`: `b^{n+6} ≤ 2^{lv} < 2 b^{n+6}`. -/
def lv (b n : ℕ) : ℕ := Nat.clog 2 (b ^ (n + 6))

/-- The closed cell `[a/2ᵏ, (a+1)/2ᵏ]` meets the open window of radius `b^{−n−6}` around `A/bⁿ`
(cleared of denominators). -/
def meets (k a b n A : ℕ) : Prop :=
  a * b ^ (n + 6) < 2 ^ k * (A * b ^ 6 + 1) ∧ 2 ^ k * (A * b ^ 6) < (a + 1) * b ^ (n + 6) + 2 ^ k

/-- The forbidden cells for exponent `6`. -/
def bad6 (k a : ℕ) : Prop := runBad k a ∨ ∃ b n A, 3 ≤ b ∧ lv b n = k ∧ meets k a b n A

/-- The lag at which base-`b` kills are charged: `2^{lag b} ≤ b⁶ − 2`. -/
def lag (b : ℕ) : ℕ := Nat.log 2 (b ^ 6 - 2)

theorem pow_le_two_pow_lv (b n : ℕ) : b ^ (n + 6) ≤ 2 ^ lv b n :=
  Nat.le_pow_clog (by norm_num) _

theorem two_pow_lv_lt {b n : ℕ} (hb : 2 ≤ b) : 2 ^ lv b n < 2 * b ^ (n + 6) := by
  have h1 : 1 < b ^ (n + 6) := Nat.one_lt_pow (by omega) (by omega)
  have h2 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h1
  have h3 : 0 < lv b n := Nat.clog_pos (by norm_num) h1
  obtain ⟨m, hm⟩ : ∃ m, lv b n = m + 1 := ⟨lv b n - 1, by omega⟩
  have h2' : 2 ^ m < b ^ (n + 6) := by
    have e : (lv b n).pred = m := by rw [hm]; rfl
    rw [← e]; exact h2
  rw [hm, pow_succ]; omega

theorem lv_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (lv b) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h1 := two_pow_lv_lt (n := n) hb
  have h2 := pow_le_two_pow_lv b (n + 1)
  have h3 : 2 * b ^ (n + 6) ≤ b ^ (n + 1 + 6) := by
    rw [show n + 1 + 6 = (n + 6) + 1 by ring, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ hb
  exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 (h1.trans_le (h3.trans h2))

theorem two_pow_lag_le {b : ℕ} (hb : 2 ≤ b) : 2 ^ lag b ≤ b ^ 6 - 2 := by
  have : 2 ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hb 6
  exact Nat.pow_log_le_self 2 (by omega)

theorem lag_lt_lv {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : lag b < lv b n := by
  have h1 := two_pow_lag_le hb
  have h2 : b ^ 6 ≤ b ^ (n + 6) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 := pow_le_two_pow_lv b n
  have h4 : 2 ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hb 6
  exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 (by omega)

theorem one_le_lag {b : ℕ} (hb : 3 ≤ b) : 1 ≤ lag b := by
  have : 3 ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hb 6
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- A window met by a cell is met by each of its ancestors. -/
theorem meets_anc {j D a b n A : ℕ} (h : meets (j + D) a b n A) :
    meets j (a / 2 ^ D) b n A := by
  obtain ⟨h1, h2⟩ := h
  rw [pow_add 2 j D] at h1 h2
  set q := a / 2 ^ D with hq
  set t := 2 ^ D with ht
  set P := b ^ (n + 6) with hP
  have htpos : 0 < t := by positivity
  have hq1 : q * t ≤ a := Nat.div_mul_le_self a t
  have hq2 : a + 1 ≤ (q + 1) * t := by
    have := Nat.div_add_mod a t
    have := Nat.mod_lt a htpos
    nlinarith
  constructor
  · have h3 : q * t * P ≤ a * P := Nat.mul_le_mul_right _ hq1
    have : q * P * t < 2 ^ j * (A * b ^ 6 + 1) * t := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  · have h3 : (a + 1) * P ≤ (q + 1) * t * P := Nat.mul_le_mul_right _ hq2
    have : 2 ^ j * (A * b ^ 6) * t < ((q + 1) * P + 2 ^ j) * t := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this

/-- An ancestor at lag `D` with `2^D ≤ b⁶ − 2` meets at most one window of each order. -/
theorem meets_unique {j k b n A A' q : ℕ} (hb : 2 ≤ b) (hjk : 2 ^ k ≤ 2 ^ j * (b ^ 6 - 2))
    (hP : b ^ (n + 6) ≤ 2 ^ k) (h : meets j q b n A) (h' : meets j q b n A') : A = A' := by
  have key : ∀ {A A'}, meets j q b n A → meets j q b n A' → A < A' → False := by
    intro A A' h h' hlt
    obtain ⟨h1, -⟩ := h
    obtain ⟨-, h2⟩ := h'
    set R := 2 ^ j
    set P := b ^ (n + 6)
    set B := b ^ 6
    have hB : 2 ≤ B := by
      have : 2 ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hb 6
      omega
    have h3 : R * ((A + 1) * B) ≤ R * (A' * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlt)
    have h4 : R * (B - 2) + R * 2 = R * B := by rw [← mul_add, Nat.sub_add_cancel hB]
    nlinarith
  rcases Nat.lt_trichotomy A A' with hlt | heq | hlt
  · exact (key h h' hlt).elim
  · exact heq
  · exact (key h' h hlt).elim

open Classical in
/-- A window of order `n` meets at most `5` cells of its resolution level. -/
theorem card_meets_le (k b n A : ℕ) (hlv : 2 ^ k < 2 * b ^ (n + 6)) :
    ((Finset.range (2 ^ k)).filter (fun a => meets k a b n A)).card ≤ 5 := by
  set S := (Finset.range (2 ^ k)).filter (fun a => meets k a b n A)
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  set m := S.min' h
  have hm : m ∈ S := S.min'_mem h
  have hmS := (Finset.mem_filter.1 hm).2
  have hsub : S ⊆ Finset.Icc m (m + 4) := by
    intro a ha
    have haS := (Finset.mem_filter.1 ha).2
    refine Finset.mem_Icc.2 ⟨S.min'_le a ha, ?_⟩
    obtain ⟨h1, -⟩ := haS
    obtain ⟨-, h2⟩ := hmS
    have : a * b ^ (n + 6) < (m + 5) * b ^ (n + 6) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  calc S.card ≤ (Finset.Icc m (m + 4)).card := Finset.card_le_card hsub
    _ = 5 := by rw [Nat.card_Icc]; omega

open Classical in
/-- Base-`2` kills at level `k + 1` (`≥ 6`), charged to the ancestor at level `k − 5`. -/
theorem card_runKill_le (k : ℕ) (h6 : 6 ≤ k + 1) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad6 k (a / 2) ∧ runBad (k + 1) a)).card ≤ 2 * cnt bad6 (k + 1 - 6) := by
  refine card_le_of_charge bad6 _ (fun a => a / 64) (k + 1 - 6) 2 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = (k + 1 - 6) + 5 := by omega
    rw [e] at ha
    have := alive_anc bad6 5 ha
    rwa [Nat.div_div_eq_div_mul] at this
  · calc _ ≤ ({64 * q, 64 * q + 63} : Finset ℕ).card := by
          refine Finset.card_le_card fun a ha => ?_
          obtain ⟨ha', hq⟩ := Finset.mem_filter.1 ha
          obtain ⟨-, -, -, h⟩ := Finset.mem_filter.1 ha'
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      _ ≤ 2 := Finset.card_le_two

open Classical in
/-- Base-`b` kills at level `k + 1`, charged to the ancestor at lag `lag b`. -/
theorem card_winKill_le (k b : ℕ) (hb : 3 ≤ b) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad6 k (a / 2) ∧ ∃ n A, lv b n = k + 1 ∧ meets (k + 1) a b n A)).card ≤
      5 * cnt bad6 (k + 1 - lag b) := by
  set S := (Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad6 k (a / 2) ∧ ∃ n A, lv b n = k + 1 ∧ meets (k + 1) a b n A)
  rcases S.eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
  · rw [hS]; simp
  obtain ⟨-, -, n₀, A₀, hn₀, hA₀⟩ := Finset.mem_filter.1 ha₀
  have hb2 : 2 ≤ b := by omega
  have hlag := lag_lt_lv hb2 n₀
  have hlag1 := one_le_lag hb
  rw [hn₀] at hlag
  set j := k + 1 - lag b with hj
  have ejk : k + 1 = j + lag b := by omega
  refine card_le_of_charge bad6 S (fun a => a / 2 ^ lag b) j 5 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = j + (lag b - 1) := by omega
    rw [e] at ha
    have := alive_anc bad6 (lag b - 1) ha
    rwa [Nat.div_div_eq_div_mul, ← pow_succ', show lag b - 1 + 1 = lag b by omega] at this
  · -- every member of the fibre meets the window `(n₀, A₀')` of the fibre's ancestor
    rcases (S.filter fun a => a / 2 ^ lag b = q).eq_empty_or_nonempty with hF | ⟨a₁, ha₁⟩
    · rw [hF]; simp
    obtain ⟨ha₁S, hq₁⟩ := Finset.mem_filter.1 ha₁
    obtain ⟨-, -, n₁, A₁, hn₁, hA₁⟩ := Finset.mem_filter.1 ha₁S
    have hjk : 2 ^ (k + 1) ≤ 2 ^ j * (b ^ 6 - 2) := by
      rw [ejk, pow_add]; exact Nat.mul_le_mul_left _ (two_pow_lag_le hb2)
    have hP : b ^ (n₁ + 6) ≤ 2 ^ (k + 1) := hn₁ ▸ pow_le_two_pow_lv b n₁
    have hsub : S.filter (fun a => a / 2 ^ lag b = q) ⊆
        (Finset.range (2 ^ (k + 1))).filter (fun a => meets (k + 1) a b n₁ A₁) := by
      intro a ha
      obtain ⟨haS, hq⟩ := Finset.mem_filter.1 ha
      obtain ⟨hr, -, n, A, hn, hA⟩ := Finset.mem_filter.1 haS
      have hnn : n = n₁ := (lv_strictMono hb2).injective (hn.trans hn₁.symm)
      subst hnn
      have m1 : meets j q b n A := by
        rw [ejk] at hA; have := meets_anc hA; rwa [hq] at this
      have m2 : meets j q b n A₁ := by
        rw [ejk] at hA₁; have := meets_anc hA₁; rwa [hq₁] at this
      have hAA := meets_unique hb2 hjk hP m1 m2
      subst hAA
      exact Finset.mem_filter.2 ⟨hr, hA⟩
    exact (Finset.card_le_card hsub).trans
      (card_meets_le (k + 1) b n₁ A₁ (hn₁ ▸ two_pow_lv_lt hb2))

/-! ### The per-level balance -/

theorem lag_ge {b d : ℕ} (h : 2 ^ d ≤ b ^ 6 - 2) : d ≤ lag b :=
  Nat.le_log_of_pow_le (by norm_num) h

theorem tail_seq : ∀ L, 17 ≤ L → (2 : ℝ) ^ (L + 2) * ((3 : ℝ) / 5) ^ (3 * (L - 1)) ≤ 1 / 64000 := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have e1 : (2 : ℝ) ^ (L + 1 + 2) = 2 ^ (L + 2) * 2 := by
      rw [show L + 1 + 2 = (L + 2) + 1 by ring, pow_succ]
    have e2 : ((3 : ℝ) / 5) ^ (3 * (L + 1 - 1)) = ((3 : ℝ) / 5) ^ (3 * (L - 1)) * ((3 : ℝ) / 5) ^ 3 := by
      rw [← pow_add]; congr 1; omega
    rw [e1, e2]
    calc (2 : ℝ) ^ (L + 2) * 2 * (((3 : ℝ) / 5) ^ (3 * (L - 1)) * ((3 : ℝ) / 5) ^ 3)
        = ((2 : ℝ) ^ (L + 2) * ((3 : ℝ) / 5) ^ (3 * (L - 1))) * (2 * ((3 : ℝ) / 5) ^ 3) := by ring
      _ ≤ 1 / 64000 * (2 * ((3 : ℝ) / 5) ^ 3) := by gcongr
      _ ≤ 1 / 64000 := by norm_num

/-- For `b ≥ 8`, `(3/5)^{lag b − 1} ≤ (1/40)/(b(b−1))`. -/
theorem weight_tail {b : ℕ} (hb : 8 ≤ b) :
    ((3 : ℝ) / 5) ^ (lag b - 1) ≤ 1 / 40 * (1 / ((b : ℝ) * ((b : ℝ) - 1))) := by
  have hb6 : 8 ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hb 6
  have hL : 17 ≤ lag b := lag_ge (by norm_num at hb6 ⊢; omega)
  have hlt : b ^ 6 < 2 ^ (lag b + 2) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (b ^ 6 - 2)
    have h2 : 2 ≤ 2 ^ (Nat.log 2 (b ^ 6 - 2)).succ := Nat.le_self_pow (by omega) 2
    have e : 2 ^ (lag b + 2) = 2 * 2 ^ (Nat.log 2 (b ^ 6 - 2)).succ := by
      rw [lag, pow_succ, pow_succ, pow_succ]; ring
    rw [e]; omega
  have hlt' : (b : ℝ) ^ 6 < 2 ^ (lag b + 2) := by exact_mod_cast hlt
  have hbR : (8 : ℝ) ≤ b := by exact_mod_cast hb
  have hbb : 0 < (b : ℝ) * ((b : ℝ) - 1) := by nlinarith
  set x := (b : ℝ) * ((b : ℝ) - 1) * ((3 : ℝ) / 5) ^ (lag b - 1) with hx
  have hx0 : 0 ≤ x := by positivity
  have hcube : x ^ 3 ≤ (1 / 40 : ℝ) ^ 3 := by
    have h1 : ((b : ℝ) * ((b : ℝ) - 1)) ^ 3 ≤ (b : ℝ) ^ 6 := by
      have : (b : ℝ) * ((b : ℝ) - 1) ≤ (b : ℝ) ^ 2 := by nlinarith
      calc ((b : ℝ) * ((b : ℝ) - 1)) ^ 3 ≤ ((b : ℝ) ^ 2) ^ 3 := by gcongr
        _ = (b : ℝ) ^ 6 := by ring
    calc x ^ 3 = ((b : ℝ) * ((b : ℝ) - 1)) ^ 3 * ((3 : ℝ) / 5) ^ (3 * (lag b - 1)) := by
          rw [hx, mul_pow, ← pow_mul, mul_comm (lag b - 1) 3]
      _ ≤ (2 : ℝ) ^ (lag b + 2) * ((3 : ℝ) / 5) ^ (3 * (lag b - 1)) := by
          gcongr; exact h1.trans hlt'.le
      _ ≤ 1 / 64000 := tail_seq _ hL
      _ = (1 / 40 : ℝ) ^ 3 := by norm_num
  have hx1 : x ≤ 1 / 40 := le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hcube
  rw [hx] at hx1
  rw [mul_one_div, le_div_iff₀ hbb]
  linarith

theorem telescope : ∀ N : ℕ, 7 ≤ N →
    ∑ b ∈ Finset.Ioc 7 N, 1 / ((b : ℝ) * ((b : ℝ) - 1)) = 1 / 7 - 1 / (N : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN, ih]
    have h0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    push_cast
    rw [show (N : ℝ) + 1 - 1 = N by ring]
    field_simp
    ring

/-- **The base series.**  `Σ_{3 ≤ b ≤ M} (3/5)^{lag b − 1} ≤ 7/200` (it is about `0.0299`). -/
theorem sum_weight_le (M : ℕ) : ∑ b ∈ Finset.Ioc 2 M, ((3 : ℝ) / 5) ^ (lag b - 1) ≤ 7 / 200 := by
  set f : ℕ → ℝ := fun b => ((3 : ℝ) / 5) ^ (lag b - 1) with hf
  have hf0 : ∀ b, 0 ≤ f b := fun b => by positivity
  have hμ0 : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hμ1 : (3 : ℝ) / 5 ≤ 1 := by norm_num
  have hsmall : ∑ b ∈ Finset.Ioc 2 7, f b ≤
      ((3 : ℝ) / 5) ^ 8 + ((3 : ℝ) / 5) ^ 10 + ((3 : ℝ) / 5) ^ 12 + ((3 : ℝ) / 5) ^ 14 +
        ((3 : ℝ) / 5) ^ 15 := by
    rw [show Finset.Ioc 2 7 = {3, 4, 5, 6, 7} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have l3 : 9 ≤ lag 3 := lag_ge (by norm_num)
    have l4 : 11 ≤ lag 4 := lag_ge (by norm_num)
    have l5 : 13 ≤ lag 5 := lag_ge (by norm_num)
    have l6 : 15 ≤ lag 6 := lag_ge (by norm_num)
    have l7 : 16 ≤ lag 7 := lag_ge (by norm_num)
    have t3 : ((3 : ℝ) / 5) ^ (lag 3 - 1) ≤ ((3 : ℝ) / 5) ^ 8 :=
      pow_le_pow_of_le_one hμ0 hμ1 (by omega)
    have t4 : ((3 : ℝ) / 5) ^ (lag 4 - 1) ≤ ((3 : ℝ) / 5) ^ 10 :=
      pow_le_pow_of_le_one hμ0 hμ1 (by omega)
    have t5 : ((3 : ℝ) / 5) ^ (lag 5 - 1) ≤ ((3 : ℝ) / 5) ^ 12 :=
      pow_le_pow_of_le_one hμ0 hμ1 (by omega)
    have t6 : ((3 : ℝ) / 5) ^ (lag 6 - 1) ≤ ((3 : ℝ) / 5) ^ 14 :=
      pow_le_pow_of_le_one hμ0 hμ1 (by omega)
    have t7 : ((3 : ℝ) / 5) ^ (lag 7 - 1) ≤ ((3 : ℝ) / 5) ^ 15 :=
      pow_le_pow_of_le_one hμ0 hμ1 (by omega)
    simp only [hf]
    linarith
  have htail : ∀ N, 7 ≤ N → ∑ b ∈ Finset.Ioc 7 N, f b ≤ 1 / 40 * (1 / 7) := by
    intro N hN
    calc ∑ b ∈ Finset.Ioc 7 N, f b
        ≤ ∑ b ∈ Finset.Ioc 7 N, 1 / 40 * (1 / ((b : ℝ) * ((b : ℝ) - 1))) :=
          Finset.sum_le_sum fun b hb => weight_tail (by have := (Finset.mem_Ioc.1 hb).1; omega)
      _ = 1 / 40 * (1 / 7 - 1 / N) := by rw [← Finset.mul_sum, telescope N hN]
      _ ≤ 1 / 40 * (1 / 7) := by
          have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          gcongr; linarith [one_div_pos.2 this]
  calc ∑ b ∈ Finset.Ioc 2 M, f b ≤ ∑ b ∈ Finset.Ioc 2 (M + 7), f b :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_right (by omega)) fun b _ _ => hf0 b
    _ = ∑ b ∈ Finset.Ioc 2 7, f b + ∑ b ∈ Finset.Ioc 7 (M + 7), f b :=
        (Finset.sum_Ioc_consecutive f (by norm_num) (by omega)).symm
    _ ≤ _ := add_le_add hsmall (htail _ (by omega))
    _ ≤ 7 / 200 := by norm_num

open Classical in
theorem killSet_subset (k : ℕ) :
    killSet bad6 k ⊆ ((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad6 k (a / 2) ∧ runBad (k + 1) a)) ∪
      (Finset.Ioc 2 (2 ^ (k + 1))).biUnion (fun b => (Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad6 k (a / 2) ∧ ∃ n A, lv b n = k + 1 ∧ meets (k + 1) a b n A)) := by
  intro a ha
  have hr : a ∈ Finset.range (2 ^ (k + 1)) := (Finset.mem_filter.1 ha).1
  obtain ⟨hal, hbad⟩ := (mem_killSet bad6).1 ha
  rcases hbad with hrun | ⟨b, n, A, hb, hn, hm⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hr, hal, hrun⟩)
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, Finset.mem_Ioc.2 ⟨hb, ?_⟩,
      Finset.mem_filter.2 ⟨hr, hal, n, A, hn, hm⟩⟩)
    calc b ≤ b ^ (n + 6) := Nat.le_self_pow (by omega) b
      _ ≤ 2 ^ lv b n := pow_le_two_pow_lv b n
      _ = 2 ^ (k + 1) := by rw [hn]

/-- **Per-level kill bound** for exponent `6`, under the growth `cnt (i+1) ≥ (5/3) cnt i` below
`k`: the kills at level `k + 1` are at most `cnt k / 3`. -/
theorem card_kill_le (k : ℕ)
    (hch : ∀ j ≤ k, (cnt bad6 j : ℝ) * ∏ _i ∈ Finset.Ico j k, ((5 : ℝ) / 3) ≤ cnt bad6 k) :
    ((killSet bad6 k).card : ℝ) ≤ (2 - 5 / 3) * cnt bad6 k := by
  classical
  have hj : ∀ j ≤ k, (cnt bad6 j : ℝ) ≤ ((3 : ℝ) / 5) ^ (k - j) * cnt bad6 k := by
    intro j hjk
    have h := hch j hjk
    rw [Finset.prod_const, Nat.card_Ico] at h
    have e : ((5 : ℝ) / 3) ^ (k - j) * ((3 : ℝ) / 5) ^ (k - j) = 1 := by
      rw [← mul_pow]; norm_num
    have hμ : (0 : ℝ) ≤ ((3 : ℝ) / 5) ^ (k - j) := by positivity
    calc (cnt bad6 j : ℝ) = (cnt bad6 j * ((5 : ℝ) / 3) ^ (k - j)) * ((3 : ℝ) / 5) ^ (k - j) := by
          rw [mul_assoc, e, mul_one]
      _ ≤ cnt bad6 k * ((3 : ℝ) / 5) ^ (k - j) := mul_le_mul_of_nonneg_right h hμ
      _ = _ := mul_comm _ _
  have hck : (0 : ℝ) ≤ cnt bad6 k := by positivity
  -- runs
  have hrun : (((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad6 k (a / 2) ∧ runBad (k + 1) a)).card : ℝ) ≤
      2 * ((3 : ℝ) / 5) ^ 5 * cnt bad6 k := by
    by_cases h6 : 6 ≤ k + 1
    · have h1 := (Nat.cast_le (α := ℝ)).2 (card_runKill_le k h6)
      push_cast at h1
      have h2 := hj (k - 5) (by omega)
      rw [show k - (k - 5) = 5 by omega] at h2
      linarith
    · have : (Finset.range (2 ^ (k + 1))).filter
          (fun a => Alive bad6 k (a / 2) ∧ runBad (k + 1) a) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun a _ h => ?_
        exact h6 h.2.1
      rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  -- windows
  have hwin : ∀ b ∈ Finset.Ioc 2 (2 ^ (k + 1)), (((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad6 k (a / 2) ∧ ∃ n A, lv b n = k + 1 ∧ meets (k + 1) a b n A)).card : ℝ) ≤
      5 * (((3 : ℝ) / 5) ^ (lag b - 1) * cnt bad6 k) := by
    intro b hb
    have hb3 : 3 ≤ b := (Finset.mem_Ioc.1 hb).1
    by_cases hl : lag b ≤ k
    · have h1 := (Nat.cast_le (α := ℝ)).2 (card_winKill_le k b hb3)
      push_cast at h1
      have hl1 := one_le_lag hb3
      have h2 := hj (k + 1 - lag b) (by omega)
      rw [show k - (k + 1 - lag b) = lag b - 1 by omega] at h2
      linarith
    · have : (Finset.range (2 ^ (k + 1))).filter
          (fun a => Alive bad6 k (a / 2) ∧ ∃ n A, lv b n = k + 1 ∧ meets (k + 1) a b n A) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun a _ h => ?_
        obtain ⟨-, n, A, hn, -⟩ := h
        have := lag_lt_lv (by omega : 2 ≤ b) n
        omega
      rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hcard := (Finset.card_le_card (killSet_subset k)).trans (Finset.card_union_le _ _)
  have hcard' := hcard.trans (Nat.add_le_add_left Finset.card_biUnion_le _)
  have hR : ((killSet bad6 k).card : ℝ) ≤
      (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad6 k (a / 2) ∧ runBad (k + 1) a)).card : ℝ) +
      ∑ b ∈ Finset.Ioc 2 (2 ^ (k + 1)), (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad6 k (a / 2) ∧ ∃ n A, lv b n = k + 1 ∧ meets (k + 1) a b n A)).card : ℝ) := by
    exact_mod_cast hcard'
  have hsum := Finset.sum_le_sum hwin
  have hS := sum_weight_le (2 ^ (k + 1))
  have h5 : ∑ b ∈ Finset.Ioc 2 (2 ^ (k + 1)), 5 * (((3 : ℝ) / 5) ^ (lag b - 1) * cnt bad6 k) =
      5 * (∑ b ∈ Finset.Ioc 2 (2 ^ (k + 1)), ((3 : ℝ) / 5) ^ (lag b - 1)) * cnt bad6 k := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have h6 : 5 * (∑ b ∈ Finset.Ioc 2 (2 ^ (k + 1)), ((3 : ℝ) / 5) ^ (lag b - 1)) * cnt bad6 k ≤
      5 * (7 / 200) * cnt bad6 k := by gcongr
  have h7 : 2 * ((3 : ℝ) / 5) ^ 5 + 5 * (7 / 200) ≤ 2 - 5 / 3 := by norm_num
  have h8 := mul_le_mul_of_nonneg_right h7 hck
  linarith

/-- The exponent-`6` tree grows by `5/3` per level. -/
theorem growth_six : ∀ k, (5 / 3 : ℝ) * cnt bad6 k ≤ cnt bad6 (k + 1) :=
  growth bad6 (g := fun _ => 5 / 3) (fun _ => by norm_num) fun k hch => card_kill_le k hch

/-! ### From cells to the Diophantine condition -/

theorem dnear_two_ge {ξ : ℝ} {n a : ℕ} (hξ : ξ ∈ cell (n + 6) a) (h : ¬ runBad (n + 6) a) :
    ((2 : ℝ) ^ 6)⁻¹ ≤ dnear ((2 : ℝ) ^ n * ξ) := by
  have hs : a % 64 ≠ 0 ∧ a % 64 ≠ 63 := by
    simp only [runBad, not_and, not_or] at h; exact h (by omega)
  obtain ⟨h1, h2⟩ := hξ
  set x := (2 : ℝ) ^ n * ξ with hx
  have e : (2 : ℝ) ^ (n + 6) = 2 ^ n * 64 := by rw [pow_add]; norm_num
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hx1 : (a : ℝ) / 64 ≤ x := by
    rw [e] at h1
    calc (a : ℝ) / 64 = 2 ^ n * ((a : ℝ) / (2 ^ n * 64)) := by field_simp
      _ ≤ x := by rw [hx]; gcongr
  have hx2 : x ≤ ((a : ℝ) + 1) / 64 := by
    rw [e] at h2
    calc x ≤ 2 ^ n * (((a : ℝ) + 1) / (2 ^ n * 64)) := by rw [hx]; gcongr
      _ = ((a : ℝ) + 1) / 64 := by field_simp
  have ha : (a : ℝ) = 64 * ((a / 64 : ℕ) : ℝ) + ((a % 64 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod a 64).symm
  have hs1 : (1 : ℝ) ≤ ((a % 64 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ a % 64)
  have hs2 : ((a % 64 : ℕ) : ℝ) ≤ 62 := by
    exact_mod_cast (by have := Nat.mod_lt a (by norm_num : 64 > 0); omega : a % 64 ≤ 62)
  unfold dnear
  rcases le_or_gt (round x) ((a / 64 : ℕ) : ℤ) with hm | hm
  · have hm' : ((round x : ℤ) : ℝ) ≤ ((a / 64 : ℕ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).2 hm
      rwa [Int.cast_natCast] at this
    rw [abs_of_nonneg (by linarith)]
    norm_num
    linarith
  · have hm' : ((a / 64 : ℕ) : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by
      have hm2 : ((a / 64 : ℕ) : ℤ) + 1 ≤ round x := hm
      have := (Int.cast_le (R := ℝ)).2 hm2
      rwa [Int.cast_add, Int.cast_natCast, Int.cast_one] at this
    rw [abs_of_nonpos (by linarith)]
    norm_num
    linarith

theorem dnear_ge_of_cell {ξ : ℝ} {b n a : ℕ} (hb : 2 ≤ b) (hξ : ξ ∈ cell (lv b n) a)
    (h : ∀ A, ¬ meets (lv b n) a b n A) : ((b : ℝ) ^ 6)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨h1, h2⟩ := hξ
  set k := lv b n
  set x := (b : ℝ) ^ n * ξ with hx
  have hQ : (0 : ℝ) < 2 ^ k := by positivity
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hB : (0 : ℝ) < (b : ℝ) ^ 6 := by positivity
  have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hξ0 : 0 ≤ ξ := le_trans (by positivity) h1
  have hx0 : 0 ≤ x := by positivity
  have hd : |x - round x| < ((b : ℝ) ^ 6)⁻¹ := hlt
  have hB1 : ((b : ℝ) ^ 6)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b)))
  have hr0 : 0 ≤ round x := by
    by_contra hneg
    replace hneg := not_le.1 hneg
    have : ((round x : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : round x ≤ -1)
    have := (abs_lt.1 hd).2
    linarith
  set A := (round x).toNat with hA
  have hAx : ((A : ℕ) : ℝ) = ((round x : ℤ) : ℝ) := by
    rw [hA]; exact_mod_cast Int.toNat_of_nonneg hr0
  obtain ⟨hd1, hd2⟩ := abs_lt.1 hd
  rw [← hAx] at hd1 hd2
  -- clear denominators
  have hBx1 : (b : ℝ) ^ 6 * x < (b : ℝ) ^ 6 * A + 1 := by
    have := mul_lt_mul_of_pos_left hd2 hB
    rw [mul_sub, mul_inv_cancel₀ hB.ne'] at this; linarith
  have hBx2 : (b : ℝ) ^ 6 * A < (b : ℝ) ^ 6 * x + 1 := by
    have := mul_lt_mul_of_pos_left hd1 hB
    rw [mul_sub, mul_neg, mul_inv_cancel₀ hB.ne'] at this; linarith
  have ha1 : (a : ℝ) ≤ 2 ^ k * ξ := by rwa [div_le_iff₀ hQ, mul_comm] at h1
  have ha2 : 2 ^ k * ξ ≤ (a : ℝ) + 1 := by rwa [le_div_iff₀ hQ, mul_comm] at h2
  refine h A ⟨?_, ?_⟩
  · have key : (a : ℝ) * (b : ℝ) ^ (n + 6) < 2 ^ k * (A * (b : ℝ) ^ 6 + 1) := by
      have e1 : (b : ℝ) ^ (n + 6) = (b : ℝ) ^ n * (b : ℝ) ^ 6 := pow_add _ _ _
      have hP : (0 : ℝ) < (b : ℝ) ^ (n + 6) := by positivity
      calc (a : ℝ) * (b : ℝ) ^ (n + 6) ≤ 2 ^ k * ξ * (b : ℝ) ^ (n + 6) :=
            mul_le_mul_of_nonneg_right ha1 hP.le
        _ = 2 ^ k * ((b : ℝ) ^ 6 * x) := by rw [e1, hx]; ring
        _ < 2 ^ k * ((b : ℝ) ^ 6 * A + 1) := mul_lt_mul_of_pos_left hBx1 hQ
        _ = 2 ^ k * (A * (b : ℝ) ^ 6 + 1) := by ring
    exact_mod_cast key
  · have key : (2 : ℝ) ^ k * (A * (b : ℝ) ^ 6) < (a + 1) * (b : ℝ) ^ (n + 6) + 2 ^ k := by
      have e1 : (b : ℝ) ^ (n + 6) = (b : ℝ) ^ n * (b : ℝ) ^ 6 := pow_add _ _ _
      have hP : (0 : ℝ) < (b : ℝ) ^ (n + 6) := by positivity
      calc (2 : ℝ) ^ k * (A * (b : ℝ) ^ 6) = 2 ^ k * ((b : ℝ) ^ 6 * A) := by ring
        _ < 2 ^ k * ((b : ℝ) ^ 6 * x + 1) := mul_lt_mul_of_pos_left hBx2 hQ
        _ = 2 ^ k * ξ * (b : ℝ) ^ (n + 6) + 2 ^ k := by rw [e1, hx]; ring
        _ ≤ (a + 1) * (b : ℝ) ^ (n + 6) + 2 ^ k := by
            gcongr
    exact_mod_cast key

/-- **Exponent `6` is attained (non-strictly).**  Some `ξ` has `‖bⁿξ‖ ≥ b^{−6}` for every base
`b ≥ 2` and every `n ≥ 0`. -/
@[blueprint (title := "A real number with ‖bⁿξ‖ ≥ b^(-6) for every base b and every n")]
theorem exists_good_six :
    ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, ((b : ℝ) ^ 6)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  have hpos := cnt_pos bad6 (g := fun _ => (5 : ℝ) / 3) (fun _ => by norm_num) growth_six
  obtain ⟨ξ, hξ⟩ := exists_mem_cells bad6 hpos
  refine ⟨ξ, fun b hb n => ?_⟩
  rcases Nat.lt_or_ge b 3 with hb3 | hb3
  · obtain rfl : b = 2 := by omega
    obtain ⟨a, ha, hx⟩ := hξ (n + 6)
    have hnot : ¬ runBad (n + 6) a := fun h => ha.2 (Or.inl h)
    simpa using dnear_two_ge hx hnot
  · obtain ⟨a, ha, hx⟩ := hξ (lv b n)
    refine dnear_ge_of_cell hb hx fun A hA => ?_
    have hlv : 0 < lv b n := lt_of_le_of_lt (Nat.zero_le _) (lag_lt_lv hb n)
    obtain ⟨m, hm⟩ : ∃ m, lv b n = m + 1 := ⟨lv b n - 1, by omega⟩
    rw [hm] at ha hA
    exact ha.2 (Or.inr ⟨b, n, A, hb3, hm, hA⟩)

end Six

end Count

/-- Every exponent `c > 6` is admissible (`Count.exists_good_six`). -/
theorem admissible_of_six_lt {c : ℝ} (hc : 6 < c) : Admissible c := by
  obtain ⟨ξ, hξ⟩ := Count.exists_good_six
  refine ⟨ξ, fun b hb n => lt_of_lt_of_le ?_ (hξ b hb n)⟩
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have h1 : (b : ℝ) ^ ((6 : ℕ) : ℝ) < (b : ℝ) ^ c :=
    Real.rpow_lt_rpow_of_exponent_lt hb1 (by exact_mod_cast hc)
  rw [Real.rpow_natCast] at h1
  rw [Real.rpow_neg (by positivity)]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 h1

/-- **`c⋆ ≤ 6`**, by the counting engine (`Count.growth`): base `2` exact through its runs, every
base `b ≥ 3` charged to an ancestor at lag `⌊log₂(b⁶ − 2)⌋`.  Improves `cStar_le_twelve`. -/
@[blueprint (title := "Bugeaud 10.36 optimal exponent: c⋆ ≤ 6 by counting")]
theorem cStar_le_six : cStar ≤ 6 :=
  le_of_forall_gt_imp_ge_of_dense fun _ hc =>
    csInf_le bddBelow_admissible (admissible_of_six_lt hc)

end NormalNumbers.UniformBadThreshold
