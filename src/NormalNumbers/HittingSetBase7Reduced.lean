/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetReduced
import NormalNumbers.Literature

/-!
# `S(7,1) ≤ 7`: 7 multipliers hit every base-7 word of length 1 🧵

Emitted by `experiments/emit_hitting_lean.py` from the multiplier set
`{1, 2, 3, 4, 5, 6, 13}` (`experiments/hitting_set_search_reduced.py`).

The ambient state space of this `gfamPred` family is `∏ᵢ mᵢ·7^0 = 9360`.
The carry-consistency reduction (`HittingSetReduced.lean`) cuts it to **24 states**:
all channels read the same `X`, so with `t = fract(X·7ᵐ)` the joint state is
`stateOfKW 7 N 1 ms ⌊N·t⌋` for `N = lcm {a·7^j} = 780`.

Reachability is kernel `decide +kernel` by **run compression**: `stateOfKW` reads
`k` only through the monotone quotients `(b·k)/N`, so the sweep over `k < 780`
is one check per run — **24 runs**.  No `native_decide` anywhere.

* `hitting_7_1_seven_reduced` : `S(7,1) ≤ 7` via `{1, 2, 3, 4, 5, 6, 13}`.

This is the SAME statement as `hitting_7_1_seven` (`HittingSetBase7.lean`), which
proves it by a chunked kernel sweep over the `9360` ambient states.  Neither file
is deleted: the old one is the independent check.

Nothing here claims the matching lower bound `S(7,1) ≥ 7`.
-/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

/-- The 7 multipliers. -/
def h71rms : List ℕ := [1, 2, 3, 4, 5, 6, 13]

/-- `lcm {a·7^j : a ∈ ms, j ≤ 0}`: the index range of the reachable curve. -/
def h71rN : ℕ := 780

/-- The 24 reachable joint states, sorted. -/
def h71rL : Array ℕ := #[0, 720, 1440, 1560, 1584, 2304, 2310, 3030, 3152, 3872, 3896, 4616, 4743, 5463, 5487, 6207, 6329, 7049, 7055, 7775, 7799, 7919, 8639, 9359]

/-- The `j`-th state, as a balanced if-tree.  `h71rL.getD j 0` would be
`O(j)` in the KERNEL (it walks the literal), which makes the run sweep quadratic
in the number of runs; this is `O(log 24)`. -/
def h71rLget (j : ℕ) : ℕ := if j < 12 then if j < 6 then if j < 3 then if j < 1 then 0 else if j < 2 then 720 else 1440 else if j < 4 then 1560 else if j < 5 then 1584 else 2304 else if j < 9 then if j < 7 then 2310 else if j < 8 then 3030 else 3152 else if j < 10 then 3872 else if j < 11 then 3896 else 4616 else if j < 18 then if j < 15 then if j < 13 then 4743 else if j < 14 then 5463 else 5487 else if j < 16 then 6207 else if j < 17 then 6329 else 7049 else if j < 21 then if j < 19 then 7055 else if j < 20 then 7775 else 7799 else if j < 22 then 7919 else if j < 23 then 8639 else 9359

/-- Its inverse, as a binary search on the sorted values.  Nothing is trusted
about either: `h71r_section` checks `Lget (idx s) = s` on every reachable `s`. -/
def h71ridx (s : ℕ) : ℕ := if s < 4743 then if s < 2310 then if s < 1560 then if s < 720 then 0 else if s < 1440 then 1 else 2 else if s < 1584 then 3 else if s < 2304 then 4 else 5 else if s < 3872 then if s < 3030 then 6 else if s < 3152 then 7 else 8 else if s < 3896 then 9 else if s < 4616 then 10 else 11 else if s < 7055 then if s < 6207 then if s < 5463 then 12 else if s < 5487 then 13 else 14 else if s < 6329 then 15 else if s < 7049 then 16 else 17 else if s < 7919 then if s < 7775 then 18 else if s < 7799 then 19 else 20 else if s < 8639 then 21 else if s < 9359 then 22 else 23

def h71rstep (w : List ℕ) : ℕ → ℕ → Option ℕ :=
  fun σ j => (gfamPred 7 (chansOfW h71rms w) (σ % 7) (σ / 7) (h71rLget j)).map h71ridx

/-- The reachability check at one index. -/
def h71rok (k : ℕ) : Bool :=
  decide (h71rLget (h71ridx (stateOfKW 7 h71rN 1 h71rms k)) = stateOfKW 7 h71rN 1 h71rms k)
    && decide (h71ridx (stateOfKW 7 h71rN 1 h71rms k) < 24)

/-- The per-run check: the quotients are constant across the run, and the run's
first index is reachable. -/
def h71rP (lo hi : ℕ) : Bool :=
  (coeffsOf 7 h71rms 1).all (fun b => decide ((b * lo) / h71rN = (b * (hi - 1)) / h71rN))
    && h71rok lo

/-- Two abutting covering sweeps concatenate.  Local to this module so that
adding it costs no rebuild of the rest of the chapter. -/
theorem h71r_runsCover_append {P : ℕ → ℕ → Bool} (rs2 : List ℕ) (e N : ℕ)
    (h2 : runsCover P e rs2 N = true) :
    ∀ (rs1 : List ℕ) (lo : ℕ), runsCover P lo rs1 e = true →
      runsCover P lo (rs1 ++ rs2) N = true := by
  intro rs1
  induction rs1 with
  | nil =>
    intro lo h1
    simp only [runsCover, decide_eq_true_eq] at h1
    subst h1
    simpa using h2
  | cons hi rest ih =>
    intro lo h1
    simp only [List.cons_append, runsCover, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, ih hi h1.2⟩

def h71rrunsC0 : List ℕ := [60, 120, 130, 156, 180, 195, 240, 260, 300, 312, 360, 390, 420, 468, 480, 520, 540, 585, 600, 624, 650, 660, 720, 780]

/-- The run endpoints: 24 runs tile `[0, 780)`, in 1 chunks —
one `decide +kernel` per chunk keeps the peak memory of each kernel probe down
(the whole sweep in one probe is OOM-killed on a 19 GB box). -/
def h71rruns : List ℕ := h71rrunsC0

theorem h71r_runs_c0 : runsCover h71rP 0 h71rrunsC0 780 = true := by decide +kernel

theorem h71r_runs_ok : runsCover h71rP 0 h71rruns h71rN = true := by
  show runsCover h71rP 0 h71rrunsC0 h71rN = true
  exact h71r_runs_c0

/-- **Reachability**, by run compression: 24 kernel checks instead of 780. -/
theorem h71r_section (k : ℕ) (hk : k < h71rN) :
    h71rLget (h71ridx (stateOfKW 7 h71rN 1 h71rms k)) = stateOfKW 7 h71rN 1 h71rms k
      ∧ h71ridx (stateOfKW 7 h71rN 1 h71rms k) < 24 := by
  refine runsCover_spec (P := h71rP) (Q := fun k =>
    h71rLget (h71ridx (stateOfKW 7 h71rN 1 h71rms k)) = stateOfKW 7 h71rN 1 h71rms k
      ∧ h71ridx (stateOfKW 7 h71rN 1 h71rms k) < 24) ?_ h71rruns 0 h71rN h71r_runs_ok k (by omega) hk
  intro lo hi hP j hj1 hj2
  simp only [h71rP, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hP
  have hconst : stateOfKW 7 h71rN 1 h71rms j = stateOfKW 7 h71rN 1 h71rms lo := by
    refine stateOfKW_congr 7 h71rN 1 (by omega) h71rms j lo ?_
    intro b hb
    exact quot_const_of_run b h71rN lo hi j hj1 hj2 (hP.1 b hb)
  have h := hP.2
  simp only [h71rok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hconst]
  exact h


/-- Certificate for the word `[0]`: 14 live states of the 24. -/
def h71rw0live : ℕ → Bool := fun j => [2, 3, 5, 7, 9, 10, 11, 13, 15, 17, 19, 20, 22, 23].contains j

def h71rw0rho : ℕ → ℕ := fun j => (([(3, 1), (5, 2), (7, 3), (9, 1), (10, 2), (11, 4), (13, 1), (15, 5), (17, 2), (19, 1), (22, 4), (23, 6)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw0omega : ℕ → ℕ := fun j => (([(1, 1), (4, 1), (6, 2), (8, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw0forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(2, (1, 2)), (3, (1, 9)), (5, (1, 17)), (7, (2, 7)), (9, (2, 19)), (11, (3, 11)), (13, (4, 3)), (15, (4, 15)), (17, (5, 5)), (19, (5, 13)), (20, (5, 20)), (23, (6, 23))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h71rw0_cert : checkCertA (h71rstep [0]) 7 24
    h71rw0live h71rw0rho h71rw0omega h71rw0forced = true := by decide +kernel


/-- Certificate for the word `[1]`: 11 live states of the 24. -/
def h71rw1live : ℕ → Bool := fun j => [0, 7, 8, 11, 12, 15, 16, 18, 20, 22, 23].contains j

def h71rw1rho : ℕ → ℕ := fun j => (([(8, 1), (12, 1), (16, 4), (18, 2), (20, 3), (22, 2), (23, 5)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw1omega : ℕ → ℕ := fun j => (([(10, 1), (19, 2)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw1forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (7, (2, 7)), (8, (2, 8)), (11, (3, 11)), (12, (3, 12)), (15, (4, 15)), (16, (4, 16)), (23, (6, 23))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h71rw1_cert : checkCertA (h71rstep [1]) 7 24
    h71rw1live h71rw1rho h71rw1omega h71rw1forced = true := by decide +kernel


/-- Certificate for the word `[2]`: 11 live states of the 24. -/
def h71rw2live : ℕ → Bool := fun j => [0, 5, 6, 11, 12, 13, 14, 17, 18, 20, 23].contains j

def h71rw2rho : ℕ → ℕ := fun j => (([(0, 1), (12, 3), (13, 2), (14, 1), (20, 1), (23, 4)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw2omega : ℕ → ℕ := fun j => (([(15, 1), (22, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw2forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (5, (1, 17)), (6, (1, 18)), (11, (3, 11)), (12, (3, 12)), (17, (5, 5)), (18, (5, 6)), (23, (6, 23))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h71rw2_cert : checkCertA (h71rstep [2]) 7 24
    h71rw2live h71rw2rho h71rw2omega h71rw2forced = true := by decide +kernel


/-- Certificate for the word `[3]`: 14 live states of the 24. -/
def h71rw3live : ℕ → Bool := fun j => [0, 3, 4, 7, 8, 9, 10, 13, 14, 15, 16, 19, 20, 23].contains j

def h71rw3rho : ℕ → ℕ := fun j => (([(0, 2), (7, 1), (16, 1), (23, 2)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw3omega : ℕ → ℕ := fun j => (([] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw3forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (3, (1, 9)), (4, (1, 10)), (7, (2, 7)), (8, (2, 8)), (9, (2, 19)), (10, (2, 20)), (13, (4, 3)), (14, (4, 4)), (15, (4, 15)), (16, (4, 16)), (19, (5, 13)), (20, (5, 14)), (23, (6, 23))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h71rw3_cert : checkCertA (h71rstep [3]) 7 24
    h71rw3live h71rw3rho h71rw3omega h71rw3forced = true := by decide +kernel


/-- Certificate for the word `[4]`: 11 live states of the 24. -/
def h71rw4live : ℕ → Bool := fun j => [0, 3, 5, 6, 9, 10, 11, 12, 17, 18, 23].contains j

def h71rw4rho : ℕ → ℕ := fun j => (([(0, 4), (3, 1), (9, 1), (10, 2), (11, 3), (23, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw4omega : ℕ → ℕ := fun j => (([(1, 1), (8, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw4forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (5, (1, 17)), (6, (1, 18)), (11, (3, 11)), (12, (3, 12)), (17, (5, 5)), (18, (5, 6)), (23, (6, 23))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h71rw4_cert : checkCertA (h71rstep [4]) 7 24
    h71rw4live h71rw4rho h71rw4omega h71rw4forced = true := by decide +kernel


/-- Certificate for the word `[5]`: 11 live states of the 24. -/
def h71rw5live : ℕ → Bool := fun j => [0, 1, 3, 5, 7, 8, 11, 12, 15, 16, 23].contains j

def h71rw5rho : ℕ → ℕ := fun j => (([(0, 5), (1, 2), (3, 3), (5, 2), (7, 4), (11, 1), (15, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw5omega : ℕ → ℕ := fun j => (([(4, 2), (13, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw5forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (7, (2, 7)), (8, (2, 8)), (11, (3, 11)), (12, (3, 12)), (15, (4, 15)), (16, (4, 16)), (23, (6, 23))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h71rw5_cert : checkCertA (h71rstep [5]) 7 24
    h71rw5live h71rw5rho h71rw5omega h71rw5forced = true := by decide +kernel


/-- Certificate for the word `[6]`: 14 live states of the 24. -/
def h71rw6live : ℕ → Bool := fun j => [0, 1, 3, 4, 6, 8, 10, 12, 13, 14, 16, 18, 20, 21].contains j

def h71rw6rho : ℕ → ℕ := fun j => (([(0, 6), (1, 4), (4, 1), (6, 2), (8, 5), (10, 1), (12, 4), (13, 2), (14, 1), (16, 3), (18, 2), (20, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw6omega : ℕ → ℕ := fun j => (([(15, 1), (17, 2), (19, 1), (22, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h71rw6forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (3, (1, 3)), (4, (1, 10)), (6, (1, 18)), (8, (2, 8)), (10, (2, 20)), (12, (3, 12)), (14, (4, 4)), (16, (4, 16)), (18, (5, 6)), (20, (5, 14)), (21, (5, 21))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h71rw6_cert : checkCertA (h71rstep [6]) 7 24
    h71rw6live h71rw6rho h71rw6omega h71rw6forced = true := by decide +kernel


/-- The section hypothesis of `signed_engine_g_single_reduced`, from `h71r_section`. -/
theorem h71r_sec (X : ℝ) (w : List ℕ) (hw : w.length = 1) (m : ℕ) :
    h71rLget (h71ridx (gfamState 7 (chansOfW h71rms w) X 0 m))
        = gfamState 7 (chansOfW h71rms w) X 0 m
      ∧ h71ridx (gfamState 7 (chansOfW h71rms w) X 0 m) < 24 := by
  have hms : ∀ a ∈ h71rms, 1 ≤ a := by decide
  have hdvd : ∀ a ∈ h71rms, ∀ j, j ≤ 1 - 1 → a * 7 ^ j ∣ h71rN := by decide
  have ht1 : Int.fract (X * ((7 : ℕ) : ℝ) ^ m) < 1 := Int.fract_lt_one _
  rw [gfamState_window 7 (by norm_num) h71rms hms w 1 hw h71rN (by norm_num [h71rN]) hdvd X m]
  refine h71r_section _ ?_
  have hN0 : (0 : ℝ) < (h71rN : ℝ) := by norm_num [h71rN]
  have hfl : ⌊(h71rN : ℝ) * Int.fract (X * ((7 : ℕ) : ℝ) ^ m)⌋ < (h71rN : ℤ) := by
    apply Int.floor_lt.2
    push_cast
    calc (h71rN : ℝ) * Int.fract (X * ((7 : ℕ) : ℝ) ^ m) < (h71rN : ℝ) * 1 :=
          mul_lt_mul_of_pos_left ht1 hN0
      _ = (h71rN : ℝ) := by ring
  have hpos' : 0 < h71rN := by norm_num [h71rN]
  omega

/-- **`S(7,1) ≤ 7`.** -/
theorem hitting_7_1_seven_reduced : Literature.IsHittingSet 7 1 {1, 2, 3, 4, 5, 6, 13} := by
  intro α hα w hw hd
  have hpos : ∀ v : List ℕ, ∀ ch ∈ chansOfW h71rms v, 1 ≤ ch.posSum := by
    intro v ch hch
    simp only [chansOfW, h71rms, List.mem_map] at hch
    obtain ⟨a, ha, rfl⟩ := hch
    simp only [ZChannel.posSum]
    fin_cases ha <;> decide
  have hell : ∀ v : List ℕ, v.length = 1 → ∀ ch ∈ chansOfW h71rms v, 1 ≤ ch.ell := by
    intro v hv ch hch
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    simp [ZChannel.ell, hv]
  have hword : ∀ v : List ℕ, (∀ c ∈ v, c < 7) → ∀ ch ∈ chansOfW h71rms v, ∀ c ∈ ch.word, c < 7 := by
    intro v hv ch hch c hc
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    exact hv c hc
  obtain ⟨d0, rfl⟩ : ∃ d0, w = [d0] := by
    rcases w with _ | ⟨d0, _ | ⟨z, t⟩⟩ <;> simp at hw
    exact ⟨d0, rfl⟩
  have hltd0 : d0 < 7 := hd d0 (by simp)
  have key : ∃ ch ∈ chansOfW h71rms [d0],
      ∀ N, ∃ n, N ≤ n ∧ OccursAt 7 (ch.a * α) ch.word n := by
    interval_cases d0
    · exact signed_engine_g_single_reduced 7 (by norm_num) (chansOfW h71rms [0])
        h71rLget h71ridx h71rw0_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h71r_sec α [0] rfl m).2)
        (fun m => (h71r_sec α [0] rfl m).1)
    · exact signed_engine_g_single_reduced 7 (by norm_num) (chansOfW h71rms [1])
        h71rLget h71ridx h71rw1_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h71r_sec α [1] rfl m).2)
        (fun m => (h71r_sec α [1] rfl m).1)
    · exact signed_engine_g_single_reduced 7 (by norm_num) (chansOfW h71rms [2])
        h71rLget h71ridx h71rw2_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h71r_sec α [2] rfl m).2)
        (fun m => (h71r_sec α [2] rfl m).1)
    · exact signed_engine_g_single_reduced 7 (by norm_num) (chansOfW h71rms [3])
        h71rLget h71ridx h71rw3_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h71r_sec α [3] rfl m).2)
        (fun m => (h71r_sec α [3] rfl m).1)
    · exact signed_engine_g_single_reduced 7 (by norm_num) (chansOfW h71rms [4])
        h71rLget h71ridx h71rw4_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h71r_sec α [4] rfl m).2)
        (fun m => (h71r_sec α [4] rfl m).1)
    · exact signed_engine_g_single_reduced 7 (by norm_num) (chansOfW h71rms [5])
        h71rLget h71ridx h71rw5_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h71r_sec α [5] rfl m).2)
        (fun m => (h71r_sec α [5] rfl m).1)
    · exact signed_engine_g_single_reduced 7 (by norm_num) (chansOfW h71rms [6])
        h71rLget h71ridx h71rw6_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h71r_sec α [6] rfl m).2)
        (fun m => (h71r_sec α [6] rfl m).1)
  obtain ⟨ch, hch, hio⟩ := key
  simp only [chansOfW, h71rms, List.map_cons, List.map_nil] at hch
  fin_cases hch
  · exact ⟨1, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨2, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨3, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨4, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨5, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨6, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨13, by simp, by norm_num, by simpa using hio⟩

end NormalNumbers.Adder
