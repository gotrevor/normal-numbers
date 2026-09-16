/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetReduced
import NormalNumbers.Literature

/-!
# `S(6,1) ≤ 7`: seven multipliers hit every base-6 digit 🧵

The hitting-set search (`experiments/hitting_set_search.py`,
`docs/hitting-set-invariant-2026-09-13.md` row `(6,1)`) found the seven
multipliers `{1, 8, 11, 14, 16, 20, 23}`.  Their product — the ambient state
space of the `gfamPred` family — is `9067520`, so neither a chunked kernel
`decide` nor a `native_decide` over `[0, S)` is practical.

**The carry-consistency reduction** (`HittingSetReduced.lean`) removes the
product entirely.  All seven channels read the same `X`, so the joint carry
vector at step `m` is `(⌊mᵢ · t⌋)ᵢ` for the single tail parameter
`t = fract(X·6ᵐ)`, and with `N = lcm(mᵢ) = 141680` it is `stateOfK ms N ⌊N·t⌋`.  The
image has just **`76` states** (`experiments/adder_reduced_emit.py`), and the
six certificates — one per base-6 digit — are checked on that relabelled space by
`signed_engine_g_single_reduced`.  The reachability fact `h61_section` (every
`k < 141680` lands in the state list) is the only ambient-sized check left, and it
is fourteen kernel `decide +kernel` chunks of `10120` indices rather than
`9067520 · 6` edges — so this file has NO `native_decide` at all.

* `hitting_6_1_seven` : `S(6,1) ≤ 7`, hitting set `{1, 8, 11, 14, 16, 20, 23}`.

Nothing here claims the lower bound `S(6,1) ≥ 7`.
-/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

/-- The seven multipliers of the `(6,1)` hitting set. -/
def h61ms : List ℕ := [1, 8, 11, 14, 16, 20, 23]

/-- `lcm` of the multipliers: the index range of the reachable curve. -/
def h61N : ℕ := 141680

/-- The `76` reachable joint states, sorted (`adder_reduced_emit.py`). -/
def h61L : Array ℕ := #[0, 394240, 413952, 415184, 415272, 809512, 809520, 829232, 830465, 1224705, 1224793, 1244505, 1638745, 1638753, 1639985, 1659697, 1659785, 2054025, 2074970, 2469210, 2469218, 2469306, 2489018, 2883258, 2884490, 3278730, 3298442, 3298530, 3298538, 3299771, 3694011, 3713723, 3713811, 4108051, 4109283, 4128995, 4129003, 4523243, 4544276, 4938516, 4938524, 4958236, 4959468, 5353708, 5353796, 5373508, 5767748, 5768981, 5768989, 5769077, 5788789, 6183029, 6184261, 6578501, 6598213, 6598301, 6598309, 6992549, 7013494, 7407734, 7407822, 7427534, 7428766, 7428774, 7823014, 7842726, 7842814, 8237054, 8238287, 8257999, 8258007, 8652247, 8652335, 8653567, 8673279, 9067519]

/-- The `j`-th reachable state. -/
def h61Lget (j : ℕ) : ℕ := h61L.getD j 0

/-- Inverse of `h61Lget` on the reachable states. -/
def h61idx (s : ℕ) : ℕ := (bfind h61L s).getD 0

/-- The reduced step relation: `gfamPred` read through the relabelling. -/
def h61step (d : ℕ) : ℕ → ℕ → Option ℕ :=
  fun σ j => (gfamPred 6 (chansOf h61ms d) (σ % 6) (σ / 6) (h61Lget j)).map h61idx

/-- The reachability predicate at one index. -/
def h61ok (k : ℕ) : Bool :=
  decide (h61Lget (h61idx (stateOfK h61ms h61N k)) = stateOfK h61ms h61N k)
    && decide (h61idx (stateOfK h61ms h61N k) < 76)

theorem h61_c0 : allOn 0 10120 h61ok = true := by decide +kernel

theorem h61_c1 : allOn 10120 10120 h61ok = true := by decide +kernel

theorem h61_c2 : allOn 20240 10120 h61ok = true := by decide +kernel

theorem h61_c3 : allOn 30360 10120 h61ok = true := by decide +kernel

theorem h61_c4 : allOn 40480 10120 h61ok = true := by decide +kernel

theorem h61_c5 : allOn 50600 10120 h61ok = true := by decide +kernel

theorem h61_c6 : allOn 60720 10120 h61ok = true := by decide +kernel

theorem h61_c7 : allOn 70840 10120 h61ok = true := by decide +kernel

theorem h61_c8 : allOn 80960 10120 h61ok = true := by decide +kernel

theorem h61_c9 : allOn 91080 10120 h61ok = true := by decide +kernel

theorem h61_c10 : allOn 101200 10120 h61ok = true := by decide +kernel

theorem h61_c11 : allOn 111320 10120 h61ok = true := by decide +kernel

theorem h61_c12 : allOn 121440 10120 h61ok = true := by decide +kernel

theorem h61_c13 : allOn 131560 10120 h61ok = true := by decide +kernel

theorem h61_all : allOn 0 h61N h61ok = true := by
  have h := allOn_of_chunks (c := 10120) 14 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h61_c0, h61_c1, h61_c2, h61_c3, h61_c4, h61_c5, h61_c6, h61_c7,
      h61_c8, h61_c9, h61_c10, h61_c11, h61_c12, h61_c13])
  exact h

/-- **Reachability**: every index `k < 141680` gives a state in the list `h61L`,
at a position below `76`.  With `gfamState_ell1` and `stateOfT_eq_stateOfK` this
is exactly the section hypothesis of `signed_engine_g_single_reduced`.  Kernel
`decide +kernel` in fourteen chunks of `10120`: the whole sweep in one probe was
killed at `15` GB. -/
theorem h61_section : ∀ k : ℕ, k < h61N →
    h61Lget (h61idx (stateOfK h61ms h61N k)) = stateOfK h61ms h61N k
      ∧ h61idx (stateOfK h61ms h61N k) < 76 := by
  intro k hk
  have h := allOn_zero_spec h61_all k hk
  simp only [h61ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- Certificate `h61r_d0` (`experiments/certs/adder_cert_h61r_d0.json`): digit `0`,
`16` live states of the `76` reachable. -/
def h61d0live : ℕ → Bool := fun j => [14, 17, 21, 24, 30, 31, 37, 39, 44, 46, 51, 57, 58, 60, 68, 75].contains j

def h61d0rho : ℕ → ℕ := fun j => (([(17, 4), (21, 1), (24, 3), (31, 4), (37, 3), (39, 4), (44, 5), (46, 5), (51, 3), (57, 4), (58, 4), (68, 1), (75, 2)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d0omega : ℕ → ℕ := fun j => (([(11, 1), (12, 1), (15, 2), (19, 1), (23, 1), (34, 1), (36, 2), (38, 1), (41, 1), (45, 1), (54, 2), (55, 1), (61, 2), (64, 1), (66, 1), (69, 1), (71, 2), (73, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d0forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(14, (1, 14)), (17, (1, 31)), (30, (2, 30)), (31, (2, 39)), (39, (3, 17)), (44, (3, 44)), (60, (4, 60)), (75, (5, 75))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h61d0_cert : checkCertA (h61step 0) 6 76
    h61d0live h61d0rho h61d0omega h61d0forced = true := by decide +kernel

/-- Certificate `h61r_d1` (`experiments/certs/adder_cert_h61r_d1.json`): digit `1`,
`23` live states of the `76` reachable. -/
def h61d1live : ℕ → Bool := fun j => [0, 3, 4, 7, 24, 26, 31, 32, 33, 37, 38, 41, 44, 45, 46, 51, 55, 56, 57, 63, 65, 71, 75].contains j

def h61d1rho : ℕ → ℕ := fun j => (([(3, 4), (4, 3), (7, 4), (24, 4), (26, 5), (31, 4), (32, 2), (37, 7), (38, 1), (41, 4), (45, 1), (51, 5), (55, 6), (56, 3), (63, 3), (65, 5), (71, 2), (75, 6)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d1omega : ℕ → ℕ := fun j => (([(1, 1), (2, 2), (8, 3), (9, 2), (25, 1), (28, 1), (34, 4), (36, 2), (39, 1), (40, 1), (47, 3), (52, 4), (53, 1), (58, 2), (60, 1), (62, 1), (64, 1), (66, 1), (68, 1), (73, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d1forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (3, (0, 31)), (24, (2, 3)), (31, (2, 41)), (33, (2, 46)), (41, (3, 24)), (44, (3, 44)), (45, (3, 45)), (46, (3, 57)), (57, (4, 33)), (75, (5, 75))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h61d1_cert : checkCertA (h61step 1) 6 76
    h61d1live h61d1rho h61d1omega h61d1forced = true := by decide +kernel

/-- Certificate `h61r_d2` (`experiments/certs/adder_cert_h61r_d2.json`): digit `2`,
`27` live states of the `76` reachable. -/
def h61d2live : ℕ → Bool := fun j => [0, 7, 9, 10, 11, 14, 15, 18, 20, 24, 38, 45, 46, 47, 48, 49, 51, 52, 53, 54, 58, 59, 64, 66, 68, 73, 75].contains j

def h61d2rho : ℕ → ℕ := fun j => (([(7, 9), (9, 7), (10, 2), (11, 6), (18, 2), (20, 2), (24, 6), (38, 1), (45, 3), (46, 9), (47, 3), (48, 7), (49, 2), (51, 6), (52, 8), (53, 1), (54, 1), (58, 9), (59, 2), (64, 6), (66, 1), (68, 3), (73, 4), (75, 5)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d2omega : ℕ → ℕ := fun j => (([(3, 1), (4, 1), (6, 2), (17, 1), (19, 3), (21, 2), (39, 1), (42, 1), (43, 1), (44, 2), (55, 1), (56, 1), (60, 2), (63, 1), (69, 1), (70, 1), (71, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d2forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (14, (1, 14)), (15, (1, 15)), (75, (5, 75))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h61d2_cert : checkCertA (h61step 2) 6 76
    h61d2live h61d2rho h61d2omega h61d2forced = true := by decide +kernel

/-- Certificate `h61r_d3` (`experiments/certs/adder_cert_h61r_d3.json`): digit `3`,
`27` live states of the `76` reachable. -/
def h61d3live : ℕ → Bool := fun j => [0, 2, 7, 9, 11, 16, 17, 21, 22, 23, 24, 26, 27, 28, 29, 30, 37, 51, 55, 57, 60, 61, 64, 65, 66, 68, 75].contains j

def h61d3rho : ℕ → ℕ := fun j => (([(0, 5), (2, 4), (7, 3), (9, 1), (11, 6), (16, 2), (17, 9), (21, 1), (22, 1), (23, 8), (24, 6), (26, 2), (27, 7), (28, 3), (29, 9), (30, 3), (37, 1), (51, 6), (55, 2), (57, 2), (64, 6), (65, 2), (66, 7), (68, 9)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d3omega : ℕ → ℕ := fun j => (([(4, 1), (5, 1), (6, 1), (12, 1), (15, 2), (19, 1), (20, 1), (31, 2), (32, 1), (33, 1), (36, 1), (54, 2), (56, 3), (58, 1), (69, 2), (71, 1), (72, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d3forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (60, (4, 60)), (61, (4, 61)), (75, (5, 75))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h61d3_cert : checkCertA (h61step 3) 6 76
    h61d3live h61d3rho h61d3omega h61d3forced = true := by decide +kernel

/-- Certificate `h61r_d4` (`experiments/certs/adder_cert_h61r_d4.json`): digit `4`,
`23` live states of the `76` reachable. -/
def h61d4live : ℕ → Bool := fun j => [0, 4, 10, 12, 18, 19, 20, 24, 29, 30, 31, 34, 37, 38, 42, 43, 44, 49, 51, 68, 71, 72, 75].contains j

def h61d4rho : ℕ → ℕ := fun j => (([(0, 6), (4, 2), (10, 5), (12, 3), (19, 3), (20, 6), (24, 5), (30, 1), (34, 4), (37, 1), (38, 7), (43, 2), (44, 4), (49, 5), (51, 4), (68, 4), (71, 3), (72, 4)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d4omega : ℕ → ℕ := fun j => (([(2, 1), (7, 1), (9, 1), (11, 1), (13, 1), (15, 1), (17, 2), (22, 1), (23, 4), (28, 3), (35, 1), (36, 1), (39, 2), (41, 4), (47, 1), (50, 1), (66, 2), (67, 3), (73, 2), (74, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d4forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (18, (1, 42)), (29, (2, 18)), (30, (2, 30)), (31, (2, 31)), (34, (2, 51)), (42, (3, 29)), (44, (3, 34)), (51, (3, 72)), (72, (5, 44)), (75, (5, 75))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h61d4_cert : checkCertA (h61step 4) 6 76
    h61d4live h61d4rho h61d4omega h61d4forced = true := by decide +kernel

/-- Certificate `h61r_d5` (`experiments/certs/adder_cert_h61r_d5.json`): digit `5`,
`16` live states of the `76` reachable. -/
def h61d5live : ℕ → Bool := fun j => [0, 7, 15, 17, 18, 24, 29, 31, 36, 38, 44, 45, 51, 54, 58, 61].contains j

def h61d5rho : ℕ → ℕ := fun j => (([(0, 2), (7, 1), (17, 4), (18, 4), (24, 3), (29, 5), (31, 5), (36, 4), (38, 3), (44, 4), (51, 3), (54, 1), (58, 4)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d5omega : ℕ → ℕ := fun j => (([(2, 1), (4, 2), (6, 1), (9, 1), (11, 1), (14, 2), (20, 1), (21, 2), (30, 1), (34, 1), (37, 1), (39, 2), (41, 1), (52, 1), (56, 1), (60, 2), (63, 1), (64, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h61d5forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (15, (1, 15)), (31, (2, 31)), (36, (2, 58)), (44, (3, 36)), (45, (3, 45)), (58, (4, 44)), (61, (4, 61))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h61d5_cert : checkCertA (h61step 5) 6 76
    h61d5live h61d5rho h61d5omega h61d5forced = true := by decide +kernel

/-! ## The engine at the reduced state space -/

/-- The section hypothesis of `signed_engine_g_single_reduced`, discharged from
`h61_section` by the carry-consistency identities `gfamState_ell1` and
`stateOfT_eq_stateOfK`. -/
theorem h61_sec (X : ℝ) (d : ℕ) (m : ℕ) :
    h61Lget (h61idx (gfamState 6 (chansOf h61ms d) X 0 m))
        = gfamState 6 (chansOf h61ms d) X 0 m
      ∧ h61idx (gfamState 6 (chansOf h61ms d) X 0 m) < 76 := by
  have hms : ∀ a ∈ h61ms, 1 ≤ a := by decide
  have hdvd : ∀ a ∈ h61ms, a ∣ h61N := by decide
  have ht : 0 ≤ Int.fract (X * ((6 : ℕ) : ℝ) ^ m) := Int.fract_nonneg _
  have ht1 : Int.fract (X * ((6 : ℕ) : ℝ) ^ m) < 1 := Int.fract_lt_one _
  rw [gfamState_ell1 6 d h61ms hms X m,
    stateOfT_eq_stateOfK h61ms h61N (by norm_num [h61N]) hdvd _ ht]
  refine h61_section _ ?_
  have hN0 : (0 : ℝ) < (h61N : ℝ) := by norm_num [h61N]
  have hfl : ⌊(h61N : ℝ) * Int.fract (X * ((6 : ℕ) : ℝ) ^ m)⌋ < (h61N : ℤ) := by
    apply Int.floor_lt.2
    push_cast
    calc (h61N : ℝ) * Int.fract (X * ((6 : ℕ) : ℝ) ^ m) < (h61N : ℝ) * 1 :=
          mul_lt_mul_of_pos_left ht1 hN0
      _ = (h61N : ℝ) := by ring
  have hpos' : 0 < h61N := by norm_num [h61N]
  omega

/-- **`S(6,1) ≤ 7`.**  The seven multipliers `{1, 8, 11, 14, 16, 20, 23}` hit
every base-6 digit: for every irrational `α` and every digit `d < 6`, some
`m` in the set has `d` occurring infinitely often in the base-6 expansion of
`m·α`.  Proved on the `76`-state carry-consistency reduction of the `9067520`
ambient states. -/
theorem hitting_6_1_seven : Literature.IsHittingSet 6 1 {1, 8, 11, 14, 16, 20, 23} := by
  intro α hα w hw hd
  obtain ⟨d, rfl⟩ : ∃ d, w = [d] := by
    rcases w with _ | ⟨d, _ | ⟨e, t⟩⟩ <;> simp at hw
    exact ⟨d, rfl⟩
  have hd6 : d < 6 := hd d (by simp)
  have hpos : ∀ ch ∈ chansOf h61ms d, 1 ≤ ch.posSum := by
    intro ch hch
    simp only [chansOf, h61ms, List.mem_map] at hch
    obtain ⟨a, ha, rfl⟩ := hch
    simp only [ZChannel.posSum]
    fin_cases ha <;> decide
  have hell : ∀ ch ∈ chansOf h61ms d, 1 ≤ ch.ell := by
    intro ch hch
    simp only [chansOf, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    simp [ZChannel.ell]
  have hword : ∀ e : ℕ, e < 6 → ∀ ch ∈ chansOf h61ms e, ∀ c ∈ ch.word, c < 6 := by
    intro e he ch hch c hc
    simp only [chansOf, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    simp at hc
    omega
  have key : ∃ ch ∈ chansOf h61ms d, ∀ N, ∃ n, N ≤ n ∧ OccursAt 6 (ch.a * α) ch.word n := by
    interval_cases d
    · exact signed_engine_g_single_reduced 6 (by norm_num) (chansOf h61ms 0)
        h61Lget h61idx h61d0_cert α hα hpos hell (hword 0 hd6) (fun m => (h61_sec α 0 m).2)
        (fun m => (h61_sec α 0 m).1)
    · exact signed_engine_g_single_reduced 6 (by norm_num) (chansOf h61ms 1)
        h61Lget h61idx h61d1_cert α hα hpos hell (hword 1 hd6) (fun m => (h61_sec α 1 m).2)
        (fun m => (h61_sec α 1 m).1)
    · exact signed_engine_g_single_reduced 6 (by norm_num) (chansOf h61ms 2)
        h61Lget h61idx h61d2_cert α hα hpos hell (hword 2 hd6) (fun m => (h61_sec α 2 m).2)
        (fun m => (h61_sec α 2 m).1)
    · exact signed_engine_g_single_reduced 6 (by norm_num) (chansOf h61ms 3)
        h61Lget h61idx h61d3_cert α hα hpos hell (hword 3 hd6) (fun m => (h61_sec α 3 m).2)
        (fun m => (h61_sec α 3 m).1)
    · exact signed_engine_g_single_reduced 6 (by norm_num) (chansOf h61ms 4)
        h61Lget h61idx h61d4_cert α hα hpos hell (hword 4 hd6) (fun m => (h61_sec α 4 m).2)
        (fun m => (h61_sec α 4 m).1)
    · exact signed_engine_g_single_reduced 6 (by norm_num) (chansOf h61ms 5)
        h61Lget h61idx h61d5_cert α hα hpos hell (hword 5 hd6) (fun m => (h61_sec α 5 m).2)
        (fun m => (h61_sec α 5 m).1)
  obtain ⟨ch, hch, hio⟩ := key
  simp only [chansOf, h61ms, List.map_cons, List.map_nil] at hch
  fin_cases hch
  · exact ⟨1, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨8, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨11, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨14, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨16, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨20, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨23, by simp, by norm_num, by simpa using hio⟩

end NormalNumbers.Adder
