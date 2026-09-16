/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetReduced
import NormalNumbers.Literature

/-!
# `S(3,2) ≤ 6`: six multipliers hit every base-3 pair 🧵

`docs/hitting-set-invariant-2026-09-13.md` row `(3,2)`: the search found the six
multipliers `{1, 2, 4, 5, 7, 8}`.  The ambient state space of the family is
`∏ᵢ mᵢ · 3 = 1632960`; the carry-consistency reduction (`HittingSetReduced.lean`)
cuts it to `54` states.  All six channels read the same `X`, so with
`t = fract(X·3ᵐ)` the carry of channel `a` is `⌊a·t⌋` and its single window digit
is `⌊3a·t⌋ − 3⌊a·t⌋` (`gdigit_window`: the `⌊X·3ᵐ⌋` terms cancel).  With
`N = lcm {a, 3a} = 840` the state is `stateOfKW 3 N 2 ms ⌊N·t⌋`
(`gfamState_window`), and the image over `k < N` is the `54`-element list `h32L`,
closed under `gfamPred`.

* `hitting_3_2_six` : `S(3,2) ≤ 6`, hitting set `{1, 2, 4, 5, 7, 8}`.

Every check here is a kernel `decide +kernel` — the nine per-word certificates on
`54` states, and the reachability sweep `h32_all` over `k < 840`.  (The first
version of this file, 2026-09-16, swept the full `1632960` ambient per word with
`native_decide` and sorted-array tables, at ~90 s a word; the reduction makes it
free and axiom-clean.)

Nothing here claims the lower bound `S(3,2) ≥ 6`.
-/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

/-- The six multipliers of the `(3,2)` hitting set. -/
def h32ms : List ℕ := [1, 2, 4, 5, 7, 8]

/-- `lcm {a·3^j : a ∈ ms, j ≤ 1}`. -/
def h32N : ℕ := 840

/-- The `54` reachable joint states, sorted (`adder_reduced_emit_ell.py`). -/
def h32L : Array ℕ := #[0, 68040, 71280, 71496, 139554, 142794, 210834, 211050, 214290, 282351, 285591, 285807, 353847, 357087, 425145, 425361, 428601, 496641, 568159, 636199, 639439, 639655, 707713, 710953, 778993, 779209, 782449, 850510, 853750, 853966, 922006, 925246, 993304, 993520, 996760, 1064800, 1136318, 1204358, 1207598, 1207814, 1275872, 1279112, 1347152, 1347368, 1350608, 1418669, 1421909, 1422125, 1490165, 1493405, 1561463, 1561679, 1564919, 1632959]

def h32Lget (j : ℕ) : ℕ := h32L.getD j 0

def h32idx (s : ℕ) : ℕ := (bfind h32L s).getD 0

def h32step (w : List ℕ) : ℕ → ℕ → Option ℕ :=
  fun σ j => (gfamPred 3 (chansOfW h32ms w) (σ % 3) (σ / 3) (h32Lget j)).map h32idx

def h32ok (k : ℕ) : Bool :=
  decide (h32Lget (h32idx (stateOfKW 3 h32N 2 h32ms k)) = stateOfKW 3 h32N 2 h32ms k)
    && decide (h32idx (stateOfKW 3 h32N 2 h32ms k) < 54)

theorem h32_all : (List.range h32N).all h32ok = true := by decide +kernel

/-- **Reachability**: every index `k < 840` lands in `h32L`, below `54`. -/
theorem h32_section (k : ℕ) (hk : k < h32N) :
    h32Lget (h32idx (stateOfKW 3 h32N 2 h32ms k)) = stateOfKW 3 h32N 2 h32ms k
      ∧ h32idx (stateOfKW 3 h32N 2 h32ms k) < 54 := by
  have h := List.all_eq_true.1 h32_all k (List.mem_range.2 hk)
  simp only [h32ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- Certificate `h32r_w00` (`experiments/certs/adder_cert_h32r_w00.json`):
word `[0, 0]`, `35` live states of the `54` reachable. -/
def h32w00live : ℕ → Bool := fun j => [5, 7, 8, 9, 10, 12, 13, 15, 17, 18, 20, 22, 23, 24, 25, 26, 30, 32, 34, 35, 36, 37, 38, 39, 41, 42, 44, 45, 47, 48, 49, 50, 51, 52, 53].contains j

def h32w00rho : ℕ → ℕ := fun j => (([(7, 2), (8, 7), (9, 3), (10, 4), (12, 3), (13, 6), (15, 2), (17, 10), (20, 4), (22, 2), (23, 1), (24, 5), (25, 3), (26, 6), (30, 2), (32, 4), (35, 10), (36, 1), (37, 2), (38, 5), (39, 6), (41, 1), (42, 4), (44, 7), (45, 2), (48, 3), (49, 7), (50, 5), (51, 8), (52, 1), (53, 9)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w00omega : ℕ → ℕ := fun j => (([] : List (ℕ × ℕ)).lookup j).getD 0

def h32w00forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(5, (0, 18)), (7, (0, 22)), (10, (0, 32)), (13, (0, 39)), (15, (0, 45)), (18, (1, 5)), (20, (1, 10)), (22, (1, 15)), (26, (1, 26)), (30, (1, 37)), (32, (1, 42)), (34, (1, 47)), (37, (2, 7)), (39, (2, 13)), (42, (2, 20)), (45, (2, 30)), (47, (2, 34)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w00_cert : checkCertA (h32step [0, 0]) 3 54
    h32w00live h32w00rho h32w00omega h32w00forced = true := by decide +kernel

/-- Certificate `h32r_w01` (`experiments/certs/adder_cert_h32r_w01.json`):
word `[0, 1]`, `19` live states of the `54` reachable. -/
def h32w01live : ℕ → Bool := fun j => [0, 13, 14, 17, 18, 21, 22, 25, 26, 27, 35, 36, 39, 40, 43, 49, 50, 51, 53].contains j

def h32w01rho : ℕ → ℕ := fun j => (([(17, 5), (18, 1), (21, 1), (22, 1), (25, 2), (26, 3), (35, 5), (36, 1), (43, 2), (49, 1), (50, 1), (51, 3), (53, 4)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w01omega : ℕ → ℕ := fun j => (([(19, 1), (20, 1), (24, 2), (33, 2), (34, 2), (37, 1), (38, 1), (41, 1), (44, 3), (45, 1), (46, 1), (47, 3), (48, 2), (52, 4)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w01forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (13, (0, 39)), (14, (0, 40)), (26, (1, 26)), (27, (1, 27)), (39, (2, 13)), (40, (2, 14)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w01_cert : checkCertA (h32step [0, 1]) 3 54
    h32w01live h32w01rho h32w01omega h32w01forced = true := by decide +kernel

/-- Certificate `h32r_w02` (`experiments/certs/adder_cert_h32r_w02.json`):
word `[0, 2]`, `22` live states of the `54` reachable. -/
def h32w02live : ℕ → Bool := fun j => [0, 9, 10, 11, 18, 20, 21, 26, 27, 32, 33, 36, 38, 39, 42, 43, 45, 47, 50, 51, 52, 53].contains j

def h32w02rho : ℕ → ℕ := fun j => (([(9, 1), (10, 2), (18, 1), (20, 2), (32, 2), (36, 1), (38, 3), (39, 1), (42, 2), (45, 1), (47, 1), (50, 3), (51, 2), (52, 2), (53, 4)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w02omega : ℕ → ℕ := fun j => (([(4, 1), (5, 1), (12, 1), (19, 1), (22, 1), (23, 1), (28, 1), (30, 1), (37, 1), (41, 1), (48, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w02forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (10, (0, 32)), (11, (0, 33)), (20, (1, 10)), (21, (1, 11)), (26, (1, 26)), (27, (1, 27)), (32, (1, 42)), (33, (1, 43)), (42, (2, 20)), (43, (2, 21)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w02_cert : checkCertA (h32step [0, 2]) 3 54
    h32w02live h32w02rho h32w02omega h32w02forced = true := by decide +kernel

/-- Certificate `h32r_w10` (`experiments/certs/adder_cert_h32r_w10.json`):
word `[1, 0]`, `15` live states of the `54` reachable. -/
def h32w10live : ℕ → Bool := fun j => [0, 8, 13, 14, 17, 26, 27, 28, 31, 35, 39, 40, 44, 51, 53].contains j

def h32w10rho : ℕ → ℕ := fun j => (([(8, 1), (17, 4), (27, 3), (28, 2), (31, 1), (35, 4), (44, 1), (51, 2), (53, 3)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w10omega : ℕ → ℕ := fun j => (([(2, 1), (5, 1), (6, 1), (7, 1), (12, 1), (16, 1), (23, 1), (24, 1), (29, 2), (30, 1), (33, 1), (38, 1), (41, 1), (43, 1), (46, 1), (48, 1), (50, 1), (52, 2)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w10forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (13, (0, 39)), (14, (0, 40)), (26, (1, 26)), (27, (1, 27)), (39, (2, 13)), (40, (2, 14)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w10_cert : checkCertA (h32step [1, 0]) 3 54
    h32w10live h32w10rho h32w10omega h32w10forced = true := by decide +kernel

/-- Certificate `h32r_w11` (`experiments/certs/adder_cert_h32r_w11.json`):
word `[1, 1]`, `30` live states of the `54` reachable. -/
def h32w11live : ℕ → Bool := fun j => [0, 1, 2, 7, 8, 10, 11, 15, 16, 17, 18, 20, 21, 22, 23, 30, 31, 32, 33, 35, 36, 37, 38, 42, 43, 45, 46, 51, 52, 53].contains j

def h32w11rho : ℕ → ℕ := fun j => (([(0, 2), (1, 1), (2, 1), (17, 3), (18, 3), (35, 3), (36, 3), (51, 1), (52, 1), (53, 2)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w11omega : ℕ → ℕ := fun j => (([(3, 1), (4, 1), (9, 1), (44, 1), (49, 1), (50, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w11forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (7, (0, 22)), (8, (0, 23)), (10, (0, 32)), (11, (0, 33)), (15, (0, 45)), (16, (0, 46)), (20, (1, 10)), (21, (1, 11)), (22, (1, 15)), (23, (1, 16)), (30, (1, 37)), (31, (1, 38)), (32, (1, 42)), (33, (1, 43)), (37, (2, 7)), (38, (2, 8)), (42, (2, 20)), (43, (2, 21)), (45, (2, 30)), (46, (2, 31)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w11_cert : checkCertA (h32step [1, 1]) 3 54
    h32w11live h32w11rho h32w11omega h32w11forced = true := by decide +kernel

/-- Certificate `h32r_w12` (`experiments/certs/adder_cert_h32r_w12.json`):
word `[1, 2]`, `15` live states of the `54` reachable. -/
def h32w12live : ℕ → Bool := fun j => [0, 2, 9, 13, 14, 18, 22, 25, 26, 27, 36, 39, 40, 45, 53].contains j

def h32w12rho : ℕ → ℕ := fun j => (([(0, 3), (2, 2), (9, 1), (18, 4), (22, 1), (25, 2), (26, 3), (36, 4), (45, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w12omega : ℕ → ℕ := fun j => (([(1, 2), (3, 1), (5, 1), (7, 1), (10, 1), (12, 1), (15, 1), (20, 1), (23, 1), (24, 2), (29, 1), (30, 1), (37, 1), (41, 1), (46, 1), (47, 1), (48, 1), (51, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w12forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (13, (0, 39)), (14, (0, 40)), (26, (1, 26)), (27, (1, 27)), (39, (2, 13)), (40, (2, 14)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w12_cert : checkCertA (h32step [1, 2]) 3 54
    h32w12live h32w12rho h32w12omega h32w12forced = true := by decide +kernel

/-- Certificate `h32r_w20` (`experiments/certs/adder_cert_h32r_w20.json`):
word `[2, 0]`, `22` live states of the `54` reachable. -/
def h32w20live : ℕ → Bool := fun j => [0, 1, 2, 3, 6, 8, 10, 11, 14, 15, 17, 20, 21, 26, 27, 32, 33, 35, 42, 43, 44, 53].contains j

def h32w20rho : ℕ → ℕ := fun j => (([(0, 4), (1, 2), (2, 2), (3, 3), (6, 1), (8, 1), (11, 2), (14, 1), (15, 3), (17, 1), (21, 2), (33, 2), (35, 1), (43, 2), (44, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w20omega : ℕ → ℕ := fun j => (([(5, 1), (12, 1), (16, 1), (23, 1), (25, 1), (30, 1), (31, 1), (34, 1), (41, 1), (48, 1), (49, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w20forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (10, (0, 32)), (11, (0, 33)), (20, (1, 10)), (21, (1, 11)), (26, (1, 26)), (27, (1, 27)), (32, (1, 42)), (33, (1, 43)), (42, (2, 20)), (43, (2, 21)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w20_cert : checkCertA (h32step [2, 0]) 3 54
    h32w20live h32w20rho h32w20omega h32w20forced = true := by decide +kernel

/-- Certificate `h32r_w21` (`experiments/certs/adder_cert_h32r_w21.json`):
word `[2, 1]`, `19` live states of the `54` reachable. -/
def h32w21live : ℕ → Bool := fun j => [0, 2, 3, 4, 10, 13, 14, 17, 18, 26, 27, 28, 31, 32, 35, 36, 39, 40, 53].contains j

def h32w21rho : ℕ → ℕ := fun j => (([(0, 4), (2, 3), (3, 1), (4, 1), (10, 2), (17, 1), (18, 5), (27, 3), (28, 2), (31, 1), (32, 1), (35, 1), (36, 5)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w21omega : ℕ → ℕ := fun j => (([(1, 4), (5, 2), (6, 3), (7, 1), (8, 1), (9, 3), (12, 1), (15, 1), (16, 1), (19, 2), (20, 2), (29, 2), (33, 1), (34, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w21forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (13, (0, 39)), (14, (0, 40)), (26, (1, 26)), (27, (1, 27)), (39, (2, 13)), (40, (2, 14)), (53, (2, 53))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w21_cert : checkCertA (h32step [2, 1]) 3 54
    h32w21live h32w21rho h32w21omega h32w21forced = true := by decide +kernel

/-- Certificate `h32r_w22` (`experiments/certs/adder_cert_h32r_w22.json`):
word `[2, 2]`, `35` live states of the `54` reachable. -/
def h32w22live : ℕ → Bool := fun j => [0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 14, 15, 16, 17, 18, 19, 21, 23, 27, 28, 29, 30, 31, 33, 35, 36, 38, 40, 41, 43, 44, 45, 46, 48].contains j

def h32w22rho : ℕ → ℕ := fun j => (([(0, 9), (1, 1), (2, 8), (3, 5), (4, 7), (5, 3), (8, 2), (9, 7), (11, 4), (12, 1), (14, 6), (15, 5), (16, 2), (17, 1), (18, 10), (21, 4), (23, 2), (27, 6), (28, 3), (29, 5), (30, 1), (31, 2), (33, 4), (36, 10), (38, 2), (40, 6), (41, 3), (43, 4), (44, 3), (45, 7), (46, 2)] : List (ℕ × ℕ)).lookup j).getD 0

def h32w22omega : ℕ → ℕ := fun j => (([] : List (ℕ × ℕ)).lookup j).getD 0

def h32w22forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (6, (0, 19)), (8, (0, 23)), (11, (0, 33)), (14, (0, 40)), (16, (0, 46)), (19, (1, 6)), (21, (1, 11)), (23, (1, 16)), (27, (1, 27)), (31, (1, 38)), (33, (1, 43)), (35, (1, 48)), (38, (2, 8)), (40, (2, 14)), (43, (2, 21)), (46, (2, 31)), (48, (2, 35))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h32w22_cert : checkCertA (h32step [2, 2]) 3 54
    h32w22live h32w22rho h32w22omega h32w22forced = true := by decide +kernel

/-! ## The section hypothesis and the theorem -/

theorem h32_sec (X : ℝ) (w : List ℕ) (hw : w.length = 2) (m : ℕ) :
    h32Lget (h32idx (gfamState 3 (chansOfW h32ms w) X 0 m))
        = gfamState 3 (chansOfW h32ms w) X 0 m
      ∧ h32idx (gfamState 3 (chansOfW h32ms w) X 0 m) < 54 := by
  have hms : ∀ a ∈ h32ms, 1 ≤ a := by decide
  have hdvd : ∀ a ∈ h32ms, ∀ j, j ≤ 2 - 1 → a * 3 ^ j ∣ h32N := by decide
  have ht1 : Int.fract (X * ((3 : ℕ) : ℝ) ^ m) < 1 := Int.fract_lt_one _
  rw [gfamState_window 3 (by norm_num) h32ms hms w 2 hw h32N (by norm_num [h32N]) hdvd X m]
  refine h32_section _ ?_
  have hN0 : (0 : ℝ) < (h32N : ℝ) := by norm_num [h32N]
  have hfl : ⌊(h32N : ℝ) * Int.fract (X * ((3 : ℕ) : ℝ) ^ m)⌋ < (h32N : ℤ) := by
    apply Int.floor_lt.2
    push_cast
    calc (h32N : ℝ) * Int.fract (X * ((3 : ℕ) : ℝ) ^ m) < (h32N : ℝ) * 1 :=
          mul_lt_mul_of_pos_left ht1 hN0
      _ = (h32N : ℝ) := by ring
  have hpos' : 0 < h32N := by norm_num [h32N]
  omega

/-- **`S(3,2) ≤ 6`.**  The six multipliers `{1, 2, 4, 5, 7, 8}` hit every base-3
word of length two, on the `54`-state carry-consistency reduction of the
`1632960` ambient states. -/
theorem hitting_3_2_six : Literature.IsHittingSet 3 2 {1, 2, 4, 5, 7, 8} := by
  intro α hα w hw hd
  have hpos : ∀ v : List ℕ, ∀ ch ∈ chansOfW h32ms v, 1 ≤ ch.posSum := by
    intro v ch hch
    simp only [chansOfW, h32ms, List.mem_map] at hch
    obtain ⟨a, ha, rfl⟩ := hch
    simp only [ZChannel.posSum]
    fin_cases ha <;> decide
  have hell : ∀ v : List ℕ, v.length = 2 → ∀ ch ∈ chansOfW h32ms v, 1 ≤ ch.ell := by
    intro v hv2 ch hch
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    simp [ZChannel.ell, hv2]
  have hword : ∀ v : List ℕ, (∀ c ∈ v, c < 3) → ∀ ch ∈ chansOfW h32ms v, ∀ c ∈ ch.word, c < 3 := by
    intro v hv ch hch c hc
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    exact hv c hc
  obtain ⟨a, b, rfl⟩ : ∃ a b, w = [a, b] := by
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hw
    exact ⟨a, b, rfl⟩
  have ha : a < 3 := hd a (by simp)
  have hb : b < 3 := hd b (by simp)
  have key : ∃ ch ∈ chansOfW h32ms [a, b],
      ∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (ch.a * α) ch.word n := by
    interval_cases a <;> interval_cases b
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [0, 0])
        h32Lget h32idx h32w00_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [0, 0] rfl m).2)
        (fun m => (h32_sec α [0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [0, 1])
        h32Lget h32idx h32w01_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [0, 1] rfl m).2)
        (fun m => (h32_sec α [0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [0, 2])
        h32Lget h32idx h32w02_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [0, 2] rfl m).2)
        (fun m => (h32_sec α [0, 2] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [1, 0])
        h32Lget h32idx h32w10_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [1, 0] rfl m).2)
        (fun m => (h32_sec α [1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [1, 1])
        h32Lget h32idx h32w11_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [1, 1] rfl m).2)
        (fun m => (h32_sec α [1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [1, 2])
        h32Lget h32idx h32w12_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [1, 2] rfl m).2)
        (fun m => (h32_sec α [1, 2] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [2, 0])
        h32Lget h32idx h32w20_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [2, 0] rfl m).2)
        (fun m => (h32_sec α [2, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [2, 1])
        h32Lget h32idx h32w21_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [2, 1] rfl m).2)
        (fun m => (h32_sec α [2, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 3 (by norm_num) (chansOfW h32ms [2, 2])
        h32Lget h32idx h32w22_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h32_sec α [2, 2] rfl m).2)
        (fun m => (h32_sec α [2, 2] rfl m).1)
  obtain ⟨ch, hch, hio⟩ := key
  simp only [chansOfW, h32ms, List.map_cons, List.map_nil] at hch
  fin_cases hch
  · exact ⟨1, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨2, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨4, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨5, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨7, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨8, by simp, by norm_num, by simpa using hio⟩

end NormalNumbers.Adder
