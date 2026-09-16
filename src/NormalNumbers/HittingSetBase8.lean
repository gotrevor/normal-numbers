/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetReduced
import NormalNumbers.Literature

/-!
# `S(8,1) ≤ 11`: 11 multipliers hit every base-8 word of length 1 🧵

Emitted by `experiments/emit_hitting_lean.py` from the multiplier set
`{2, 4, 7, 11, 13, 14, 17, 20, 22, 28, 38}` (`experiments/hitting_set_search_reduced.py`).

The ambient state space of this `gfamPred` family is `∏ᵢ mᵢ·8^0 = 892268016640`.
The carry-consistency reduction (`HittingSetReduced.lean`) cuts it to **128 states**:
all channels read the same `X`, so with `t = fract(X·8ᵐ)` the joint state is
`stateOfKW 8 N 1 ms ⌊N·t⌋` for `N = lcm {a·8^j} = 6466460`.

Reachability is kernel `decide +kernel` by **run compression**: `stateOfKW` reads
`k` only through the monotone quotients `(b·k)/N`, so the sweep over `k < 6466460`
is one check per run — **128 runs**.  No `native_decide` anywhere.

* `hitting_8_1_eleven` : `S(8,1) ≤ 11` via `{2, 4, 7, 11, 13, 14, 17, 20, 22, 28, 38}`.

Nothing here claims the matching lower bound.
-/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

/-- The 11 multipliers. -/
def h81ms : List ℕ := [2, 4, 7, 11, 13, 14, 17, 20, 22, 28, 38]

/-- `lcm {a·8^j : a ∈ ms, j ≤ 0}`: the index range of the reachable curve. -/
def h81N : ℕ := 6466460

/-- The 128 reachable joint states, sorted. -/
def h81L : Array ℕ := #[0, 23480737280, 24319335040, 24357453120, 24359359024, 47840096304, 47840208416, 48678814184, 48678814800, 72159552080, 72197670216, 72199576120, 95680313400, 96518911160, 96519023272, 119999760552, 120037878632, 120876484408, 120878390312, 120878390928, 144359128208, 144359240320, 145197838080, 145235956216, 168716693496, 168718599400, 192199336680, 193037942448, 193076060528, 193076061144, 193076173256, 216556910536, 217397414202, 240878151482, 240916269618, 241754875394, 265235612674, 265235724786, 265237630690, 265237631306, 288718368586, 288756486666, 289595084426, 313075821706, 313077727610, 313077839722, 313916445490, 313954563626, 337435300906, 337435301522, 338273899282, 361754636562, 361756542466, 361794660546, 361794772658, 385275509938, 386114115714, 409594852994, 409596758898, 409634877034, 409634877650, 410473475410, 410473587522, 433954324802, 458313691837, 481794429117, 481794541229, 482633138989, 482633139605, 482671257741, 482673163645, 506153900925, 506992506701, 530473243981, 530473356093, 530511474173, 530513380077, 553994117357, 554832715117, 554832715733, 578313453013, 578351571149, 579190176917, 579190289029, 579192194933, 602672932213, 603511529973, 603549648053, 627030385333, 627030385949, 627032291853, 627032403965, 650513141245, 651351747021, 651389865157, 674870602437, 675711106103, 699191843383, 699191955495, 699191956111, 699230074191, 700068679959, 723549417239, 723551323143, 747032060423, 747070178559, 747908776319, 747908888431, 771389625711, 771389626327, 771391532231, 772230138007, 772268256087, 795748993367, 795749105479, 796587703239, 820068440519, 820070346423, 820108464559, 843589201839, 843589202455, 844427808223, 844427920335, 867908657615, 867910563519, 867948681599, 868787279359, 892268016639]

def h81Lget (j : ℕ) : ℕ := h81L.getD j 0

def h81idx (s : ℕ) : ℕ := (bfind h81L s).getD 0

def h81step (w : List ℕ) : ℕ → ℕ → Option ℕ :=
  fun σ j => (gfamPred 8 (chansOfW h81ms w) (σ % 8) (σ / 8) (h81Lget j)).map h81idx

/-- The reachability check at one index. -/
def h81ok (k : ℕ) : Bool :=
  decide (h81Lget (h81idx (stateOfKW 8 h81N 1 h81ms k)) = stateOfKW 8 h81N 1 h81ms k)
    && decide (h81idx (stateOfKW 8 h81N 1 h81ms k) < 128)

/-- The run endpoints: 128 runs tile `[0, 6466460)`. -/
def h81runs : List ℕ := [170170, 230945, 293930, 323323, 340340, 380380, 461890, 497420, 510510, 587860, 646646, 680680, 692835, 760760, 850850, 881790, 923780, 969969, 994840, 1021020, 1141140, 1154725, 1175720, 1191190, 1293292, 1361360, 1385670, 1469650, 1492260, 1521520, 1531530, 1616615, 1701700, 1763580, 1847560, 1871870, 1901900, 1939938, 1989680, 2042040, 2057510, 2078505, 2212210, 2263261, 2282280, 2309450, 2351440, 2382380, 2487100, 2540395, 2552550, 2586584, 2645370, 2662660, 2722720, 2771340, 2892890, 2909907, 2939300, 2984520, 3002285, 3043040, 3063060, 3233230, 3403400, 3423420, 3464175, 3481940, 3527160, 3556553, 3573570, 3695120, 3743740, 3803800, 3821090, 3879876, 3913910, 3926065, 3979360, 4084080, 4115020, 4157010, 4184180, 4203199, 4254250, 4387955, 4408950, 4424420, 4476780, 4526522, 4564560, 4594590, 4618900, 4702880, 4764760, 4849845, 4934930, 4944940, 4974200, 4996810, 5080790, 5105100, 5173168, 5275270, 5290740, 5311735, 5325320, 5445440, 5471620, 5496491, 5542680, 5584670, 5615610, 5705700, 5773625, 5785780, 5819814, 5878600, 5955950, 5969040, 6004570, 6086080, 6126120, 6143137, 6172530, 6235515, 6296290, 6466460]

/-- The per-run check: the quotients are constant across the run, and the run's
first index is reachable. -/
def h81P (lo hi : ℕ) : Bool :=
  (coeffsOf 8 h81ms 1).all (fun b => decide ((b * lo) / h81N = (b * (hi - 1)) / h81N))
    && h81ok lo

theorem h81_runs_ok : runsCover h81P 0 h81runs h81N = true := by decide +kernel

/-- **Reachability**, by run compression: 128 kernel checks instead of 6466460. -/
theorem h81_section (k : ℕ) (hk : k < h81N) :
    h81Lget (h81idx (stateOfKW 8 h81N 1 h81ms k)) = stateOfKW 8 h81N 1 h81ms k
      ∧ h81idx (stateOfKW 8 h81N 1 h81ms k) < 128 := by
  refine runsCover_spec (P := h81P) (Q := fun k =>
    h81Lget (h81idx (stateOfKW 8 h81N 1 h81ms k)) = stateOfKW 8 h81N 1 h81ms k
      ∧ h81idx (stateOfKW 8 h81N 1 h81ms k) < 128) ?_ h81runs 0 h81N h81_runs_ok k (by omega) hk
  intro lo hi hP j hj1 hj2
  simp only [h81P, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hP
  have hconst : stateOfKW 8 h81N 1 h81ms j = stateOfKW 8 h81N 1 h81ms lo := by
    refine stateOfKW_congr 8 h81N 1 (by omega) h81ms j lo ?_
    intro b hb
    exact quot_const_of_run b h81N lo hi j hj1 hj2 (hP.1 b hb)
  have h := hP.2
  simp only [h81ok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hconst]
  exact h


/-- Certificate for the word `[0]`: 35 live states of the 128. -/
def h81w0live : ℕ → Bool := fun j => [6, 9, 13, 15, 16, 20, 24, 25, 26, 27, 31, 34, 42, 43, 48, 51, 55, 63, 71, 75, 78, 80, 85, 92, 95, 100, 102, 103, 107, 110, 114, 116, 125, 126, 127].contains j

def h81w0rho : ℕ → ℕ := fun j => (([(6, 1), (9, 1), (13, 5), (15, 2), (20, 7), (24, 3), (25, 7), (26, 1), (27, 11), (31, 9), (42, 6), (43, 4), (48, 2), (51, 3), (55, 4), (63, 9), (75, 3), (78, 5), (80, 2), (85, 6), (95, 9), (100, 1), (102, 3), (103, 10), (107, 7), (114, 3), (116, 4), (125, 1), (126, 2), (127, 8)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w0omega : ℕ → ℕ := fun j => (([(14, 1), (38, 1), (52, 1), (54, 1), (56, 1), (79, 1), (84, 1), (88, 1), (108, 1), (113, 1), (117, 1), (118, 1), (121, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w0forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(16, (1, 16)), (24, (1, 75)), (34, (2, 34)), (42, (2, 85)), (51, (3, 24)), (55, (3, 55)), (71, (4, 71)), (75, (4, 102)), (85, (5, 42)), (92, (5, 92)), (102, (6, 51)), (110, (6, 110)), (127, (7, 127))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w0_cert : checkCertA (h81step [0]) 8 128
    h81w0live h81w0rho h81w0omega h81w0forced = true := by decide +kernel


/-- Certificate for the word `[1]`: 19 live states of the 128. -/
def h81w1live : ℕ → Bool := fun j => [0, 22, 32, 33, 42, 43, 44, 45, 55, 56, 63, 64, 85, 86, 96, 103, 108, 110, 127].contains j

def h81w1rho : ℕ → ℕ := fun j => (([(22, 1), (32, 1), (33, 2), (42, 5), (43, 2), (44, 4), (45, 3), (63, 6), (64, 2), (85, 5), (86, 1), (96, 1), (103, 3), (108, 2), (110, 4), (127, 5)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w1omega : ℕ → ℕ := fun j => (([(15, 1), (16, 2), (23, 1), (25, 3), (26, 2), (27, 1), (29, 1), (31, 2), (34, 4), (49, 3), (50, 1), (52, 3), (54, 1), (65, 3), (66, 1), (80, 1), (81, 2), (87, 1), (89, 1), (90, 1), (92, 2), (97, 1), (98, 1), (99, 1), (104, 4), (105, 1), (106, 1), (107, 1), (109, 1), (116, 1), (117, 3), (118, 1), (121, 1), (122, 1), (123, 1), (125, 1), (126, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w1forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (42, (2, 85)), (55, (3, 55)), (56, (3, 56)), (85, (5, 42)), (127, (7, 127))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w1_cert : checkCertA (h81step [1]) 8 128
    h81w1live h81w1rho h81w1omega h81w1forced = true := by decide +kernel


/-- Certificate for the word `[2]`: 43 live states of the 128. -/
def h81w2live : ℕ → Bool := fun j => [0, 5, 13, 24, 25, 27, 29, 31, 34, 36, 37, 43, 45, 46, 51, 52, 54, 56, 60, 63, 64, 65, 66, 67, 68, 70, 71, 75, 76, 89, 90, 94, 95, 100, 102, 103, 110, 111, 114, 118, 120, 126, 127].contains j

def h81w2rho : ℕ → ℕ := fun j => (([(5, 12), (25, 4), (27, 5), (29, 1), (31, 10), (34, 11), (36, 7), (37, 2), (43, 6), (45, 1), (46, 2), (52, 4), (54, 3), (56, 11), (60, 2), (63, 10), (64, 1), (65, 6), (66, 11), (67, 8), (68, 7), (70, 4), (71, 11), (76, 4), (89, 1), (90, 5), (94, 1), (95, 10), (100, 5), (103, 4), (111, 1), (118, 8), (120, 4), (126, 6), (127, 9)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w2omega : ℕ → ℕ := fun j => (([(28, 1), (33, 1), (44, 1), (48, 1), (49, 1), (55, 1), (59, 1), (91, 1), (92, 1), (98, 1), (99, 1), (121, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w2forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (13, (0, 114)), (24, (1, 75)), (25, (1, 76)), (27, (1, 100)), (51, (3, 24)), (52, (3, 25)), (56, (3, 71)), (71, (4, 56)), (75, (4, 102)), (76, (4, 103)), (100, (6, 27)), (102, (6, 51)), (103, (6, 52)), (110, (6, 110)), (111, (6, 111)), (114, (7, 13)), (127, (7, 127))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w2_cert : checkCertA (h81step [2]) 8 128
    h81w2live h81w2rho h81w2omega h81w2forced = true := by decide +kernel


/-- Certificate for the word `[3]`: 18 live states of the 128. -/
def h81w3live : ℕ → Bool := fun j => [0, 20, 32, 34, 35, 42, 51, 53, 64, 67, 68, 85, 96, 101, 107, 116, 121, 127].contains j

def h81w3rho : ℕ → ℕ := fun j => (([(20, 2), (32, 1), (34, 2), (42, 1), (51, 3), (53, 1), (64, 1), (67, 1), (68, 2), (85, 1), (96, 1), (101, 1), (107, 2), (116, 3), (121, 2), (127, 4)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w3omega : ℕ → ℕ := fun j => (([(3, 1), (7, 1), (8, 1), (9, 1), (10, 1), (16, 2), (17, 4), (18, 1), (22, 3), (23, 2), (36, 1), (37, 1), (38, 3), (50, 5), (54, 4), (55, 1), (56, 2), (57, 2), (58, 1), (59, 1), (61, 1), (63, 1), (65, 1), (69, 1), (71, 2), (72, 1), (73, 1), (75, 1), (87, 2), (88, 2), (102, 1), (103, 2), (108, 1), (115, 5), (117, 1), (122, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w3forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (34, (2, 34)), (35, (2, 35)), (42, (2, 85)), (85, (5, 42)), (127, (7, 127))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w3_cert : checkCertA (h81step [3]) 8 128
    h81w3live h81w3rho h81w3omega h81w3forced = true := by decide +kernel


/-- Certificate for the word `[4]`: 18 live states of the 128. -/
def h81w4live : ℕ → Bool := fun j => [0, 6, 11, 20, 26, 31, 42, 59, 60, 63, 74, 76, 85, 92, 93, 95, 107, 127].contains j

def h81w4rho : ℕ → ℕ := fun j => (([(0, 4), (6, 2), (11, 3), (20, 2), (26, 1), (31, 1), (42, 1), (59, 2), (60, 1), (63, 1), (74, 1), (76, 3), (85, 1), (93, 2), (95, 1), (107, 2)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w4omega : ℕ → ℕ := fun j => (([(5, 1), (10, 1), (12, 5), (19, 1), (24, 2), (25, 1), (39, 2), (40, 2), (52, 1), (54, 1), (55, 1), (56, 2), (58, 1), (62, 1), (64, 1), (66, 1), (68, 1), (69, 1), (70, 2), (71, 2), (72, 1), (73, 4), (77, 5), (89, 3), (90, 1), (91, 1), (104, 2), (105, 3), (109, 1), (110, 4), (111, 2), (117, 1), (118, 1), (119, 1), (120, 1), (124, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w4forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (42, (2, 85)), (85, (5, 42)), (92, (5, 92)), (93, (5, 93)), (127, (7, 127))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w4_cert : checkCertA (h81step [4]) 8 128
    h81w4live h81w4rho h81w4omega h81w4forced = true := by decide +kernel


/-- Certificate for the word `[5]`: 43 live states of the 128. -/
def h81w5live : ℕ → Bool := fun j => [0, 1, 7, 9, 13, 16, 17, 24, 25, 27, 32, 33, 37, 38, 51, 52, 56, 57, 59, 60, 61, 62, 63, 64, 67, 71, 73, 75, 76, 81, 82, 84, 90, 91, 93, 96, 98, 100, 102, 103, 114, 122, 127].contains j

def h81w5rho : ℕ → ℕ := fun j => (([(0, 9), (1, 6), (7, 4), (9, 8), (16, 1), (24, 4), (27, 5), (32, 10), (33, 1), (37, 5), (38, 1), (51, 4), (56, 11), (57, 4), (59, 7), (60, 8), (61, 11), (62, 6), (63, 1), (64, 10), (67, 2), (71, 11), (73, 3), (75, 4), (81, 2), (82, 1), (84, 6), (90, 2), (91, 7), (93, 11), (96, 10), (98, 1), (100, 5), (102, 4), (122, 12)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w5omega : ℕ → ℕ := fun j => (([(6, 1), (28, 1), (29, 1), (35, 1), (36, 1), (68, 1), (72, 1), (78, 1), (79, 1), (83, 1), (94, 1), (99, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w5forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (13, (0, 114)), (16, (1, 16)), (17, (1, 17)), (24, (1, 75)), (25, (1, 76)), (27, (1, 100)), (51, (3, 24)), (52, (3, 25)), (56, (3, 71)), (71, (4, 56)), (75, (4, 102)), (76, (4, 103)), (100, (6, 27)), (102, (6, 51)), (103, (6, 52)), (114, (7, 13)), (127, (7, 127))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w5_cert : checkCertA (h81step [5]) 8 128
    h81w5live h81w5rho h81w5omega h81w5forced = true := by decide +kernel


/-- Certificate for the word `[6]`: 19 live states of the 128. -/
def h81w6live : ℕ → Bool := fun j => [0, 17, 19, 24, 31, 41, 42, 63, 64, 71, 72, 82, 83, 84, 85, 94, 95, 105, 127].contains j

def h81w6rho : ℕ → ℕ := fun j => (([(0, 5), (17, 4), (19, 2), (24, 3), (31, 1), (41, 1), (42, 5), (63, 2), (64, 6), (82, 3), (83, 4), (84, 2), (85, 5), (94, 2), (95, 1), (105, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w6omega : ℕ → ℕ := fun j => (([(1, 1), (2, 1), (4, 1), (5, 1), (6, 1), (9, 1), (10, 3), (11, 1), (18, 1), (20, 1), (21, 1), (22, 1), (23, 4), (28, 1), (29, 1), (30, 1), (35, 2), (37, 1), (38, 1), (40, 1), (46, 2), (47, 1), (61, 1), (62, 3), (73, 1), (75, 3), (77, 1), (78, 3), (93, 4), (96, 2), (98, 1), (100, 1), (101, 2), (102, 3), (104, 1), (111, 2), (112, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w6forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (42, (2, 85)), (71, (4, 71)), (72, (4, 72)), (85, (5, 42)), (127, (7, 127))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w6_cert : checkCertA (h81step [6]) 8 128
    h81w6live h81w6rho h81w6omega h81w6forced = true := by decide +kernel


/-- Certificate for the word `[7]`: 35 live states of the 128. -/
def h81w7live : ℕ → Bool := fun j => [0, 1, 2, 11, 13, 17, 20, 24, 25, 27, 32, 35, 42, 47, 49, 52, 56, 64, 72, 76, 79, 84, 85, 93, 96, 100, 101, 102, 103, 107, 111, 112, 114, 118, 121].contains j

def h81w7rho : ℕ → ℕ := fun j => (([(0, 8), (1, 2), (2, 1), (11, 4), (13, 3), (20, 7), (24, 10), (25, 3), (27, 1), (32, 9), (42, 6), (47, 2), (49, 5), (52, 3), (64, 9), (72, 4), (76, 3), (79, 2), (84, 4), (85, 6), (96, 9), (100, 11), (101, 1), (102, 7), (103, 3), (107, 7), (112, 2), (114, 5), (118, 1), (121, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w7omega : ℕ → ℕ := fun j => (([(6, 1), (9, 1), (10, 1), (14, 1), (19, 1), (39, 1), (43, 1), (48, 1), (71, 1), (73, 1), (75, 1), (89, 1), (113, 1)] : List (ℕ × ℕ)).lookup j).getD 0

def h81w7forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ([(0, (0, 0)), (17, (1, 17)), (25, (1, 76)), (35, (2, 35)), (42, (2, 85)), (52, (3, 25)), (56, (3, 56)), (72, (4, 72)), (76, (4, 103)), (85, (5, 42)), (93, (5, 93)), (103, (6, 52)), (111, (6, 111))] : List (ℕ × ℕ × ℕ)).lookup j

theorem h81w7_cert : checkCertA (h81step [7]) 8 128
    h81w7live h81w7rho h81w7omega h81w7forced = true := by decide +kernel


/-- The section hypothesis of `signed_engine_g_single_reduced`, from `h81_section`. -/
theorem h81_sec (X : ℝ) (w : List ℕ) (hw : w.length = 1) (m : ℕ) :
    h81Lget (h81idx (gfamState 8 (chansOfW h81ms w) X 0 m))
        = gfamState 8 (chansOfW h81ms w) X 0 m
      ∧ h81idx (gfamState 8 (chansOfW h81ms w) X 0 m) < 128 := by
  have hms : ∀ a ∈ h81ms, 1 ≤ a := by decide
  have hdvd : ∀ a ∈ h81ms, ∀ j, j ≤ 1 - 1 → a * 8 ^ j ∣ h81N := by decide
  have ht1 : Int.fract (X * ((8 : ℕ) : ℝ) ^ m) < 1 := Int.fract_lt_one _
  rw [gfamState_window 8 (by norm_num) h81ms hms w 1 hw h81N (by norm_num [h81N]) hdvd X m]
  refine h81_section _ ?_
  have hN0 : (0 : ℝ) < (h81N : ℝ) := by norm_num [h81N]
  have hfl : ⌊(h81N : ℝ) * Int.fract (X * ((8 : ℕ) : ℝ) ^ m)⌋ < (h81N : ℤ) := by
    apply Int.floor_lt.2
    push_cast
    calc (h81N : ℝ) * Int.fract (X * ((8 : ℕ) : ℝ) ^ m) < (h81N : ℝ) * 1 :=
          mul_lt_mul_of_pos_left ht1 hN0
      _ = (h81N : ℝ) := by ring
  have hpos' : 0 < h81N := by norm_num [h81N]
  omega

/-- **`S(8,1) ≤ 11`.** -/
theorem hitting_8_1_eleven : Literature.IsHittingSet 8 1 {2, 4, 7, 11, 13, 14, 17, 20, 22, 28, 38} := by
  intro α hα w hw hd
  have hpos : ∀ v : List ℕ, ∀ ch ∈ chansOfW h81ms v, 1 ≤ ch.posSum := by
    intro v ch hch
    simp only [chansOfW, h81ms, List.mem_map] at hch
    obtain ⟨a, ha, rfl⟩ := hch
    simp only [ZChannel.posSum]
    fin_cases ha <;> decide
  have hell : ∀ v : List ℕ, v.length = 1 → ∀ ch ∈ chansOfW h81ms v, 1 ≤ ch.ell := by
    intro v hv ch hch
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    simp [ZChannel.ell, hv]
  have hword : ∀ v : List ℕ, (∀ c ∈ v, c < 8) → ∀ ch ∈ chansOfW h81ms v, ∀ c ∈ ch.word, c < 8 := by
    intro v hv ch hch c hc
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    exact hv c hc
  obtain ⟨d0, rfl⟩ : ∃ d0, w = [d0] := by
    rcases w with _ | ⟨d0, _ | ⟨z, t⟩⟩ <;> simp at hw
    exact ⟨d0, rfl⟩
  have hltd0 : d0 < 8 := hd d0 (by simp)
  have key : ∃ ch ∈ chansOfW h81ms [d0],
      ∀ N, ∃ n, N ≤ n ∧ OccursAt 8 (ch.a * α) ch.word n := by
    interval_cases d0
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [0])
        h81Lget h81idx h81w0_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [0] rfl m).2)
        (fun m => (h81_sec α [0] rfl m).1)
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [1])
        h81Lget h81idx h81w1_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [1] rfl m).2)
        (fun m => (h81_sec α [1] rfl m).1)
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [2])
        h81Lget h81idx h81w2_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [2] rfl m).2)
        (fun m => (h81_sec α [2] rfl m).1)
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [3])
        h81Lget h81idx h81w3_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [3] rfl m).2)
        (fun m => (h81_sec α [3] rfl m).1)
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [4])
        h81Lget h81idx h81w4_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [4] rfl m).2)
        (fun m => (h81_sec α [4] rfl m).1)
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [5])
        h81Lget h81idx h81w5_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [5] rfl m).2)
        (fun m => (h81_sec α [5] rfl m).1)
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [6])
        h81Lget h81idx h81w6_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [6] rfl m).2)
        (fun m => (h81_sec α [6] rfl m).1)
    · exact signed_engine_g_single_reduced 8 (by norm_num) (chansOfW h81ms [7])
        h81Lget h81idx h81w7_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h81_sec α [7] rfl m).2)
        (fun m => (h81_sec α [7] rfl m).1)
  obtain ⟨ch, hch, hio⟩ := key
  simp only [chansOfW, h81ms, List.map_cons, List.map_nil] at hch
  fin_cases hch
  · exact ⟨2, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨4, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨7, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨11, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨13, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨14, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨17, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨20, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨22, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨28, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨38, by simp, by norm_num, by simpa using hio⟩

end NormalNumbers.Adder
