/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBounds

/-!
# `S(7,1) ≤ 7` and the base-7 lower wiring 🧵

Continues `HittingSetBounds.lean` at base `7`.  The hitting-set search
(`experiments/hitting_set_search.py`, `docs/hitting-set-invariant-2026-09-13.md`
row `(7,1)`) found the seven multipliers `{1, 2, 3, 4, 5, 6, 13}`; the emitter
`experiments/adder_baseg_emit.py h71` produced one certificate per base-7 digit
(`experiments/certs/adder_cert_h71_d{0..6}.json`, ambient `9360` states, `14`–`21`
live states each), Python-verified.  The signed base-`g` engine
`signed_engine_g_single` turns them into

* `hitting_7_1_seven` : `S(7,1) ≤ 7`, hitting set `{1, 2, 3, 4, 5, 6, 13}`.

The lower wiring is `Mahler.mahler_lower_bound_base7` unfolded at its witness and
`w = [1]`:

* `not_hitting_7_1_eight` : the initial segment `{1,…,8}` is **not** a hitting set;
* `not_hitting_7_1_six`   : neither is `{1,…,6}` (`IsHittingSet.mono`).

Every certificate is a kernel `decide` (`decide +kernel`, no `native_decide`).
A whole-certificate `checkCertA` over the `9360 · 7` edges does close in the kernel
(one certificate alone: about `11` minutes, `10` GB), but seven of them elaborated
together exhaust the box, so each edge sweep is split into six `1560`-state
`checkEdgesOnA` chunks glued by `checkEdgesOnA_of_chunks` plus one `checkForcedA`,
exactly as the `h23` family in `HittingSetBounds.lean`.  The module builds in about
`24` minutes at a `9` GB peak.

Nothing here claims the lower bound `S(7,1) ≥ 7` (that every `6`-set fails); the
search only excludes `6`-sets with all multipliers below `24`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-! ## `S(7,1) ≤ 7`: the family `x, 2x, 3x, 4x, 5x, 6x, 13x` -/

def h71Chans (d : ℕ) : List ZChannel :=
  [⟨1, 0, [d]⟩, ⟨2, 0, [d]⟩, ⟨3, 0, [d]⟩, ⟨4, 0, [d]⟩, ⟨5, 0, [d]⟩, ⟨6, 0, [d]⟩, ⟨13, 0, [d]⟩]

/-- Certificate `h71_d0` (`experiments/certs/adder_cert_h71_d0.json`): word `[0]`, ambient `9360`, `14` live states. -/
def h71d0live : ℕ → Bool := fun s => [1440, 1560, 2304, 3030, 3872, 3896, 4616, 5463, 6207, 7049, 7775, 7799, 8639, 9359].contains s

def h71d0rho : ℕ → ℕ := fun s =>
  (([(1560, 1), (2304, 2), (3030, 3), (3872, 1), (3896, 2), (4616, 4), (5463, 1), (6207, 5), (7049, 2), (7775, 1), (8639, 4), (9359, 6)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d0omega : ℕ → ℕ := fun s =>
  (([(720, 1), (744, 1), (840, 1), (864, 1), (1464, 1), (1584, 2), (2160, 1), (2184, 1), (2280, 1), (2310, 2), (2312, 1), (2430, 1), (2432, 1), (3032, 1), (3150, 1), (3152, 1), (3750, 1), (3752, 1), (3870, 1), (3902, 1), (4016, 1), (4022, 1), (4622, 1), (4736, 1), (4742, 1), (5336, 1), (5342, 1), (5456, 1), (5462, 1), (5487, 1), (5583, 1), (5607, 1), (6183, 1), (6303, 1), (6327, 1), (6903, 1), (6927, 1), (7023, 1), (7047, 1), (7055, 1), (7073, 1), (7079, 1), (7769, 1), (7793, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d0forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(1440, (1, 1440)), (1560, (1, 3872)), (2304, (1, 7049)), (3030, (2, 3030)), (3872, (2, 7775)), (4616, (3, 4616)), (5463, (4, 1560)), (6207, (4, 6207)), (7049, (5, 2304)), (7775, (5, 5463)), (7799, (5, 7799)), (9359, (6, 9359))] : List (ℕ × ℕ × ℕ)).lookup s

theorem h71d0_c0 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 h71d0live h71d0rho h71d0omega h71d0forced 0 1560 = true := by decide +kernel

theorem h71d0_c1 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 h71d0live h71d0rho h71d0omega h71d0forced 1560 1560 = true := by decide +kernel

theorem h71d0_c2 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 h71d0live h71d0rho h71d0omega h71d0forced 3120 1560 = true := by decide +kernel

theorem h71d0_c3 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 h71d0live h71d0rho h71d0omega h71d0forced 4680 1560 = true := by decide +kernel

theorem h71d0_c4 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 h71d0live h71d0rho h71d0omega h71d0forced 6240 1560 = true := by decide +kernel

theorem h71d0_c5 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 h71d0live h71d0rho h71d0omega h71d0forced 7800 1560 = true := by decide +kernel

theorem h71d0_forced : checkForcedA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 9360 h71d0live h71d0forced = true := by decide +kernel

theorem h71d0_cert : checkCertA (fun σ s' => gfamPred 7 (h71Chans 0) (σ % 7) (σ / 7) s')
    7 9360 h71d0live h71d0rho h71d0omega h71d0forced = true := by
  refine checkCertA_of_edgesOn ?_ h71d0_forced
  have h := checkEdgesOnA_of_chunks (c := 1560) 6 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h71d0_c0, h71d0_c1, h71d0_c2, h71d0_c3, h71d0_c4, h71d0_c5])
  exact h

/-- Certificate `h71_d1` (`experiments/certs/adder_cert_h71_d1.json`): word `[1]`, ambient `9360`, `21` live states. -/
def h71d1live : ℕ → Bool := fun s => [0, 3030, 3032, 3150, 3152, 4616, 4617, 4622, 4623, 4736, 4737, 4742, 4743, 6207, 6209, 6327, 6329, 7055, 7799, 8639, 9359].contains s

def h71d1rho : ℕ → ℕ := fun s =>
  (([(3152, 1), (4743, 1), (6329, 4), (7055, 2), (7799, 3), (8639, 2), (9359, 5)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d1omega : ℕ → ℕ := fun s =>
  (([(720, 1), (2310, 1), (2312, 1), (2334, 1), (2336, 1), (2430, 1), (2432, 1), (2454, 1), (2456, 1), (3054, 1), (3056, 1), (3174, 1), (3176, 1), (3750, 1), (3752, 1), (3774, 1), (3776, 1), (3870, 1), (3872, 2), (3894, 1), (3896, 1), (3897, 1), (3902, 1), (3903, 1), (4016, 1), (4017, 1), (4022, 1), (4023, 1), (5336, 1), (5337, 1), (5342, 1), (5343, 1), (5456, 1), (5457, 1), (5462, 1), (5463, 2), (5465, 1), (5487, 1), (5489, 1), (5583, 1), (5585, 1), (5607, 1), (5609, 1), (6183, 1), (6185, 1), (6303, 1), (6305, 1), (6903, 1), (6905, 1), (6927, 1), (6929, 1), (7023, 1), (7025, 1), (7047, 1), (7049, 2), (7073, 1), (7079, 1), (7169, 1), (7175, 1), (7193, 1), (7199, 1), (7769, 1), (7775, 3), (7793, 1), (7889, 1), (7895, 1), (7913, 1), (7919, 2), (8489, 1), (8495, 1), (8513, 1), (8519, 1), (8609, 1), (8615, 1), (8633, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d1forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (3030, (2, 3030)), (3032, (2, 3032)), (3150, (2, 3150)), (3152, (2, 3152)), (4616, (3, 4616)), (4617, (3, 4617)), (4622, (3, 4622)), (4623, (3, 4623)), (4736, (3, 4736)), (4737, (3, 4737)), (4742, (3, 4742)), (4743, (3, 4743)), (6207, (4, 6207)), (6209, (4, 6209)), (6327, (4, 6327)), (6329, (4, 6329)), (9359, (6, 9359))] : List (ℕ × ℕ × ℕ)).lookup s

theorem h71d1_c0 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 h71d1live h71d1rho h71d1omega h71d1forced 0 1560 = true := by decide +kernel

theorem h71d1_c1 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 h71d1live h71d1rho h71d1omega h71d1forced 1560 1560 = true := by decide +kernel

theorem h71d1_c2 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 h71d1live h71d1rho h71d1omega h71d1forced 3120 1560 = true := by decide +kernel

theorem h71d1_c3 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 h71d1live h71d1rho h71d1omega h71d1forced 4680 1560 = true := by decide +kernel

theorem h71d1_c4 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 h71d1live h71d1rho h71d1omega h71d1forced 6240 1560 = true := by decide +kernel

theorem h71d1_c5 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 h71d1live h71d1rho h71d1omega h71d1forced 7800 1560 = true := by decide +kernel

theorem h71d1_forced : checkForcedA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 9360 h71d1live h71d1forced = true := by decide +kernel

theorem h71d1_cert : checkCertA (fun σ s' => gfamPred 7 (h71Chans 1) (σ % 7) (σ / 7) s')
    7 9360 h71d1live h71d1rho h71d1omega h71d1forced = true := by
  refine checkCertA_of_edgesOn ?_ h71d1_forced
  have h := checkEdgesOnA_of_chunks (c := 1560) 6 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h71d1_c0, h71d1_c1, h71d1_c2, h71d1_c3, h71d1_c4, h71d1_c5])
  exact h

/-- Certificate `h71_d2` (`experiments/certs/adder_cert_h71_d2.json`): word `[2]`, ambient `9360`, `18` live states. -/
def h71d2live : ℕ → Bool := fun s => [0, 1584, 2304, 2310, 4616, 4617, 4622, 4623, 4736, 4737, 4742, 4743, 5463, 5487, 7049, 7055, 7799, 9359].contains s

def h71d2rho : ℕ → ℕ := fun s =>
  (([(0, 3), (1584, 1), (2304, 2), (4743, 5), (5463, 4), (5487, 1), (7049, 2), (7799, 3), (9359, 6)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d2omega : ℕ → ℕ := fun s =>
  (([(720, 1), (726, 1), (744, 1), (750, 1), (840, 1), (846, 1), (864, 1), (870, 1), (1440, 1), (1446, 1), (1464, 1), (1470, 1), (1560, 1), (1566, 1), (1590, 1), (2160, 1), (2166, 1), (2184, 1), (2190, 1), (2280, 1), (2286, 1), (3896, 1), (3897, 1), (3902, 1), (3903, 1), (4016, 1), (4017, 1), (4022, 1), (4023, 1), (5336, 1), (5337, 1), (5342, 1), (5343, 1), (5456, 1), (5457, 1), (5462, 1), (5465, 1), (5489, 1), (5583, 1), (5585, 1), (5607, 1), (5609, 1), (6183, 1), (6185, 1), (6207, 2), (6209, 1), (6303, 1), (6305, 1), (6327, 1), (6329, 1), (6903, 1), (6905, 1), (6927, 1), (6929, 1), (7023, 1), (7025, 1), (7047, 1), (7073, 1), (7079, 1), (7169, 1), (7175, 1), (7193, 1), (7199, 1), (7769, 1), (7775, 2), (7793, 1), (7889, 1), (7895, 1), (7913, 1), (7919, 2), (8489, 1), (8495, 1), (8513, 1), (8519, 1), (8609, 1), (8615, 1), (8633, 1), (8639, 2)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d2forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (2304, (1, 7049)), (2310, (1, 7055)), (4616, (3, 4616)), (4617, (3, 4617)), (4622, (3, 4622)), (4623, (3, 4623)), (4736, (3, 4736)), (4737, (3, 4737)), (4742, (3, 4742)), (4743, (3, 4743)), (7049, (5, 2304)), (7055, (5, 2310)), (9359, (6, 9359))] : List (ℕ × ℕ × ℕ)).lookup s

theorem h71d2_c0 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 h71d2live h71d2rho h71d2omega h71d2forced 0 1560 = true := by decide +kernel

theorem h71d2_c1 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 h71d2live h71d2rho h71d2omega h71d2forced 1560 1560 = true := by decide +kernel

theorem h71d2_c2 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 h71d2live h71d2rho h71d2omega h71d2forced 3120 1560 = true := by decide +kernel

theorem h71d2_c3 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 h71d2live h71d2rho h71d2omega h71d2forced 4680 1560 = true := by decide +kernel

theorem h71d2_c4 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 h71d2live h71d2rho h71d2omega h71d2forced 6240 1560 = true := by decide +kernel

theorem h71d2_c5 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 h71d2live h71d2rho h71d2omega h71d2forced 7800 1560 = true := by decide +kernel

theorem h71d2_forced : checkForcedA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 9360 h71d2live h71d2forced = true := by decide +kernel

theorem h71d2_cert : checkCertA (fun σ s' => gfamPred 7 (h71Chans 2) (σ % 7) (σ / 7) s')
    7 9360 h71d2live h71d2rho h71d2omega h71d2forced = true := by
  refine checkCertA_of_edgesOn ?_ h71d2_forced
  have h := checkEdgesOnA_of_chunks (c := 1560) 6 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h71d2_c0, h71d2_c1, h71d2_c2, h71d2_c3, h71d2_c4, h71d2_c5])
  exact h

/-- Certificate `h71_d3` (`experiments/certs/adder_cert_h71_d3.json`): word `[3]`, ambient `9360`, `18` live states. -/
def h71d3live : ℕ → Bool := fun s => [0, 1560, 1584, 3030, 3032, 3150, 3152, 3872, 3896, 5463, 5487, 6207, 6209, 6327, 6329, 7775, 7799, 9359].contains s

def h71d3rho : ℕ → ℕ := fun s =>
  (([(0, 2), (3030, 1), (6329, 1), (9359, 2)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d3omega : ℕ → ℕ := fun s =>
  (([(720, 2), (726, 1), (744, 1), (750, 1), (840, 1), (846, 1), (864, 1), (870, 1), (1440, 1), (1446, 1), (1464, 1), (1470, 1), (1566, 1), (1590, 1), (2160, 1), (2166, 1), (2184, 1), (2190, 1), (2280, 1), (2286, 1), (2304, 1), (2310, 2), (2312, 1), (2334, 1), (2336, 1), (2430, 1), (2432, 1), (2454, 1), (2456, 1), (3054, 1), (3056, 1), (3174, 1), (3176, 1), (3750, 1), (3752, 1), (3774, 1), (3776, 1), (3870, 1), (3894, 1), (5465, 1), (5489, 1), (5583, 1), (5585, 1), (5607, 1), (5609, 1), (6183, 1), (6185, 1), (6303, 1), (6305, 1), (6903, 1), (6905, 1), (6927, 1), (6929, 1), (7023, 1), (7025, 1), (7047, 1), (7049, 2), (7055, 1), (7073, 1), (7079, 1), (7169, 1), (7175, 1), (7193, 1), (7199, 1), (7769, 1), (7793, 1), (7889, 1), (7895, 1), (7913, 1), (7919, 1), (8489, 1), (8495, 1), (8513, 1), (8519, 1), (8609, 1), (8615, 1), (8633, 1), (8639, 2)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d3forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (1560, (1, 3872)), (1584, (1, 3896)), (3030, (2, 3030)), (3032, (2, 3032)), (3150, (2, 3150)), (3152, (2, 3152)), (3872, (2, 7775)), (3896, (2, 7799)), (5463, (4, 1560)), (5487, (4, 1584)), (6207, (4, 6207)), (6209, (4, 6209)), (6327, (4, 6327)), (6329, (4, 6329)), (7775, (5, 5463)), (7799, (5, 5487)), (9359, (6, 9359))] : List (ℕ × ℕ × ℕ)).lookup s

theorem h71d3_c0 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 h71d3live h71d3rho h71d3omega h71d3forced 0 1560 = true := by decide +kernel

theorem h71d3_c1 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 h71d3live h71d3rho h71d3omega h71d3forced 1560 1560 = true := by decide +kernel

theorem h71d3_c2 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 h71d3live h71d3rho h71d3omega h71d3forced 3120 1560 = true := by decide +kernel

theorem h71d3_c3 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 h71d3live h71d3rho h71d3omega h71d3forced 4680 1560 = true := by decide +kernel

theorem h71d3_c4 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 h71d3live h71d3rho h71d3omega h71d3forced 6240 1560 = true := by decide +kernel

theorem h71d3_c5 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 h71d3live h71d3rho h71d3omega h71d3forced 7800 1560 = true := by decide +kernel

theorem h71d3_forced : checkForcedA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 9360 h71d3live h71d3forced = true := by decide +kernel

theorem h71d3_cert : checkCertA (fun σ s' => gfamPred 7 (h71Chans 3) (σ % 7) (σ / 7) s')
    7 9360 h71d3live h71d3rho h71d3omega h71d3forced = true := by
  refine checkCertA_of_edgesOn ?_ h71d3_forced
  have h := checkEdgesOnA_of_chunks (c := 1560) 6 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h71d3_c0, h71d3_c1, h71d3_c2, h71d3_c3, h71d3_c4, h71d3_c5])
  exact h

/-- Certificate `h71_d4` (`experiments/certs/adder_cert_h71_d4.json`): word `[4]`, ambient `9360`, `18` live states. -/
def h71d4live : ℕ → Bool := fun s => [0, 1560, 2304, 2310, 3872, 3896, 4616, 4617, 4622, 4623, 4736, 4737, 4742, 4743, 7049, 7055, 7775, 9359].contains s

def h71d4rho : ℕ → ℕ := fun s =>
  (([(0, 6), (1560, 3), (2310, 2), (3872, 1), (3896, 4), (4616, 5), (7055, 2), (7775, 1), (9359, 3)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d4omega : ℕ → ℕ := fun s =>
  (([(720, 2), (726, 1), (744, 1), (750, 1), (840, 1), (846, 1), (864, 1), (870, 1), (1440, 2), (1446, 1), (1464, 1), (1470, 1), (1566, 1), (1584, 2), (1590, 1), (2160, 1), (2166, 1), (2184, 1), (2190, 1), (2280, 1), (2286, 1), (2312, 1), (2334, 1), (2336, 1), (2430, 1), (2432, 1), (2454, 1), (2456, 1), (3030, 1), (3032, 1), (3054, 1), (3056, 1), (3150, 1), (3152, 2), (3174, 1), (3176, 1), (3750, 1), (3752, 1), (3774, 1), (3776, 1), (3870, 1), (3894, 1), (3897, 1), (3902, 1), (3903, 1), (4016, 1), (4017, 1), (4022, 1), (4023, 1), (5336, 1), (5337, 1), (5342, 1), (5343, 1), (5456, 1), (5457, 1), (5462, 1), (5463, 1), (7073, 1), (7079, 1), (7169, 1), (7175, 1), (7193, 1), (7199, 1), (7769, 1), (7793, 1), (7799, 1), (7889, 1), (7895, 1), (7913, 1), (7919, 1), (8489, 1), (8495, 1), (8513, 1), (8519, 1), (8609, 1), (8615, 1), (8633, 1), (8639, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d4forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (2304, (1, 7049)), (2310, (1, 7055)), (4616, (3, 4616)), (4617, (3, 4617)), (4622, (3, 4622)), (4623, (3, 4623)), (4736, (3, 4736)), (4737, (3, 4737)), (4742, (3, 4742)), (4743, (3, 4743)), (7049, (5, 2304)), (7055, (5, 2310)), (9359, (6, 9359))] : List (ℕ × ℕ × ℕ)).lookup s

theorem h71d4_c0 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 h71d4live h71d4rho h71d4omega h71d4forced 0 1560 = true := by decide +kernel

theorem h71d4_c1 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 h71d4live h71d4rho h71d4omega h71d4forced 1560 1560 = true := by decide +kernel

theorem h71d4_c2 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 h71d4live h71d4rho h71d4omega h71d4forced 3120 1560 = true := by decide +kernel

theorem h71d4_c3 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 h71d4live h71d4rho h71d4omega h71d4forced 4680 1560 = true := by decide +kernel

theorem h71d4_c4 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 h71d4live h71d4rho h71d4omega h71d4forced 6240 1560 = true := by decide +kernel

theorem h71d4_c5 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 h71d4live h71d4rho h71d4omega h71d4forced 7800 1560 = true := by decide +kernel

theorem h71d4_forced : checkForcedA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 9360 h71d4live h71d4forced = true := by decide +kernel

theorem h71d4_cert : checkCertA (fun σ s' => gfamPred 7 (h71Chans 4) (σ % 7) (σ / 7) s')
    7 9360 h71d4live h71d4rho h71d4omega h71d4forced = true := by
  refine checkCertA_of_edgesOn ?_ h71d4_forced
  have h := checkEdgesOnA_of_chunks (c := 1560) 6 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h71d4_c0, h71d4_c1, h71d4_c2, h71d4_c3, h71d4_c4, h71d4_c5])
  exact h

/-- Certificate `h71_d5` (`experiments/certs/adder_cert_h71_d5.json`): word `[5]`, ambient `9360`, `21` live states. -/
def h71d5live : ℕ → Bool := fun s => [0, 720, 1560, 2304, 3030, 3032, 3150, 3152, 4616, 4617, 4622, 4623, 4736, 4737, 4742, 4743, 6207, 6209, 6327, 6329, 9359].contains s

def h71d5rho : ℕ → ℕ := fun s =>
  (([(0, 5), (720, 2), (1560, 3), (2304, 2), (3030, 4), (4616, 1), (6207, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d5omega : ℕ → ℕ := fun s =>
  (([(726, 1), (744, 1), (750, 1), (840, 1), (846, 1), (864, 1), (870, 1), (1440, 2), (1446, 1), (1464, 1), (1470, 1), (1566, 1), (1584, 3), (1590, 1), (2160, 1), (2166, 1), (2184, 1), (2190, 1), (2280, 1), (2286, 1), (2310, 2), (2312, 1), (2334, 1), (2336, 1), (2430, 1), (2432, 1), (2454, 1), (2456, 1), (3054, 1), (3056, 1), (3174, 1), (3176, 1), (3750, 1), (3752, 1), (3774, 1), (3776, 1), (3870, 1), (3872, 1), (3894, 1), (3896, 2), (3897, 1), (3902, 1), (3903, 1), (4016, 1), (4017, 1), (4022, 1), (4023, 1), (5336, 1), (5337, 1), (5342, 1), (5343, 1), (5456, 1), (5457, 1), (5462, 1), (5463, 1), (5465, 1), (5487, 2), (5489, 1), (5583, 1), (5585, 1), (5607, 1), (5609, 1), (6183, 1), (6185, 1), (6303, 1), (6305, 1), (6903, 1), (6905, 1), (6927, 1), (6929, 1), (7023, 1), (7025, 1), (7047, 1), (7049, 1), (8639, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d5forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (3030, (2, 3030)), (3032, (2, 3032)), (3150, (2, 3150)), (3152, (2, 3152)), (4616, (3, 4616)), (4617, (3, 4617)), (4622, (3, 4622)), (4623, (3, 4623)), (4736, (3, 4736)), (4737, (3, 4737)), (4742, (3, 4742)), (4743, (3, 4743)), (6207, (4, 6207)), (6209, (4, 6209)), (6327, (4, 6327)), (6329, (4, 6329)), (9359, (6, 9359))] : List (ℕ × ℕ × ℕ)).lookup s

theorem h71d5_c0 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 h71d5live h71d5rho h71d5omega h71d5forced 0 1560 = true := by decide +kernel

theorem h71d5_c1 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 h71d5live h71d5rho h71d5omega h71d5forced 1560 1560 = true := by decide +kernel

theorem h71d5_c2 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 h71d5live h71d5rho h71d5omega h71d5forced 3120 1560 = true := by decide +kernel

theorem h71d5_c3 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 h71d5live h71d5rho h71d5omega h71d5forced 4680 1560 = true := by decide +kernel

theorem h71d5_c4 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 h71d5live h71d5rho h71d5omega h71d5forced 6240 1560 = true := by decide +kernel

theorem h71d5_c5 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 h71d5live h71d5rho h71d5omega h71d5forced 7800 1560 = true := by decide +kernel

theorem h71d5_forced : checkForcedA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 9360 h71d5live h71d5forced = true := by decide +kernel

theorem h71d5_cert : checkCertA (fun σ s' => gfamPred 7 (h71Chans 5) (σ % 7) (σ / 7) s')
    7 9360 h71d5live h71d5rho h71d5omega h71d5forced = true := by
  refine checkCertA_of_edgesOn ?_ h71d5_forced
  have h := checkEdgesOnA_of_chunks (c := 1560) 6 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h71d5_c0, h71d5_c1, h71d5_c2, h71d5_c3, h71d5_c4, h71d5_c5])
  exact h

/-- Certificate `h71_d6` (`experiments/certs/adder_cert_h71_d6.json`): word `[6]`, ambient `9360`, `14` live states. -/
def h71d6live : ℕ → Bool := fun s => [0, 720, 1560, 1584, 2310, 3152, 3896, 4743, 5463, 5487, 6329, 7055, 7799, 7919].contains s

def h71d6rho : ℕ → ℕ := fun s =>
  (([(0, 6), (720, 4), (1584, 1), (2310, 2), (3152, 5), (3896, 1), (4743, 4), (5463, 2), (5487, 1), (6329, 3), (7055, 2), (7799, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d6omega : ℕ → ℕ := fun s =>
  (([(1566, 1), (1590, 1), (2280, 1), (2286, 1), (2304, 1), (2312, 1), (2336, 1), (2432, 1), (2456, 1), (3032, 1), (3056, 1), (3176, 1), (3752, 1), (3776, 1), (3872, 1), (3897, 1), (3903, 1), (4017, 1), (4023, 1), (4617, 1), (4623, 1), (4737, 1), (5337, 1), (5343, 1), (5457, 1), (5489, 1), (5607, 1), (5609, 1), (6207, 1), (6209, 1), (6327, 1), (6927, 1), (6929, 1), (7047, 1), (7049, 2), (7079, 1), (7175, 1), (7199, 1), (7775, 2), (7895, 1), (8495, 1), (8519, 1), (8615, 1), (8639, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def h71d6forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (1560, (1, 1560)), (1584, (1, 3896)), (2310, (1, 7055)), (3152, (2, 3152)), (3896, (2, 7799)), (4743, (3, 4743)), (5487, (4, 1584)), (6329, (4, 6329)), (7055, (5, 2310)), (7799, (5, 5487)), (7919, (5, 7919))] : List (ℕ × ℕ × ℕ)).lookup s

theorem h71d6_c0 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 h71d6live h71d6rho h71d6omega h71d6forced 0 1560 = true := by decide +kernel

theorem h71d6_c1 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 h71d6live h71d6rho h71d6omega h71d6forced 1560 1560 = true := by decide +kernel

theorem h71d6_c2 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 h71d6live h71d6rho h71d6omega h71d6forced 3120 1560 = true := by decide +kernel

theorem h71d6_c3 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 h71d6live h71d6rho h71d6omega h71d6forced 4680 1560 = true := by decide +kernel

theorem h71d6_c4 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 h71d6live h71d6rho h71d6omega h71d6forced 6240 1560 = true := by decide +kernel

theorem h71d6_c5 : checkEdgesOnA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 h71d6live h71d6rho h71d6omega h71d6forced 7800 1560 = true := by decide +kernel

theorem h71d6_forced : checkForcedA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 9360 h71d6live h71d6forced = true := by decide +kernel

theorem h71d6_cert : checkCertA (fun σ s' => gfamPred 7 (h71Chans 6) (σ % 7) (σ / 7) s')
    7 9360 h71d6live h71d6rho h71d6omega h71d6forced = true := by
  refine checkCertA_of_edgesOn ?_ h71d6_forced
  have h := checkEdgesOnA_of_chunks (c := 1560) 6 (by
    intro j hj lo hlo
    interval_cases j <;> simp only [Nat.reduceMul, Nat.zero_mul, Nat.one_mul] at hlo <;> subst hlo
    exacts [h71d6_c0, h71d6_c1, h71d6_c2, h71d6_c3, h71d6_c4, h71d6_c5])
  exact h

/-- **`S(7,1) ≤ 7`.**  The seven multipliers `{1, 2, 3, 4, 5, 6, 13}` hit every
base-7 digit.  The initial segments `{1,…,6}` and `{1,…,8}` fail
(`not_hitting_7_1_six`, `not_hitting_7_1_eight`), so again the witness is not an
initial segment. -/
theorem hitting_7_1_seven : Literature.IsHittingSet 7 1 {1, 2, 3, 4, 5, 6, 13} := by
  intro α hα w hw hd
  obtain ⟨d, rfl⟩ : ∃ d, w = [d] := by
    rcases w with _ | ⟨d, _ | ⟨e, t⟩⟩ <;> simp at hw
    exact ⟨d, rfl⟩
  have hd7 : d < 7 := hd d (by simp)
  have key : ∃ ch ∈ h71Chans d, ∀ N, ∃ n, N ≤ n ∧ OccursAt 7 (ch.a * α) ch.word n := by
    interval_cases d
    · exact signed_engine_g_single 7 (by norm_num) (h71Chans 0) rfl h71d0_cert α hα
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 7 (by norm_num) (h71Chans 1) rfl h71d1_cert α hα
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 7 (by norm_num) (h71Chans 2) rfl h71d2_cert α hα
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 7 (by norm_num) (h71Chans 3) rfl h71d3_cert α hα
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 7 (by norm_num) (h71Chans 4) rfl h71d4_cert α hα
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 7 (by norm_num) (h71Chans 5) rfl h71d5_cert α hα
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 7 (by norm_num) (h71Chans 6) rfl h71d6_cert α hα
        (by decide) (by decide) (by decide)
  obtain ⟨ch, hch, hio⟩ := key
  fin_cases hch
  · exact ⟨1, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨2, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨3, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨4, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨5, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨6, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨13, by simp, by norm_num, by simpa using hio⟩

/-! ## The base-7 lower wiring -/

/-- The initial segment `{1,…,8}` is **not** a hitting set at base 7, block
length 1: the Mahler witness of `mahler_lower_bound_base7` has digit `1`
occurring only finitely often in `m·α` for every `1 ≤ m ≤ 8`. -/
theorem not_hitting_7_1_eight : ¬ Literature.IsHittingSet 7 1 {1, 2, 3, 4, 5, 6, 7, 8} := by
  intro h
  obtain ⟨α, hα, hbad⟩ := Mahler.mahler_lower_bound_base7
  obtain ⟨m, hm, hm1, hio⟩ := h α hα [1] rfl (by simp)
  have hm8 : m ≤ 8 := by simp at hm; omega
  obtain ⟨N, hN⟩ := hbad m hm1 hm8
  obtain ⟨n, hn, hocc⟩ := hio N
  exact hN n hn hocc

/-- Hence `{1,…,6}` is not a hitting set either: with `hitting_7_1_seven` this
shows the size-`7` witness `{1, 2, 3, 4, 5, 6, 13}` is not an initial segment. -/
theorem not_hitting_7_1_six : ¬ Literature.IsHittingSet 7 1 {1, 2, 3, 4, 5, 6} := fun h =>
  not_hitting_7_1_eight (h.mono (by intro x hx; simp at hx ⊢; omega))

end NormalNumbers.Adder
