/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRuns

/-!
# The lattice-point reformulation of the run crux (R1)

Companion to `docs/alien-review-2026-08-29.md` (transmission 2, move R1) and
`docs/lit-sweep-2026-08-29.md`.  The Bailey–Crandall surrogate is an **exact
rational**: `x_n = A_n / L_n` with `L_n = lcm(1..n)`.  A run of `k` equal
binary digits of `ln 2` at position `n` therefore pins the integer numerator
`A_n` into an explicit real interval of width `L_n / 2^k` — fewer than one
integer as soon as `2^k > L_n` (`k ≈ log₂ L_n ≈ n·log₂ e` by PNT, `≤ 2n` by
Nair's elementary `lcm(1..n) ≤ 4^n`).  The transmission-2 hope was that this
pigeonhole threshold undercuts the measure-route run threshold
`(μ−1)n ≈ 2.57n` (Marcovecchio 2009) at a *cheaper* hypothesis; the costume
verdict below is that it does not — the widths differ but the avoidance
hypothesis is the separation statement itself, re-coordinatized.

What this file proves, all unconditional:

* `lnTwoNum_spec`: the surrogate's exact numerator over `lcmRange n`
  (denominator-clearing identity);
* `lnTwoOrbit_eq_res`: `x_n = lnTwoRes n / lcmRange n` with
  `lnTwoRes n = lnTwoNum n % lcmRange n`;
* **Translation edges** `zeroRun_lattice_window` / `oneRun_lattice_window`:
  a long run places `lnTwoRes n` in an explicit window of width
  `lcmRange n / 2^k` anchored at `latticeCenter n = L_n·(1 − τ_n)`;
* **Unique-candidate lemmas** `zeroRun_res_eq_ceil` / `oneRun_res_eq_ceil_sub_one`:
  when `L_n < 2^k` the window holds at most one integer, and the run forces
  `lnTwoRes n` to equal that explicit candidate;
* the frozen node `LnTwoLatticeAvoid` (the **coincidence-failure
  hypothesis**) and the wiring `run_le_of_latticeAvoid`: avoidance of the
  per-`n` window caps every run at `g n`.

🚨 **Costume verdict (proved below, same session — signpost rule).**  The
window's *position* depends on `τ_n`, i.e. on `ln 2` itself, and that
dependence collapses the node back onto `‖2ⁿ·ln 2‖` exactly:
`latticeAvoid_of_dyadicSep` / `dyadicSep_of_latticeAvoid` show
**`LnTwoLatticeAvoid g` ⟺ dyadic separation at rate `2^(−g n)`** — a
re-coordinatization of `LnTwoDyadicSep`, NOT a new rung.  At `g n = 2n+2`
the node is `LnTwoExpSep β ≈ 2`, i.e. `μ(ln 2) ≤ 3` territory — *stronger*
than the citable Marcovecchio hypothesis.  The transmission-2 napkin
("pigeonhole threshold 1.44n beats measure threshold 2.57n") correctly
prices the *window width* but wrongly implies the avoidance hypothesis is
cheaper than a measure hypothesis; they are the same statement in two
coordinate systems.  This also settles the blueprint §5.3 annotation: the
sliver/ride family carries Diophantine content, full stop.

**What survives** (the honest value of the lattice coordinates):

1. the **certificate structure** — a run event is a single explicit integer
   identity `lnTwoRes n = ⌈latticeCenter n⌉` per position, so refuting a
   run is one integer inequality;
2. the **congruence attack surface** — `lnTwoNum` is an explicit integer
   sequence, and window avoidance for structured `n` (e.g. `n = p−1`,
   where `A_{p−1} ≡ unit·q_p(2) (mod p)`, the Fermat-quotient bridge of the
   lit-sweep doc) is now a statement congruence arithmetic can touch, which
   the `‖2ⁿ·ln 2‖` coordinates never exposed.

Node discipline: `LnTwoLatticeAvoid` is a named `Prop` (working
hypothesis), never an axiom.  Its probe is `experiments/lntwo_runs.py` via
the costume equivalence (record runs track `log₂ n`, so the empirical
margin over the `g n = 2n+2` window is astronomically safe).
-/

namespace NormalNumbers

open Finset

/-! ### The denominator `lcm(1..n)` and the exact numerator -/

/-- `lcm(1, …, n)` — the denominator scale of the Bailey–Crandall surrogate. -/
def lcmRange (n : ℕ) : ℕ := (Finset.range n).lcm (· + 1)

theorem lcmRange_pos (n : ℕ) : 0 < lcmRange n := by
  rcases Nat.eq_zero_or_pos (lcmRange n) with h | h
  · exfalso
    rw [lcmRange, Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, _, hx⟩ := h
    omega
  · exact h

theorem succ_dvd_lcmRange {k n : ℕ} (h : k < n) : (k + 1) ∣ lcmRange n :=
  Finset.dvd_lcm (Finset.mem_range.mpr h)

/-- The exact integer numerator of `2ⁿ·(Σ_{k<n} 1/((k+1)·2^(k+1)))` over
`lcmRange n`: `A_n = Σ_{k<n} (L_n/(k+1))·2^(n−k−1)`. -/
def lnTwoNum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (lcmRange n / (k + 1)) * 2 ^ (n - k - 1)

/-- **Denominator clearing**: `A_n / L_n = 2ⁿ·(partial sum)` exactly, in `ℝ`.
The surrogate orbit is an exact rational with denominator `lcm(1..n)`. -/
theorem lnTwoNum_spec (n : ℕ) :
    ((lnTwoNum n : ℝ)) = lcmRange n * (2 ^ n * lnTwoPartial n) := by
  rw [lnTwoNum, lnTwoPartial, Finset.mul_sum, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k < n := Finset.mem_range.mp hk
  have hdvd : (k + 1) ∣ lcmRange n := succ_dvd_lcmRange hkn
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [Nat.cast_div hdvd (by exact_mod_cast hk1)]
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - k - 1) * 2 ^ (k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  rw [hpow]
  field_simp

/-- The residue numerator: `x_n = lnTwoRes n / lcmRange n` with
`0 ≤ lnTwoRes n < lcmRange n`. -/
def lnTwoRes (n : ℕ) : ℕ := lnTwoNum n % lcmRange n

theorem lnTwoRes_lt (n : ℕ) : lnTwoRes n < lcmRange n :=
  Nat.mod_lt _ (lcmRange_pos n)

/-- **The surrogate is an explicit rational**:
`x_n = lnTwoRes n / lcmRange n`. -/
theorem lnTwoOrbit_eq_res (n : ℕ) :
    lnTwoOrbit n = (lnTwoRes n : ℝ) / lcmRange n := by
  have hL : ((lcmRange n : ℝ)) ≠ 0 := by
    exact_mod_cast (lcmRange_pos n).ne'
  have hval : (2 : ℝ) ^ n * lnTwoPartial n = (lnTwoNum n : ℝ) / lcmRange n := by
    rw [lnTwoNum_spec]
    field_simp
  rw [lnTwoOrbit_eq_fract, hval, Int.fract_div_natCast_eq_div_natCast_mod]
  rfl

/-! ### The translation edges: a run pins the numerator to a lattice window -/

/-- The window center: `L_n·(1 − τ_n)`, where `τ_n = 2ⁿ·lnTwoTail n` is the
scaled series tail.  The center depends on `ln 2` itself — this is where the
Diophantine content of the run question lives. -/
noncomputable def latticeCenter (n : ℕ) : ℝ :=
  lcmRange n * (1 - 2 ^ n * lnTwoTail n)

/-- **Zero-run translation edge**: a run of `k` zeros at position `n` with
`2ᵏ > 2(n+1)` places the integer `lnTwoRes n` in the explicit real window
`[latticeCenter n, latticeCenter n + L_n/2ᵏ)` of width `L_n/2ᵏ`. -/
theorem zeroRun_lattice_window {n k : ℕ}
    (hk : 2 * ((n : ℝ) + 1) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n) :
    (lnTwoRes n : ℝ) ∈ Set.Ico (latticeCenter n) (latticeCenter n + lcmRange n / 2 ^ k) := by
  rw [occursAt_replicate_zero_iff, orbit_log_two_eq] at h
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hτge : 1 / (2 * ((n : ℝ) + 1)) ≤ τ := lnTwoTail_ge n
  have hx01 := lnTwoOrbit_mem_Ico n
  have hL0 : (0 : ℝ) < lcmRange n := by exact_mod_cast lcmRange_pos n
  have hxres : x = (lnTwoRes n : ℝ) / lcmRange n := lnTwoOrbit_eq_res n
  have hwin : 1 - τ ≤ x ∧ x < 1 - τ + 1 / 2 ^ k := by
    rcases lt_or_ge (x + τ) 1 with hlt | hge
    · exfalso
      rw [Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩] at h
      have hsmall : (1 : ℝ) / 2 ^ k < 1 / (2 * ((n : ℝ) + 1)) :=
        one_div_lt_one_div_of_lt (by positivity) hk
      linarith [h.2, hx01.1]
    · have hτ1 : τ ≤ 1 := by
        have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
      have hfr : Int.fract (x + τ) = x + τ - 1 := by
        have h2 : x + τ - 1 + ((1 : ℤ) : ℝ) = x + τ := by push_cast; ring
        rw [← h2, Int.fract_add_intCast,
          Int.fract_eq_self.mpr ⟨by linarith, by linarith [hx01.2]⟩]
        push_cast
        ring
      rw [hfr] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
  constructor
  · rw [latticeCenter, ← hτ_def]
    calc (lcmRange n : ℝ) * (1 - τ) ≤ lcmRange n * x :=
          mul_le_mul_of_nonneg_left hwin.1 hL0.le
    _ = lnTwoRes n := by rw [hxres]; field_simp
  · rw [latticeCenter, ← hτ_def]
    calc (lnTwoRes n : ℝ) = lcmRange n * x := by rw [hxres]; field_simp
    _ < lcmRange n * (1 - τ + 1 / 2 ^ k) :=
          mul_lt_mul_of_pos_left hwin.2 hL0
    _ = lcmRange n * (1 - τ) + lcmRange n / 2 ^ k := by ring

/-- **One-run translation edge**: for `n ≥ 1`, a run of `k` ones at position
`n` with `2ᵏ > 2(n+1)` places `lnTwoRes n` in the mirror window
`[latticeCenter n − L_n/2ᵏ, latticeCenter n)`. -/
theorem oneRun_lattice_window {n k : ℕ} (hn : 1 ≤ n)
    (hk : 2 * ((n : ℝ) + 1) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    (lnTwoRes n : ℝ) ∈ Set.Ico (latticeCenter n - lcmRange n / 2 ^ k) (latticeCenter n) := by
  rw [occursAt_replicate_one_iff, orbit_log_two_eq] at h
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hτge : 1 / (2 * ((n : ℝ) + 1)) ≤ τ := lnTwoTail_ge n
  have hx01 := lnTwoOrbit_mem_Ico n
  have hL0 : (0 : ℝ) < lcmRange n := by exact_mod_cast lcmRange_pos n
  have hxres : x = (lnTwoRes n : ℝ) / lcmRange n := lnTwoOrbit_eq_res n
  have hn1 : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hq : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn1
  have hsmall : (1 : ℝ) / 2 ^ k < 1 / (2 * ((n : ℝ) + 1)) :=
    one_div_lt_one_div_of_lt (by positivity) hk
  have hq2 : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hwin : 1 - τ - 1 / 2 ^ k ≤ x ∧ x < 1 - τ := by
    rcases lt_or_ge (x + τ) 1 with hlt | hge
    · rw [Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · exfalso
      have hfr : Int.fract (x + τ) = x + τ - 1 := by
        have hlt2 : x + τ - 1 < 1 := by linarith [hx01.2, hτle, hq]
        have h2 : x + τ - 1 + ((1 : ℤ) : ℝ) = x + τ := by push_cast; ring
        rw [← h2, Int.fract_add_intCast,
          Int.fract_eq_self.mpr ⟨by linarith, hlt2⟩]
        push_cast
        ring
      rw [hfr] at h
      have h1 : 1 - 1 / 2 ^ k ≤ x + τ - 1 := h.1
      have hub : x + τ - 1 ≤ 1 / ((n : ℝ) + 1) := by linarith [hx01.2]
      linarith
  constructor
  · rw [latticeCenter, ← hτ_def]
    calc (lcmRange n : ℝ) * (1 - τ) - lcmRange n / 2 ^ k
        = lcmRange n * (1 - τ - 1 / 2 ^ k) := by ring
    _ ≤ lcmRange n * x := mul_le_mul_of_nonneg_left hwin.1 hL0.le
    _ = lnTwoRes n := by rw [hxres]; field_simp
  · rw [latticeCenter, ← hτ_def]
    calc (lnTwoRes n : ℝ) = lcmRange n * x := by rw [hxres]; field_simp
    _ < lcmRange n * (1 - τ) := mul_lt_mul_of_pos_left hwin.2 hL0

/-! ### Unique-candidate lemmas: below one integer per window -/

/-- Any integer in a half-open window `[c, c + w)` with `w ≤ 1` is `⌈c⌉`. -/
theorem int_eq_ceil_of_mem_Ico {c w : ℝ} (hw : w ≤ 1) {m : ℤ}
    (hm : (m : ℝ) ∈ Set.Ico c (c + w)) : m = ⌈c⌉ := by
  have h1 : ⌈c⌉ ≤ m := Int.ceil_le.mpr hm.1
  have h2 : (m : ℝ) < c + 1 := lt_of_lt_of_le hm.2 (by linarith)
  have h3 : (m : ℝ) < (⌈c⌉ : ℝ) + 1 := lt_of_lt_of_le h2 (by
    have := Int.le_ceil c
    linarith)
  have h4 : m < ⌈c⌉ + 1 := by exact_mod_cast h3
  omega

/-- Any integer in a half-open window `[c − w, c)` with `w ≤ 1` is `⌈c⌉ − 1`. -/
theorem int_eq_ceil_sub_one_of_mem_Ico {c w : ℝ} (hw : w ≤ 1) {m : ℤ}
    (hm : (m : ℝ) ∈ Set.Ico (c - w) c) : m = ⌈c⌉ - 1 := by
  have h1 : m < ⌈c⌉ := Int.lt_ceil.mpr hm.2
  have h2 : (⌈c⌉ : ℝ) < c + 1 := Int.ceil_lt_add_one c
  have h3 : ⌈c⌉ - 2 < m := by
    have : (⌈c⌉ : ℝ) - 2 < (m : ℝ) := by linarith [hm.1]
    exact_mod_cast this
  omega

/-- **Zero-run unique candidate**: with the pigeonhole threshold `L_n < 2ᵏ`
in force, a run of `k` zeros at position `n` forces the numerator to equal
the single explicit integer `⌈latticeCenter n⌉`.  The event "`lnTwoRes n`
hits that integer" is the per-`n` coincidence the frozen node below rules
out. -/
theorem zeroRun_res_eq_ceil {n k : ℕ}
    (hk : 2 * ((n : ℝ) + 1) < 2 ^ k) (hL : (lcmRange n : ℝ) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n) :
    (lnTwoRes n : ℤ) = ⌈latticeCenter n⌉ := by
  have hmem := zeroRun_lattice_window hk h
  have hw : (lcmRange n : ℝ) / 2 ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hL.le
  exact_mod_cast int_eq_ceil_of_mem_Ico hw (by exact_mod_cast hmem)

/-- **One-run unique candidate**: mirror statement, candidate
`⌈latticeCenter n⌉ − 1`. -/
theorem oneRun_res_eq_ceil_sub_one {n k : ℕ} (hn : 1 ≤ n)
    (hk : 2 * ((n : ℝ) + 1) < 2 ^ k) (hL : (lcmRange n : ℝ) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    (lnTwoRes n : ℤ) = ⌈latticeCenter n⌉ - 1 := by
  have hmem := oneRun_lattice_window hn hk h
  have hw : (lcmRange n : ℝ) / 2 ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hL.le
  exact_mod_cast int_eq_ceil_sub_one_of_mem_Ico hw (by exact_mod_cast hmem)

/-! ### The frozen node and its run-bound edge -/

/-- **Node (frozen, OPEN): lattice-window avoidance — the coincidence-failure
hypothesis.**  For `n ≥ N₀` the numerator `lnTwoRes n` misses the symmetric
window of width `2·L_n/2^(g n)` around `latticeCenter n`.

🚨 Read with the costume theorems below: this node is **equivalent** to
dyadic separation at rate `2^(−g n)` (`latticeAvoid_of_dyadicSep` /
`dyadicSep_of_latticeAvoid`) — at `g n = 2n+2` it is `μ(ln 2) ≤ 3`
territory, beyond the citable Marcovecchio bound.  The window contains
fewer than one integer on average (`L_n ≤ 4ⁿ`, Nair; `≈ eⁿ` by PNT), which
is why the random model favors it, but plausibility is not weakness.
Provenance: alien transmission 2 (R1), 2026-08-29, costume-corrected the
same day.  Odds the `g n = 2n+2` instance holds for some `N₀`: high
(random model; `experiments/lntwo_runs.py` records track `log₂ n`); odds
it is provable unconditionally: very low (it implies an irrationality
measure below the state of the art). -/
def LnTwoLatticeAvoid (g : ℕ → ℕ) (N₀ : ℕ) : Prop :=
  ∀ n, N₀ ≤ n →
    (lnTwoRes n : ℝ) ∉ Set.Ico (latticeCenter n - lcmRange n / 2 ^ g n)
      (latticeCenter n + lcmRange n / 2 ^ g n)

/-- **Wiring**: lattice-window avoidance caps every run — a run of `k`
zeros or ones at position `n ≥ max N₀ 1` with the (mild) side condition
`2^(g n) > 2(n+1)` forces `k < g n`.  With `g n = 2n+2` this is the
conditional run bound `k ≤ 2n+1` — but note (costume theorems) the
hypothesis is then `ExpSep β ≈ 2`, so this wiring adds no strength over
`run_le_of_expSep`; its value is the lattice rendering of the same edge. -/
theorem run_le_of_latticeAvoid {g : ℕ → ℕ} {N₀ : ℕ}
    (havoid : LnTwoLatticeAvoid g N₀) {n k : ℕ} (hn : N₀ ≤ n) (hn1 : 1 ≤ n)
    (hg : 2 * ((n : ℝ) + 1) < 2 ^ g n)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n ∨
         OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    k < g n := by
  rcases Nat.lt_or_ge k (g n) with hlt | hcon
  · exact hlt
  exfalso
  have hL0 : (0 : ℝ) < lcmRange n := by exact_mod_cast lcmRange_pos n
  have hpow : (2 : ℝ) ^ g n ≤ 2 ^ k := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcon
  have hk : 2 * ((n : ℝ) + 1) < 2 ^ k := lt_of_lt_of_le hg hpow
  have hwsub : (lcmRange n : ℝ) / 2 ^ k ≤ lcmRange n / 2 ^ g n :=
    div_le_div_of_nonneg_left hL0.le (by positivity) hpow
  have hwpos : (0 : ℝ) < lcmRange n / 2 ^ g n := by positivity
  refine havoid n hn ?_
  rcases h with h | h
  · have hmem := zeroRun_lattice_window hk h
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  · have hmem := oneRun_lattice_window hn1 hk h
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-! ### The costume theorems: the node is dyadic separation in lattice coordinates

Proved the same session the node was frozen (signpost rule).  The two
directions below show `LnTwoLatticeAvoid g` is `LnTwoDyadicSep` at rate
`2^(−g n)` **re-coordinatized** — the window's position depends on `ln 2`
through `τ_n`, and the dependence collapses the lattice statement back onto
`‖2ⁿ·ln 2‖` exactly.  At `g n = 2n + O(1)` the node is therefore an
`LnTwoExpSep β ≈ 2` statement (`μ(ln 2) ≤ 3` territory) — STRONGER than the
citable Marcovecchio hypothesis, not weaker.  What the lattice coordinates
genuinely add is the *certificate structure* (`zeroRun_res_eq_ceil`): the
run event is one explicit integer identity per `n`, an attack surface for
congruence arithmetic on `lnTwoNum` (Fermat-quotient bridge, lit-sweep doc)
that the `‖2ⁿ·ln 2‖` coordinates do not expose. -/

/-- Core identity: the numerator's distance to the window center is the
lattice-scaled distance of the perturbed surrogate to the wrap point. -/
theorem abs_res_sub_center (n : ℕ) :
    |(lnTwoRes n : ℝ) - latticeCenter n|
      = lcmRange n * |lnTwoOrbit n + 2 ^ n * lnTwoTail n - 1| := by
  have hL0 : (0 : ℝ) < lcmRange n := by exact_mod_cast lcmRange_pos n
  have hxres : lnTwoOrbit n = (lnTwoRes n : ℝ) / lcmRange n := lnTwoOrbit_eq_res n
  have hres : (lnTwoRes n : ℝ) = lcmRange n * lnTwoOrbit n := by
    rw [hxres]; field_simp
  have hdiff : (lnTwoRes n : ℝ) - latticeCenter n
      = lcmRange n * (lnTwoOrbit n + 2 ^ n * lnTwoTail n - 1) := by
    rw [hres, latticeCenter]; ring
  rw [hdiff, abs_mul, abs_of_pos hL0]

/-- `‖2ⁿ·ln 2‖` is bounded by the perturbed surrogate's distance to the
wrap point `1`. -/
theorem lnTwoNorm_le_abs (n : ℕ) :
    lnTwoNorm n ≤ |lnTwoOrbit n + 2 ^ n * lnTwoTail n - 1| := by
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hτ1 : τ ≤ 1 := by
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have hx01 := lnTwoOrbit_mem_Ico n
  have horb : orbit 2 (Real.log 2) n = Int.fract (x + τ) := orbit_log_two_eq n
  simp only [lnTwoNorm, horb]
  rcases lt_or_ge (x + τ) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩,
      abs_of_nonpos (by linarith : x + τ - 1 ≤ 0)]
    have := min_le_right (x + τ) (1 - (x + τ))
    linarith
  · have hfr : Int.fract (x + τ) = x + τ - 1 := by
      have h2 : x + τ - 1 + ((1 : ℤ) : ℝ) = x + τ := by push_cast; ring
      rw [← h2, Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith [hx01.2]⟩]
      push_cast
      ring
    rw [hfr, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + τ - 1)]
    exact min_le_left _ _

/-- **Costume theorem, direction 1**: strict dyadic separation at rate
`2^(−g n)` implies lattice-window avoidance — the node is no harder than a
separation bound. -/
theorem latticeAvoid_of_dyadicSep {g : ℕ → ℕ} {N₀ : ℕ}
    (h : ∀ n, N₀ ≤ n → 1 / 2 ^ g n < lnTwoNorm n) : LnTwoLatticeAvoid g N₀ := by
  intro n hn hmem
  have hL0 : (0 : ℝ) < lcmRange n := by exact_mod_cast lcmRange_pos n
  have habs : |(lnTwoRes n : ℝ) - latticeCenter n| ≤ lcmRange n / 2 ^ g n := by
    rcases hmem with ⟨h1, h2⟩
    rw [abs_le]
    constructor <;> linarith
  have hLw : (lcmRange n : ℝ) / 2 ^ g n = lcmRange n * (1 / 2 ^ g n) := by ring
  have h3 : (lcmRange n : ℝ) * |lnTwoOrbit n + 2 ^ n * lnTwoTail n - 1|
      ≤ lcmRange n * (1 / 2 ^ g n) := by
    rw [← abs_res_sub_center, ← hLw]
    exact habs
  have h4 : |lnTwoOrbit n + 2 ^ n * lnTwoTail n - 1| ≤ 1 / 2 ^ g n :=
    le_of_mul_le_mul_left h3 hL0
  linarith [h n hn, lnTwoNorm_le_abs n, h4]

/-- **Costume theorem, direction 2**: lattice-window avoidance yields the
dyadic separation bound back (for `n ≥ 1` under the standard side
condition).  Together with direction 1: **`LnTwoLatticeAvoid` is
`LnTwoDyadicSep` at rate `2^(−g n)` in lattice coordinates — a
re-coordinatization of the wall, not a new rung below it.**  This refutes,
at the kernel level, the transmission-2 reading of R1 as a hypothesis
weaker than the measure route: the `g n = 2n+2` instance is `μ(ln 2) ≤ 3`
territory, beyond Marcovecchio.  The reformulation's surviving value is the
certificate structure and the congruence attack surface on `lnTwoNum`. -/
theorem dyadicSep_of_latticeAvoid {g : ℕ → ℕ} {N₀ : ℕ}
    (havoid : LnTwoLatticeAvoid g N₀) {n : ℕ} (hn : N₀ ≤ n) (hn1 : 1 ≤ n)
    (hg : 2 * ((n : ℝ) + 1) < 2 ^ g n) :
    1 / 2 ^ g n ≤ lnTwoNorm n := by
  rcases le_or_gt (1 / 2 ^ g n) (lnTwoNorm n) with hok | hbad
  · exact hok
  exfalso
  have hL0 : (0 : ℝ) < lcmRange n := by exact_mod_cast lcmRange_pos n
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hτge : 1 / (2 * ((n : ℝ) + 1)) ≤ τ := lnTwoTail_ge n
  have hx01 := lnTwoOrbit_mem_Ico n
  have hn1' : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hτhalf : τ ≤ 1 / 2 := hτle.trans (one_div_le_one_div_of_le (by norm_num) hn1')
  have hw0small : (1 : ℝ) / 2 ^ g n < 1 / (2 * ((n : ℝ) + 1)) :=
    one_div_lt_one_div_of_lt (by positivity) hg
  have hq2 : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have horb : orbit 2 (Real.log 2) n = Int.fract (x + τ) := orbit_log_two_eq n
  have hnorm : min (Int.fract (x + τ)) (1 - Int.fract (x + τ)) < 1 / 2 ^ g n := by
    simpa [lnTwoNorm, horb] using hbad
  have hD : |x + τ - 1| < 1 / 2 ^ g n := by
    rcases min_lt_iff.mp hnorm with hlo | hhi
    · rcases lt_or_ge (x + τ) 1 with hlt | hge
      · exfalso
        rw [Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩] at hlo
        linarith [hx01.1]
      · have hfr : Int.fract (x + τ) = x + τ - 1 := by
          have h2 : x + τ - 1 + ((1 : ℤ) : ℝ) = x + τ := by push_cast; ring
          rw [← h2, Int.fract_add_intCast,
            Int.fract_eq_self.mpr ⟨by linarith, by linarith [hx01.2, hτhalf]⟩]
          push_cast
          ring
        rw [hfr] at hlo
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + τ - 1)]
        exact hlo
    · rcases lt_or_ge (x + τ) 1 with hlt | hge
      · rw [Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩] at hhi
        rw [abs_of_nonpos (by linarith : x + τ - 1 ≤ 0)]
        linarith
      · exfalso
        have hfr : Int.fract (x + τ) = x + τ - 1 := by
          have h2 : x + τ - 1 + ((1 : ℤ) : ℝ) = x + τ := by push_cast; ring
          rw [← h2, Int.fract_add_intCast,
            Int.fract_eq_self.mpr ⟨by linarith, by linarith [hx01.2, hτhalf]⟩]
          push_cast
          ring
        rw [hfr] at hhi
        linarith [hx01.2, hτhalf, hw0small, hq2]
  have habs : |(lnTwoRes n : ℝ) - latticeCenter n| < lcmRange n / 2 ^ g n := by
    rw [abs_res_sub_center, show (lcmRange n : ℝ) / 2 ^ g n
      = lcmRange n * (1 / 2 ^ g n) by ring]
    exact mul_lt_mul_of_pos_left hD hL0
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  exact havoid n hn ⟨by linarith, by linarith⟩

end NormalNumbers
