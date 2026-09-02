/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerMultiplier
import NormalNumbers.MahlerLowerBound

/-!
# The Mahler multiplier problem: the run branch is settled at `gᵏ` 🧮

`MahlerMultiplier.lean` proves the universal bound `M(g,k) ≤ g^(k+1)` and
`MahlerLowerBound*.lean` prove `M(g,k) ≥ gᵏ − 1` (all `g`) and
`M(g,k) ≥ t(gᵏ − 1)` (`g = t·c`, `c ≥ 2`).  For **prime** bases the two
sides were a factor `g` apart, and the open question was which side moves.

This file answers half of it with an elementary argument: **whenever the
expansion of `α` contains a run of `k` zeros (or of `k` digits `g − 1`)
immediately preceded by a digit coprime to `g`, some multiplier `m ≤ gᵏ`
already produces every `k`-block infinitely often.**

    `mahler_multiplier_of_zero_runs`  (prime `g`, `0ᵏ` occurs i.o. in `α`)
    `mahler_multiplier_of_pred_runs`  (prime `g`, `(g−1)ᵏ` occurs i.o. in `α`)

For prime `g` every *maximal* run qualifies (its predecessor digit is
nonzero, hence a unit mod `g`), so the hypothesis is just "`0ᵏ` occurs
infinitely often in `α`".  The classical Liouville witnesses
(`liouvilleNumber g`, giving `M ≥ gᵏ − 1`) live in exactly this branch, so
the run branch is now pinned to within one unit:

    gᵏ − 1  ≤  M_run(g,k)  ≤  gᵏ            (prime `g`).

## The argument

Let `x = orbit g α n = {gⁿ α}` and `Q = gᵏ`.  Then `Q x = A + ε` where
`A = ⌊Q x⌋` is the integer formed by the `k` digits right after position
`n`, and `ε = orbit g α (n + k)`.  A run of `k` zeros right after that
block means `0 < ε < 1/Q`; the digit just before the run is `A mod g`.  If
`A` is a unit mod `Q` (`g` prime and `A mod g ≠ 0`), choose `1 ≤ m < Q`
with `m A ≡ W (mod Q)`; then

    m x = (m A + m ε)/Q = integer + (W + m ε)/Q,   0 < m ε < 1,

so `{m x} ∈ [W/Q, (W+1)/Q)` — the block `W` occurs in `m·α` at position
`n` (`cell_hit_of_coprime`).  `W = 0` uses `m = Q` (`{Q x} = ε`).  The
`(g−1)`-run case is the reflection `x ↦ −x` (`cell_hit_of_coprime_neg`).
Passing from "a run occurs i.o." to "a *maximal* run occurs i.o., arbitrarily
late" is `exists_maximal_zero_run` (irrationality keeps every orbit point
positive, so runs cannot reach back to a fixed position).

## Consequence for the chapter (numerics, recorded in `PENDING_WORK.md`)

An exact adder-machine computation of `M(g,1)` (incremental trimmed
product over the channels `1..M`, every SCC entropy-checked) gives

    g      2  3  4  5   6  7   8   9  10  11  13  17  19   23
    M(g,1) 1  2  6  6  20  9  28  24  72  25  35  64  80  120

so `M(g,1)` for odd primes tracks `((g−1)/2)²` — it is `Θ(g²)`, *not*
`Θ(g)`: the `g^(k+1)` upper bound has the right order for prime bases too,
and it is the **lower** side that must move.  By this file's theorem the
witnesses achieving `Θ(g²)` are forced into the run-free branch (no `0ᵏ`,
no `(g−1)ᵏ`), where the orbit hops between rationals `p/q`, `q < g`, that
are Farey neighbours (e.g. `g = 23`: `10/11 = 0.(20)`, `11/12 = 0.(21 1)`,
`7/10 = 0.(16 2 6 20)`, approached from below), with the hop
`p/q → p''/q''` costing `M ≤ (g − q)·q''` — maximised near `q ≈ q'' ≈ g/2`.
-/

namespace NormalNumbers.Mahler

open scoped Nat

/-- The all-zero block has value `0`. -/
theorem blockNatVal_replicate_zero (g k : ℕ) :
    blockNatVal g (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp [blockNatVal]
  | succ k ih => rw [List.replicate_succ, blockNatVal_cons, ih]; simp

/-- `fract (g · fract y) = fract (g y)` for a natural `g`. -/
theorem fract_nat_mul_fract (g : ℕ) (y : ℝ) :
    Int.fract ((g : ℝ) * Int.fract y) = Int.fract ((g : ℝ) * y) := by
  have h : (g : ℝ) * Int.fract y = (g : ℝ) * y - ((g * ⌊y⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]

/-- Iterated orbit step: `orbit g α (n + j) = {gʲ · orbit g α n}`. -/
theorem orbit_add_pow (g : ℕ) (α : ℝ) (n j : ℕ) :
    orbit g α (n + j) = Int.fract ((g : ℝ) ^ j * orbit g α n) := by
  induction j with
  | zero => simp [orbit, Int.fract_fract]
  | succ j ih =>
      rw [← add_assoc, orbit_succ, ih, fract_nat_mul_fract, pow_succ]
      congr 1; ring

/-- **Cell hit from a unit block.**  If `Q x = A + ε` with `A` coprime to
`Q` and `0 < ε < 1/Q`, then every cell `[W/Q, (W+1)/Q)` of the `Q`-grid
contains `{m x}` for some `1 ≤ m ≤ Q`. -/
theorem cell_hit_of_coprime (Q : ℕ) (hQ : 1 ≤ Q) (x : ℝ) (A : ℤ) (ε : ℝ)
    (hx : (Q : ℝ) * x = A + ε) (hε0 : 0 < ε) (hε1 : ε < 1 / Q)
    (hcop : IsCoprime A (Q : ℤ)) (W : ℕ) (hW : W < Q) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ Q ∧
      Int.fract ((m : ℝ) * x) ∈ Set.Ico ((W : ℝ) / Q) (((W : ℝ) + 1) / Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) / Q ≤ 1 := by
    rw [div_le_one hQR]; exact_mod_cast hQ
  obtain ⟨r, hr0, hrQ, t, ht⟩ := exists_residue_mul A Q hQ hcop W
  by_cases hr : r = 0
  · -- `Q ∣ W` with `0 ≤ W < Q`, so `W = 0`; use `m = Q`
    subst hr
    have hWZ : (W : ℤ) < Q := by exact_mod_cast hW
    have h1 : (W : ℤ) = Q * (-t) := by linarith
    have hW0 : W = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · have : (Q : ℤ) * 1 ≤ (Q : ℤ) * (-t) := mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
      · subst h; simpa using h1
      · have : (Q : ℤ) * (-t) < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
        omega
    subst hW0
    refine ⟨Q, hQ, le_rfl, ?_⟩
    rw [fract_eq_of_eq_int_add A hx hε0.le (by linarith)]
    simp only [Nat.cast_zero, zero_div, zero_add, Set.mem_Ico]
    exact ⟨hε0.le, hε1⟩
  · have hr1 : 1 ≤ r := by omega
    refine ⟨r.toNat, by omega, by omega, ?_⟩
    have hrt : ((r.toNat : ℕ) : ℝ) = r := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
    have htR : (r : ℝ) * A - W = Q * t := by exact_mod_cast ht
    have hrR0 : (0 : ℝ) ≤ r := by exact_mod_cast hr0
    have hrRQ : (r : ℝ) < Q := by exact_mod_cast hrQ
    set s : ℝ := ((W : ℝ) + r * ε) / Q with hs
    have hQs : (Q : ℝ) * s = W + r * ε := by rw [hs]; field_simp
    have key : ((r.toNat : ℕ) : ℝ) * x = (t : ℝ) + s := by
      rw [hrt]
      apply mul_left_cancel₀ hQR.ne'
      linear_combination (r : ℝ) * hx + htR - hQs
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have hrε : (r : ℝ) * ε < 1 := by
      calc (r : ℝ) * ε ≤ Q * ε := mul_le_mul_of_nonneg_right hrRQ.le hε0.le
        _ < Q * (1 / Q) := mul_lt_mul_of_pos_left hε1 hQR
        _ = 1 := by field_simp
    have hW1 : (W : ℝ) + 1 ≤ Q := by exact_mod_cast hW
    have hs1 : s < 1 := by rw [hs, div_lt_one hQR]; linarith
    rw [fract_eq_of_eq_int_add t key hs0 hs1]
    constructor
    · rw [hs]; apply div_le_div_of_nonneg_right _ hQR.le
      nlinarith [mul_nonneg hrR0 hε0.le]
    · rw [hs]; apply div_lt_div_of_pos_right _ hQR; linarith

/-- **Cell hit from a unit block, mirrored.**  If `Q x = B − ε` with `B`
coprime to `Q`, `0 < ε < 1/Q`, and `x` irrational, then every cell of the
`Q`-grid contains `{m x}` for some `1 ≤ m ≤ Q`. -/
theorem cell_hit_of_coprime_neg (Q : ℕ) (hQ : 1 ≤ Q) (x : ℝ) (hx : Irrational x)
    (B : ℤ) (ε : ℝ) (hxB : (Q : ℝ) * x = B - ε) (hε0 : 0 < ε) (hε1 : ε < 1 / Q)
    (hcop : IsCoprime B (Q : ℤ)) (W : ℕ) (hW : W < Q) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ Q ∧
      Int.fract ((m : ℝ) * x) ∈ Set.Ico ((W : ℝ) / Q) (((W : ℝ) + 1) / Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨m, hm1, hmQ, hmem⟩ := cell_hit_of_coprime Q hQ (-x) (-B) ε
    (by push_cast; linarith) hε0 hε1 hcop.neg_left (Q - 1 - W) (by omega)
  refine ⟨m, hm1, hmQ, ?_⟩
  have hmx : Irrational ((m : ℝ) * x) := hx.natCast_mul (by omega)
  have hfne : Int.fract ((m : ℝ) * x) ≠ 0 := by
    intro h0
    rw [Int.fract, sub_eq_zero] at h0
    exact hmx.ne_int _ h0
  rw [show (m : ℝ) * -x = -((m : ℝ) * x) from by ring, Int.fract_neg hfne] at hmem
  have hcast : ((Q - 1 - W : ℕ) : ℝ) = (Q : ℝ) - 1 - W := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hmem
  obtain ⟨h1, h2⟩ := hmem
  have hlt : Int.fract ((m : ℝ) * x) ≠ ((W : ℝ) + 1) / Q := by
    intro heq
    have hrat : Irrational (Int.fract ((m : ℝ) * x)) := hmx.sub_intCast _
    apply hrat.ne_rat (((W : ℚ) + 1) / (Q : ℚ))
    rw [heq]; push_cast; ring
  have hA : ((Q : ℝ) - 1 - W) / Q = 1 - ((W : ℝ) + 1) / Q := by
    field_simp; ring
  have hB : ((Q : ℝ) - 1 - W + 1) / Q = 1 - (W : ℝ) / Q := by
    field_simp; ring
  rw [hA] at h1
  rw [hB] at h2
  exact ⟨by linarith, lt_of_le_of_ne (by linarith) hlt⟩

/-- Orbit points of an irrational are positive. -/
theorem orbit_pos (g : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α) (n : ℕ) :
    0 < orbit g α n := by
  rcases (orbit_mem_Ico g α n).1.lt_or_eq with h | h
  · exact h
  · exact absurd h.symm (orbit_irrational g hg α hα n).ne_zero

/-- **Orbit form, zero run.**  If the `k` digits after position `n + k` are
zero and the block `A = ⌊gᵏ · orbit n⌋` (the `k` digits after position `n`)
is coprime to `g`, then every `k`-block is hit at position `n` by some
`m ≤ gᵏ`. -/
theorem hit_of_zero_run (g k n : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (hcop : IsCoprime ⌊(g : ℝ) ^ k * orbit g α n⌋ (g : ℤ))
    (hrun : orbit g α (n + k) < 1 / (g : ℝ) ^ k) (W : ℕ) (hW : W < g ^ k) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ k ∧
      Int.fract ((m : ℝ) * orbit g α n) ∈
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
  have hQ : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  have hcast : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  have hx : ((g ^ k : ℕ) : ℝ) * orbit g α n
      = ⌊(g : ℝ) ^ k * orbit g α n⌋ + orbit g α (n + k) := by
    rw [hcast, orbit_add_pow]; exact (Int.floor_add_fract _).symm
  have hcop' : IsCoprime ⌊(g : ℝ) ^ k * orbit g α n⌋ ((g ^ k : ℕ) : ℤ) := by
    push_cast; exact hcop.pow_right
  obtain ⟨m, hm1, hmQ, hmem⟩ := cell_hit_of_coprime (g ^ k) hQ _ _ _ hx
    (orbit_pos g hg α hα (n + k)) (by rw [hcast]; exact hrun) hcop' W hW
  refine ⟨m, hm1, hmQ, ?_⟩
  rw [hcast] at hmem; exact hmem

/-- **Orbit form, `(g−1)` run.**  If the `k` digits after position `n + k`
are all `g − 1` and `A + 1` is coprime to `g` (`A = ⌊gᵏ · orbit n⌋`), then
every `k`-block is hit at position `n` by some `m ≤ gᵏ`. -/
theorem hit_of_pred_run (g k n : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (hcop : IsCoprime (⌊(g : ℝ) ^ k * orbit g α n⌋ + 1) (g : ℤ))
    (hrun : 1 - 1 / (g : ℝ) ^ k < orbit g α (n + k)) (W : ℕ) (hW : W < g ^ k) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ k ∧
      Int.fract ((m : ℝ) * orbit g α n) ∈
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
  have hQ : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  have hcast : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  have hx : ((g ^ k : ℕ) : ℝ) * orbit g α n
      = ((⌊(g : ℝ) ^ k * orbit g α n⌋ + 1 : ℤ) : ℝ) - (1 - orbit g α (n + k)) := by
    rw [hcast, orbit_add_pow]; push_cast
    linear_combination (Int.floor_add_fract ((g : ℝ) ^ k * orbit g α n)).symm
  have hcop' : IsCoprime (⌊(g : ℝ) ^ k * orbit g α n⌋ + 1) ((g ^ k : ℕ) : ℤ) := by
    push_cast; exact hcop.pow_right
  have h1 := (orbit_mem_Ico g α (n + k)).2
  obtain ⟨m, hm1, hmQ, hmem⟩ := cell_hit_of_coprime_neg (g ^ k) hQ _
    (orbit_irrational g hg α hα n) _ _ hx (by linarith) (by rw [hcast]; linarith) hcop' W hW
  refine ⟨m, hm1, hmQ, ?_⟩
  rw [hcast] at hmem; exact hmem

/-- The floor of `g · y` splits as `g ⌊y⌋ + ⌊g {y}⌋`. -/
theorem floor_nat_mul_eq (g : ℕ) (y : ℝ) :
    ⌊(g : ℝ) * y⌋ = g * ⌊y⌋ + ⌊(g : ℝ) * Int.fract y⌋ := by
  have h : (g : ℝ) * y = ((g * ⌊y⌋ : ℤ) : ℝ) + (g : ℝ) * Int.fract y := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.floor_intCast_add]

/-- The last base-`g` digit of the block `⌊gᵏ · orbit n⌋` is the digit at
position `n + k − 1`, namely `⌊g · orbit (n + k − 1)⌋`. -/
theorem floor_pow_orbit_emod (g k n : ℕ) (hg : 2 ≤ g) (α : ℝ) :
    ⌊(g : ℝ) ^ (k + 1) * orbit g α n⌋ % g = ⌊(g : ℝ) * orbit g α (n + k)⌋ := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  rw [orbit_add_pow, pow_succ, mul_comm ((g : ℝ) ^ k) (g : ℝ), mul_assoc, floor_nat_mul_eq]
  have h0 : 0 ≤ ⌊(g : ℝ) * Int.fract ((g : ℝ) ^ k * orbit g α n)⌋ :=
    Int.floor_nonneg.2 (by positivity)
  have h1 : ⌊(g : ℝ) * Int.fract ((g : ℝ) ^ k * orbit g α n)⌋ < g := by
    rw [Int.floor_lt]; push_cast
    calc (g : ℝ) * Int.fract ((g : ℝ) ^ k * orbit g α n) < g * 1 :=
          mul_lt_mul_of_pos_left (Int.fract_lt_one _) hgR
      _ = g := mul_one _
  rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

/-- **Maximal runs occur arbitrarily late.**  If `orbit g α p < g⁻ᵏ` for
infinitely many `p` (a run of `k` zeros starts at `p` i.o.), then for every
`N` there is such a `p ≥ N + k` whose preceding digit `⌊g · orbit (p − 1)⌋`
is nonzero. -/
theorem exists_maximal_zero_run (g k : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (hrun : ∀ N, ∃ p, N ≤ p ∧ orbit g α p < 1 / (g : ℝ) ^ k) (N : ℕ) :
    ∃ p, N + k + 1 ≤ p ∧ orbit g α p < 1 / (g : ℝ) ^ k ∧
      1 ≤ ⌊(g : ℝ) * orbit g α (p - 1)⌋ := by
  have hgR : (1 : ℝ) < g := by exact_mod_cast (by omega : 1 < g)
  have hg0 : (0 : ℝ) < g := by linarith
  have hinv1 : (1 : ℝ) / g < 1 := by rw [div_lt_one hg0]; exact hgR
  have hinv0 : (0 : ℝ) < 1 / g := by positivity
  set J := N + k with hJ
  -- every early orbit point stays above a fixed power of `1/g`
  have hpos : ∀ j, 0 < orbit g α j := orbit_pos g hg α hα
  choose i hi using fun j => exists_pow_lt_of_lt_one (hpos j) hinv1
  set I := (Finset.range (J + 1)).sup i with hI
  have hIj : ∀ j, j ≤ J → i j ≤ I := fun j hj =>
    Finset.le_sup (f := i) (Finset.mem_range.2 (by omega))
  obtain ⟨n, hn, hnrun⟩ := hrun (I + J + k + 1)
  -- runs reaching back to position `j` : `orbit j < (1/g)^(n + k - j)`
  have hex : ∃ j, j ≤ n ∧ orbit g α j < (1 / (g : ℝ)) ^ (n + k - j) := by
    refine ⟨n, le_rfl, ?_⟩
    rw [Nat.add_sub_cancel_left, one_div_pow]; exact hnrun
  classical
  set j₀ := Nat.find hex with hj₀
  have hj₀spec : j₀ ≤ n ∧ orbit g α j₀ < (1 / (g : ℝ)) ^ (n + k - j₀) := Nat.find_spec hex
  have hj₀min : ∀ j, j < j₀ → ¬ (j ≤ n ∧ orbit g α j < (1 / (g : ℝ)) ^ (n + k - j)) :=
    fun j hj => Nat.find_min hex hj
  -- `j₀ > J`: early positions are too large to start such a run
  have hj₀J : J < j₀ := by
    by_contra hcon
    push Not at hcon
    have h1 := hj₀spec.2
    have hle : (1 / (g : ℝ)) ^ (n + k - j₀) ≤ (1 / (g : ℝ)) ^ (i j₀) := by
      apply pow_le_pow_of_le_one hinv0.le hinv1.le
      have := hIj j₀ hcon
      omega
    linarith [hi j₀]
  refine ⟨j₀, by omega, ?_, ?_⟩
  · have h1 := hj₀spec.2
    have hle : (1 / (g : ℝ)) ^ (n + k - j₀) ≤ (1 / (g : ℝ)) ^ k := by
      apply pow_le_pow_of_le_one hinv0.le hinv1.le
      have := hj₀spec.1
      omega
    have hle' : (1 / (g : ℝ)) ^ k = 1 / (g : ℝ) ^ k := one_div_pow _ _
    linarith
  · -- the digit before position `j₀` is nonzero, else the run reaches `j₀ − 1`
    by_contra hcon
    push Not at hcon
    have hd0 : ⌊(g : ℝ) * orbit g α (j₀ - 1)⌋ = 0 := by
      have := Int.floor_nonneg.2
        (mul_nonneg hg0.le (orbit_mem_Ico g α (j₀ - 1)).1)
      omega
    have hstep : orbit g α j₀ = Int.fract ((g : ℝ) * orbit g α (j₀ - 1)) := by
      rw [← orbit_succ]; congr 1; omega
    have hfr : Int.fract ((g : ℝ) * orbit g α (j₀ - 1)) = (g : ℝ) * orbit g α (j₀ - 1) := by
      rw [Int.fract, hd0]; simp
    have hlt : orbit g α (j₀ - 1) < (1 / (g : ℝ)) ^ (n + k - (j₀ - 1)) := by
      have h1 := hj₀spec.2
      rw [hstep, hfr] at h1
      have hexp : n + k - (j₀ - 1) = (n + k - j₀) + 1 := by omega
      rw [hexp, pow_succ]
      have : orbit g α (j₀ - 1) < (1 / (g : ℝ)) ^ (n + k - j₀) * (1 / g) := by
        rw [mul_one_div, lt_div_iff₀ hg0]; linarith
      exact this
    exact hj₀min (j₀ - 1) (by omega) ⟨by omega, hlt⟩

/-- A nonzero base-`g` digit is a unit mod a prime `g`. -/
theorem isCoprime_of_emod_pos (g : ℕ) (hg : g.Prime) (A : ℤ) (h1 : 1 ≤ A % g) :
    IsCoprime A (g : ℤ) := by
  have hnd : ¬ (g : ℤ) ∣ A := by
    intro hdvd
    rw [Int.dvd_iff_emod_eq_zero] at hdvd
    omega
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hcop : Nat.Coprime g A.natAbs := by
    rw [hg.coprime_iff_not_dvd, ← Int.natCast_dvd]; exact hnd
  rw [Int.gcd_comm]
  exact hcop

/-- **Zero runs settle the multiplier problem at `gᵏ` (prime base).**  If
the base-`g` expansion of the irrational `α` contains the block `0ᵏ`
infinitely often and `g` is prime, then for every `k`-block `w` some
multiplier `1 ≤ m ≤ gᵏ` has `w` occurring infinitely often in `m·α`. -/
theorem mahler_multiplier_of_zero_runs (g : ℕ) (hg : g.Prime) (α : ℝ) (hα : Irrational α)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : 1 ≤ w.length)
    (hrun : ∀ N, ∃ n, N ≤ n ∧ OccursAt g α (List.replicate w.length 0) n) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ w.length ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg2 : 2 ≤ g := hg.two_le
  set k := w.length with hkdef
  set W := blockNatVal g w with hWdef
  have hW : W < g ^ k := blockNatVal_lt g w hwd
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  -- the run hypothesis in orbit form
  have hrun' : ∀ N, ∃ p, N ≤ p ∧ orbit g α p < 1 / (g : ℝ) ^ k := by
    intro N
    obtain ⟨n, hn, hocc⟩ := hrun N
    rw [occursAt_iff_orbit_mem g hg2 _ _
      (by intro d hd; rw [List.mem_replicate] at hd; omega) n, List.length_replicate,
      blockNatVal_replicate_zero] at hocc
    refine ⟨n, hn, ?_⟩
    have := hocc.2
    simpa using this
  by_contra hcon
  push Not at hcon
  choose! Nf hNf using hcon
  set N₀ := (Finset.range (g ^ k + 1)).sup Nf with hN₀def
  have hN₀ : ∀ m, m ≤ g ^ k → Nf m ≤ N₀ := fun m hm =>
    Finset.le_sup (f := Nf) (Finset.mem_range.2 (by omega))
  obtain ⟨p, hp, hprun, hdig⟩ := exists_maximal_zero_run g k hg2 α hα hrun' N₀
  set n := p - k with hn
  have hpn : p = n + k := by omega
  -- the block before the run is a unit mod `g`
  have hcop : IsCoprime ⌊(g : ℝ) ^ k * orbit g α n⌋ (g : ℤ) := by
    apply isCoprime_of_emod_pos g hg
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', floor_pow_orbit_emod g k' n hg2 α]
    have : n + k' = p - 1 := by omega
    rw [this]; exact hdig
  obtain ⟨m, hm1, hmQ, hmem⟩ := hit_of_zero_run g k n hg2 α hα hcop (hpn ▸ hprun) W hW
  apply hNf m hm1 hmQ n (le_trans (hN₀ m hmQ) (by omega))
  rw [occursAt_iff_orbit_mem g hg2 _ w hwd n, orbit_nat_mul]
  exact hmem

/-! ### The `(g−1)`-run case by reflection `α ↦ −α` -/

/-- The digit-reflected block `w ↦ map (g − 1 − ·) w` has value `gᵏ − 1 − W`. -/
theorem blockNatVal_map_reflect (g : ℕ) (hg : 1 ≤ g) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) :
    blockNatVal g (w.map fun d => g - 1 - d) + blockNatVal g w + 1 = g ^ w.length := by
  induction w with
  | nil => simp [blockNatVal]
  | cons d w ih =>
      have hd : d < g := hwd d (List.mem_cons_self ..)
      have ih' := ih (fun e he => hwd e (List.mem_cons_of_mem d he))
      rw [List.map_cons, blockNatVal_cons, blockNatVal_cons, List.length_map, List.length_cons,
        pow_succ]
      zify [hd, hg, (show d ≤ g - 1 by omega)] at ih' ⊢
      linear_combination ih'

/-- Reflection of the orbit: `orbit g (−x) n = 1 − orbit g x n` for irrational `x`. -/
theorem orbit_neg (g : ℕ) (hg : 2 ≤ g) (x : ℝ) (hx : Irrational x) (n : ℕ) :
    orbit g (-x) n = 1 - orbit g x n := by
  have hne : Int.fract (x * (g : ℝ) ^ n) ≠ 0 := (orbit_irrational g hg x hx n).ne_zero
  unfold orbit
  rw [neg_mul, Int.fract_neg hne]

/-- A block occurs in `−x` exactly when its digit reflection occurs in `x`
(irrational `x`, so cell endpoints are never hit). -/
theorem occursAt_neg_iff (g : ℕ) (hg : 2 ≤ g) (x : ℝ) (hx : Irrational x)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (n : ℕ) :
    OccursAt g (-x) (w.map fun d => g - 1 - d) n ↔ OccursAt g x w n := by
  have hwd' : ∀ d ∈ w.map (fun d => g - 1 - d), d < g := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨e, _, rfl⟩ := hd
    omega
  rw [occursAt_iff_orbit_mem g hg _ _ hwd' n, occursAt_iff_orbit_mem g hg _ _ hwd n,
    orbit_neg g hg x hx n, List.length_map]
  have hval := blockNatVal_map_reflect g (by omega) w hwd
  set k := w.length with hk
  set W := blockNatVal g w with hW
  set R := blockNatVal g (w.map fun d => g - 1 - d) with hR
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hRR : (R : ℝ) = (g : ℝ) ^ k - 1 - W := by
    have h : ((R : ℝ) + W + 1) = (g : ℝ) ^ k := by exact_mod_cast hval
    linarith
  have hirr : Irrational (orbit g x n) := orbit_irrational g hg x hx n
  have hA : ((g : ℝ) ^ k - 1 - W) / (g : ℝ) ^ k = 1 - ((W : ℝ) + 1) / (g : ℝ) ^ k := by
    field_simp; ring
  have hB : ((g : ℝ) ^ k - 1 - W + 1) / (g : ℝ) ^ k = 1 - (W : ℝ) / (g : ℝ) ^ k := by
    field_simp; ring
  rw [hRR, Set.mem_Ico, Set.mem_Ico, hA, hB]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, lt_of_le_of_ne (by linarith) ?_⟩
    intro heq
    apply hirr.ne_rat (((W : ℚ) + 1) / ((g : ℚ) ^ k))
    rw [heq]; push_cast; ring
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    have hne : orbit g x n ≠ (W : ℝ) / (g : ℝ) ^ k := by
      intro heq
      apply hirr.ne_rat ((W : ℚ) / ((g : ℚ) ^ k))
      rw [heq]; push_cast; ring
    have : (W : ℝ) / (g : ℝ) ^ k < orbit g x n := lt_of_le_of_ne h1 (Ne.symm hne)
    linarith

/-- **`(g−1)`-runs settle the multiplier problem at `gᵏ` (prime base).**  If
the base-`g` expansion of the irrational `α` contains the block `(g−1)ᵏ`
infinitely often and `g` is prime, then for every `k`-block `w` some
multiplier `1 ≤ m ≤ gᵏ` has `w` occurring infinitely often in `m·α`. -/
theorem mahler_multiplier_of_pred_runs (g : ℕ) (hg : g.Prime) (α : ℝ) (hα : Irrational α)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : 1 ≤ w.length)
    (hrun : ∀ N, ∃ n, N ≤ n ∧ OccursAt g α (List.replicate w.length (g - 1)) n) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ w.length ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg2 : 2 ≤ g := hg.two_le
  set w' := w.map fun d => g - 1 - d with hw'
  have hwd' : ∀ d ∈ w', d < g := by
    intro d hd
    rw [hw', List.mem_map] at hd
    obtain ⟨e, _, rfl⟩ := hd
    omega
  have hlen : w'.length = w.length := List.length_map ..
  have hrep : ∀ d ∈ List.replicate w.length (g - 1), d < g := by
    intro d hd
    rw [List.mem_replicate] at hd
    omega
  have hrun' : ∀ N, ∃ n, N ≤ n ∧ OccursAt g (-α) (List.replicate w'.length 0) n := by
    intro N
    obtain ⟨n, hn, h⟩ := hrun N
    refine ⟨n, hn, ?_⟩
    have hrefl : List.replicate w'.length 0
        = (List.replicate w.length (g - 1)).map (fun d => g - 1 - d) := by
      rw [hlen, List.map_replicate]; simp
    rw [hrefl, occursAt_neg_iff g hg2 α hα _ hrep n]
    exact h
  obtain ⟨m, hm1, hmQ, hocc⟩ :=
    mahler_multiplier_of_zero_runs g hg (-α) hα.neg w' hwd' (by rw [hlen]; exact hk) hrun'
  refine ⟨m, hm1, by rw [hlen] at hmQ; exact hmQ, fun N => ?_⟩
  obtain ⟨n, hn, h⟩ := hocc N
  refine ⟨n, hn, ?_⟩
  rw [show (m : ℝ) * -α = -((m : ℝ) * α) by ring,
    occursAt_neg_iff g hg2 _ (hα.natCast_mul (by omega)) w hwd n] at h
  exact h

end NormalNumbers.Mahler
