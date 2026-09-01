/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive

/-!
# Mahler's multiplier theorem, with the bound `(g+3)·gᵏ` 🧮

**Theorem** (`mahler_multiplier`).  For every irrational `α`, every base
`g ≥ 2`, and every block `w` of `k` base-`g` digits, some multiplier
`1 ≤ m ≤ (g+3)·gᵏ` has `w` occurring infinitely often in the base-`g`
expansion of `m·α`.

This is the theorem behind the whole adder/tower wing (Mahler 1973,
Theorem M, with `m ≤ g^(2k+1)`; sharpened by Berend–Boshernitzan 1994 to
`m ≤ 2·g^(k+1)` per our secondary sources — see `Literature.lean`).  The
bound proved here, `(g+3)·gᵏ`, is **below** `2g^(k+1)` for every `g ≥ 4`,
equal to it at `g = 3`, and above it only at `g = 2` (`5·2ᵏ` vs `4·2ᵏ`).
The ledger edges are wired in `LiteratureMahler.lean`.

## The proof (self-contained, elementary)

Write `x_n = {gⁿ α}` (`orbit g α n`) and `C = [W/gᵏ, (W+1)/gᵏ)` for the
cell of `w`.  `w` occurs at position `n` in `m α` iff `{m x_n} ∈ C`
(`occursAt_iff_orbit_mem` + `orbit_nat_mul`).  Suppose every `m ≤ M`
fails from position `N₀` on, so every `x_n`, `n ≥ N₀`, is **bad**:
`{m x_n} ∉ C` for all `1 ≤ m ≤ M`.

* **Covering lemma** (`near_rational_of_bad`).  By Dirichlet there is a
  reduced `p/q`, `q ≤ gᵏ`, with `η := q x − p`, `|η| < g⁻ᵏ`.  Writing
  `m = ℓ q + r`, the multiples `{m x}` fall into `q` arithmetic
  progressions of step `η`, one starting within `|η|` of each grid point
  `j/q` (`rp ≡ j mod q` is solvable since `gcd(p,q) = 1`).  With
  `L = ⌊M/q⌋` points each, once `(L−1)|η| ≥ 1/q` these progressions
  sweep every cell of width `≥ |η|` (`sweep_pos` / `sweep_neg`).  So a
  bad `x` has `(L−1)|η| < 1/q`, i.e. `(M − 2gᵏ)·|q x − p| < 1`.
* **Escape lemma** (`orbit_escapes`).  If `x_n` is within `1/(q_n D)` of
  `p_n/q_n` (`q_n ≤ Q`) for all `n ≥ N₀`, with `D ≥ (g+1)Q`, then the
  shadow rational `g p_n/q_n − ⌊g x_n⌋` (denominator `q_n`) and
  `p_{n+1}/q_{n+1}` are both within `< 1/(q_n q_{n+1})` of `x_{n+1}`, so
  they coincide: the integer `q_{n+1}(g p_n − q_n⌊g x_n⌋) − q_n p_{n+1}`
  has absolute value `< 1`.  Hence the defect `ε_n = x_n − p_n/q_n`
  satisfies `ε_{n+1} = g ε_n` **exactly**, and `|ε_{N₀+i}| = gⁱ |ε_{N₀}|`
  is unbounded while `ε_{N₀} ≠ 0` (irrational vs rational) — but every
  `|ε_n| < 1/D`.
* Taking `M = (g+3)gᵏ` gives `D = M − 2gᵏ = (g+1)gᵏ`, exactly the escape
  lemma's threshold with `Q = gᵏ`.

No ergodic theory, no compactness: Dirichlet + a modular inverse + the
`×g` recursion.  Every theorem here audits `[propext, Classical.choice,
Quot.sound]`.
-/

namespace NormalNumbers.Mahler

/-- Modular inverse witness: for coprime `p, q` and any `j`, some `r ∈ [0, q)`
has `r * p ≡ j (mod q)`. -/
theorem exists_residue_mul (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime p (q : ℤ))
    (j : ℤ) : ∃ r : ℤ, 0 ≤ r ∧ r < q ∧ (q : ℤ) ∣ r * p - j := by
  obtain ⟨u, v, huv⟩ := hcop
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  refine ⟨(u * j) % q, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hq0, ?_⟩
  have hmod : (u * j) % q = u * j - q * ((u * j) / q) := Int.emod_def _ _
  rw [hmod]
  refine ⟨-(j * v) - (u * j / q) * p, ?_⟩
  linear_combination j * huv

/-- The fractional part of `t` when `t = z + y` with `z` an integer and
`y ∈ [0, 1)`. -/
theorem fract_eq_of_eq_int_add {t y : ℝ} (z : ℤ) (h : t = z + y) (hy0 : 0 ≤ y)
    (hy1 : y < 1) : Int.fract t = y := by
  rw [h, Int.fract_intCast_add]
  exact Int.fract_eq_self.2 ⟨hy0, hy1⟩

/-- **The sweep lemma, positive-step form.**  Let `η = q x − p ∈ (0, g⁻ᵏ)`
with `p, q` coprime.  The multiples `m x`, `1 ≤ m < L q`, written as
`m = ℓ q + r`, form `q` arithmetic progressions of step `η` (one starting
within `η` above each grid point `j/q`); once `(L−1) η ≥ 1/q` their union
meets every cell `[W/gᵏ, (W+1)/gᵏ)`. -/
theorem sweep_pos (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (x : ℝ) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime p (q : ℤ))
    (hη0 : 0 < (q : ℝ) * x - p) (hη1 : (q : ℝ) * x - p < 1 / (g : ℝ) ^ k)
    (L : ℕ) (hcover : 1 / (q : ℝ) ≤ ((L : ℝ) - 1) * ((q : ℝ) * x - p)) :
    ∃ m : ℕ, 1 ≤ m ∧ m + 1 ≤ L * q ∧
      Int.fract ((m : ℝ) * x) ∈
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
  set η : ℝ := (q : ℝ) * x - p with hηdef
  set a : ℝ := (W : ℝ) / (g : ℝ) ^ k with hadef
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ha0 : 0 ≤ a := by positivity
  have hcell : a + 1 / (g : ℝ) ^ k = ((W : ℝ) + 1) / (g : ℝ) ^ k := by
    rw [hadef, add_div]
  have hW1 : (W : ℝ) + 1 ≤ (g : ℝ) ^ k := by exact_mod_cast hW
  have ha1 : ((W : ℝ) + 1) / (g : ℝ) ^ k ≤ 1 := by
    rw [div_le_one hgk]; exact hW1
  have halt1 : a < 1 := by
    rw [hadef, div_lt_one hgk]; linarith
  have hqx : (q : ℝ) * x = p + η := by rw [hηdef]; ring
  -- `L ≥ 2` is forced by the covering hypothesis
  have hL2' : 2 ≤ L := by
    by_contra hcon
    push Not at hcon
    have hL1 : (L : ℝ) ≤ 1 := by exact_mod_cast (by omega : L ≤ 1)
    have h1 : ((L : ℝ) - 1) * η ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hη0.le; linarith
    have h2 : (0 : ℝ) < 1 / q := by positivity
    linarith
  -- special case `W = 0`: the multiple `q x` has fractional part `η ∈ (0, g⁻ᵏ)`
  by_cases hW0 : W = 0
  · subst hW0
    refine ⟨q, hq, ?_, ?_⟩
    · have : 2 * q ≤ L * q := Nat.mul_le_mul_right q hL2'
      omega
    · rw [fract_eq_of_eq_int_add p hqx hη0.le (by linarith)]
      refine ⟨?_, ?_⟩
      · rw [hadef]; simp only [Nat.cast_zero, zero_div]; exact hη0.le
      · simp only [Nat.cast_zero, zero_add]; exact hη1
  -- main case `W ≥ 1`, so `a > 0`
  have hapos : 0 < a := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hW0
    rw [hadef]; positivity
  -- the grid point `j / q` just below `a`
  set j : ℤ := ⌊a * q⌋ with hjdef
  have hj1 : (j : ℝ) ≤ a * q := Int.floor_le _
  have hj2 : a * q < j + 1 := Int.lt_floor_add_one _
  have hj0 : (0 : ℤ) ≤ j := by
    rw [hjdef]; exact Int.floor_nonneg.2 (by positivity)
  have hjq : j < q := by
    have : (j : ℝ) < q := by nlinarith
    exact_mod_cast this
  obtain ⟨r, hr0, hrq, t, ht⟩ := exists_residue_mul p q hq hcop j
  have htR : (r : ℝ) * p - j = q * t := by exact_mod_cast ht
  -- the start of the progression through the residue class `r`
  set s : ℝ := (j : ℝ) / q + (r : ℝ) * η / q with hsdef
  have hrR0 : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hrRq : (r : ℝ) < q := by exact_mod_cast hrq
  have hs_lo : a - 1 / q < s := by
    have h1 : a - 1 / q < (j : ℝ) / q := by
      rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hqR]; linarith
    have h2 : 0 ≤ (r : ℝ) * η / q := by positivity
    rw [hsdef]; linarith
  have hs_hi : s < a + η := by
    have h1 : (j : ℝ) / q ≤ a := by rw [div_le_iff₀ hqR]; exact hj1
    have h2 : (r : ℝ) * η / q < η := by
      rw [div_lt_iff₀ hqR]; nlinarith
    rw [hsdef]; linarith
  have hs_eq : (q : ℝ) * s = j + r * η := by
    rw [hsdef]; field_simp
  -- the key identity: `(ℓ q + r) x = (ℓ p + t) + (s + ℓ η)`
  have key : ∀ ℓ : ℕ, (((ℓ * q + r.toNat : ℕ) : ℝ)) * x
      = (((ℓ : ℤ) * p + t : ℤ) : ℝ) + (s + ℓ * η) := by
    intro ℓ
    have hrt : ((r.toNat : ℕ) : ℝ) = r := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
    push_cast
    rw [hrt]
    apply mul_left_cancel₀ hqR.ne'
    linear_combination ((ℓ : ℝ) * q + r) * hqx + htR - hs_eq
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  by_cases hsa : a ≤ s
  · -- the progression already starts inside the cell: take `m = r`
    have hr1 : 1 ≤ r := by
      by_contra hcon
      push Not at hcon
      have hr : r = 0 := by omega
      subst hr
      -- then `q ∣ j`, so `j = 0` and `a ≤ s = j/q = 0`
      have hjz : j = 0 := by
        have : (q : ℤ) ∣ j := ⟨-t, by linarith⟩
        rcases this with ⟨c, hc⟩
        have hc0 : 0 ≤ c := by
          by_contra hneg; push Not at hneg
          have : j < 0 := by
            have : (q : ℤ) * c ≤ (q : ℤ) * (-1) := by
              apply mul_le_mul_of_nonneg_left _ (by omega); omega
            omega
          omega
        have hc1 : c < 1 := by
          by_contra hge; push Not at hge
          have : (q : ℤ) * 1 ≤ (q : ℤ) * c := mul_le_mul_of_nonneg_left hge (by omega)
          omega
        have : c = 0 := by omega
        subst this; simpa using hc
      have : s = 0 := by rw [hsdef, hjz]; simp
      linarith
    refine ⟨r.toNat, ?_, ?_, ?_⟩
    · omega
    · have : r.toNat + 1 ≤ q := by omega
      have : q ≤ L * q := Nat.le_mul_of_pos_left q (by omega)
      omega
    · have h0' : ((r.toNat : ℕ) : ℝ) * x = (t : ℝ) + s := by
        have := key 0; simpa using this
      rw [fract_eq_of_eq_int_add t h0' hs0 (by linarith)]
      exact ⟨hsa, by linarith⟩
  · -- the progression starts below the cell: step up `⌈(a − s)/η⌉` times
    push Not at hsa
    set ℓ : ℕ := ⌈(a - s) / η⌉₊ with hℓdef
    have hpos : 0 < (a - s) / η := by positivity
    have hℓ1 : 1 ≤ ℓ := by
      rw [hℓdef]; exact Nat.ceil_pos.2 hpos
    have hℓ_lo : (a - s) / η ≤ ℓ := Nat.le_ceil _
    have hℓ_hi : (ℓ : ℝ) < (a - s) / η + 1 := Nat.ceil_lt_add_one hpos.le
    have hy_lo : a ≤ s + ℓ * η := by
      rw [div_le_iff₀ hη0] at hℓ_lo; linarith
    have hy_hi : s + ℓ * η < a + η := by
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hη0] at hℓ_hi; linarith
    have hℓL : ℓ + 1 ≤ L := by
      have h1 : (a - s) / η < (L : ℝ) - 1 := by
        rw [div_lt_iff₀ hη0]
        have : a - s < 1 / q := by linarith
        linarith
      have : (ℓ : ℝ) < L := by linarith
      have : ℓ < L := by exact_mod_cast this
      omega
    refine ⟨ℓ * q + r.toNat, ?_, ?_, ?_⟩
    · have : q ≤ ℓ * q := Nat.le_mul_of_pos_left q hℓ1
      omega
    · have h1 : (ℓ + 1) * q ≤ L * q := Nat.mul_le_mul_right q hℓL
      have h2 : r.toNat + 1 ≤ q := by omega
      nlinarith
    · rw [fract_eq_of_eq_int_add _ (key ℓ) (by positivity) (by linarith)]
      exact ⟨hy_lo, by linarith⟩

/-- **The sweep lemma, negative-step form** (by reflection `x ↦ −x`, which
sends the cell `W` to the cell `gᵏ − 1 − W`); `x` irrational rules out the
endpoint. -/
theorem sweep_neg (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (x : ℝ) (hx : Irrational x) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime p (q : ℤ))
    (hη0 : (q : ℝ) * x - p < 0) (hη1 : -(1 / (g : ℝ) ^ k) < (q : ℝ) * x - p)
    (L : ℕ) (hcover : 1 / (q : ℝ) ≤ ((L : ℝ) - 1) * ((p : ℝ) - q * x)) :
    ∃ m : ℕ, 1 ≤ m ∧ m + 1 ≤ L * q ∧
      Int.fract ((m : ℝ) * x) ∈
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hW1 : W + 1 ≤ g ^ k := hW
  have hW' : g ^ k - 1 - W < g ^ k := by omega
  have hcast : ((g ^ k - 1 - W : ℕ) : ℝ) = (g : ℝ) ^ k - 1 - W := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  obtain ⟨m, hm1, hmL, hmem⟩ := sweep_pos g k (g ^ k - 1 - W) hg hW' (-x) (-p) q hq
    hcop.neg_left (by push_cast; linarith) (by push_cast; linarith) L
    (by convert hcover using 2; push_cast; ring)
  refine ⟨m, hm1, hmL, ?_⟩
  have hmx : Irrational ((m : ℝ) * x) := hx.natCast_mul (by omega)
  have hfne : Int.fract ((m : ℝ) * x) ≠ 0 := by
    intro h0
    rw [Int.fract, sub_eq_zero] at h0
    exact hmx.ne_int _ h0
  rw [show (m : ℝ) * -x = -((m : ℝ) * x) from by ring, Int.fract_neg hfne, hcast] at hmem
  obtain ⟨h1, h2⟩ := hmem
  have hlt : Int.fract ((m : ℝ) * x) ≠ ((W : ℝ) + 1) / (g : ℝ) ^ k := by
    intro heq
    have hrat : Irrational (Int.fract ((m : ℝ) * x)) := hmx.sub_intCast _
    apply hrat.ne_rat (((W : ℚ) + 1) / ((g : ℚ) ^ k))
    rw [heq]; push_cast; ring
  have hA : ((g : ℝ) ^ k - 1 - W) / (g : ℝ) ^ k = 1 - ((W : ℝ) + 1) / (g : ℝ) ^ k := by
    field_simp; ring
  have hB : ((g : ℝ) ^ k - 1 - W + 1) / (g : ℝ) ^ k = 1 - (W : ℝ) / (g : ℝ) ^ k := by
    field_simp; ring
  rw [hA] at h1
  rw [hB] at h2
  exact ⟨by linarith, lt_of_le_of_ne (by linarith) hlt⟩

/-- **The covering lemma.**  If none of the multiples `m x`, `1 ≤ m ≤ M`, has
its fractional part in the cell `[W/gᵏ, (W+1)/gᵏ)`, then `x` is within
`1/(q (M − 2gᵏ))` of a rational `p/q` with `q ≤ gᵏ` — i.e.
`(M − 2gᵏ)·|q x − p| < 1`. -/
theorem near_rational_of_bad (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (M : ℕ) (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k)) :
    ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ g ^ k ∧
      ((M : ℝ) - 2 * (g : ℝ) ^ k) * |(q : ℝ) * x - p| < 1 := by
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hgkN : 0 < g ^ k := by positivity
  obtain ⟨ρ, hρ, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hgkN
  set q : ℕ := ρ.den with hqdef
  set p : ℤ := ρ.num with hpdef
  have hq1 : 1 ≤ q := ρ.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have hcop : IsCoprime p (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact ρ.reduced
  have hρx : (ρ : ℝ) = (p : ℝ) / q := by
    rw [hpdef, hqdef, Rat.cast_def]
  -- `|q x − p| ≤ 1/(gᵏ+1) < 1/gᵏ`
  have hη : |(q : ℝ) * x - p| ≤ 1 / ((g : ℝ) ^ k + 1) := by
    have h := hρ
    have e : x - (p : ℝ) / q = ((q : ℝ) * x - p) / q := by field_simp
    rw [hρx, e, abs_div, abs_of_pos hqR, div_le_iff₀ hqR] at h
    calc |(q : ℝ) * x - p| ≤ 1 / ((((g ^ k : ℕ) : ℝ) + 1) * q) * q := h
      _ = 1 / ((g : ℝ) ^ k + 1) := by push_cast; field_simp
  have hη1 : |(q : ℝ) * x - p| < 1 / (g : ℝ) ^ k := by
    calc |(q : ℝ) * x - p| ≤ 1 / ((g : ℝ) ^ k + 1) := hη
      _ < 1 / (g : ℝ) ^ k := by
          apply one_div_lt_one_div_of_lt hgk; linarith
  have hqgk : q ≤ g ^ k := hden
  refine ⟨p, q, hq1, hqgk, ?_⟩
  set L : ℕ := M / q with hLdef
  -- the multiples with `m + 1 ≤ L q ≤ M` all miss the cell, so `(L−1)|η| < 1/q`
  have hnocover : ((L : ℝ) - 1) * |(q : ℝ) * x - p| < 1 / q := by
    by_contra hcon
    push Not at hcon
    have hLq : L * q ≤ M := Nat.div_mul_le_self M q
    have hne : (q : ℝ) * x - p ≠ 0 := by
      intro h0
      apply (hx.mul_natCast (by omega : q ≠ 0)).ne_int p
      linarith
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hcov' : 1 / (q : ℝ) ≤ ((L : ℝ) - 1) * ((p : ℝ) - q * x) := by
        rw [abs_of_neg hneg, neg_sub] at hcon; exact hcon
      have hη1' : -(1 / (g : ℝ) ^ k) < (q : ℝ) * x - p := by
        have := neg_abs_le ((q : ℝ) * x - p)
        linarith
      obtain ⟨m, hm1, hmL, hmem⟩ := sweep_neg g k W hg hW x hx p q hq1 hcop hneg hη1' L hcov'
      exact hbad m hm1 (by omega) hmem
    · have hcov' : 1 / (q : ℝ) ≤ ((L : ℝ) - 1) * ((q : ℝ) * x - p) := by
        rw [abs_of_pos hpos] at hcon; exact hcon
      have hη1' : (q : ℝ) * x - p < 1 / (g : ℝ) ^ k := by
        have := le_abs_self ((q : ℝ) * x - p)
        linarith
      obtain ⟨m, hm1, hmL, hmem⟩ := sweep_pos g k W hg hW x p q hq1 hcop hpos hη1' L hcov'
      exact hbad m hm1 (by omega) hmem
  -- `(M − 2gᵏ)|η| ≤ q (L − 1) |η| < 1`
  have hqL : (M : ℝ) - q < (q : ℝ) * L := by
    have h := Nat.div_add_mod M q
    have h2 := Nat.mod_lt M hq1
    have h3 : (q : ℝ) * L + ((M % q : ℕ) : ℝ) = M := by
      rw [hLdef]; exact_mod_cast h
    have h4 : ((M % q : ℕ) : ℝ) < q := by exact_mod_cast h2
    linarith
  have hgkq : (q : ℝ) ≤ (g : ℝ) ^ k := by exact_mod_cast hqgk
  have hcoef : (M : ℝ) - 2 * (g : ℝ) ^ k ≤ (q : ℝ) * ((L : ℝ) - 1) := by
    have : (q : ℝ) * ((L : ℝ) - 1) = q * L - q := by ring
    linarith
  have habs : 0 ≤ |(q : ℝ) * x - p| := abs_nonneg _
  calc ((M : ℝ) - 2 * (g : ℝ) ^ k) * |(q : ℝ) * x - p|
      ≤ (q : ℝ) * ((L : ℝ) - 1) * |(q : ℝ) * x - p| :=
        mul_le_mul_of_nonneg_right hcoef habs
    _ = (q : ℝ) * (((L : ℝ) - 1) * |(q : ℝ) * x - p|) := by ring
    _ < (q : ℝ) * (1 / q) := mul_lt_mul_of_pos_left hnocover hqR
    _ = 1 := by field_simp

/-- One step of the `×g` orbit: `orbit g α (n+1) = {g · orbit g α n}`. -/
theorem orbit_succ (g : ℕ) (α : ℝ) (n : ℕ) :
    orbit g α (n + 1) = Int.fract ((g : ℝ) * orbit g α n) := by
  unfold orbit
  have h := Int.floor_add_fract (α * (g : ℝ) ^ n)
  have : α * (g : ℝ) ^ (n + 1)
      = (g : ℝ) * Int.fract (α * (g : ℝ) ^ n) + ((⌊α * (g : ℝ) ^ n⌋ * g : ℤ) : ℝ) := by
    push_cast
    rw [pow_succ]
    linear_combination (-(g : ℝ)) * h
  rw [this, Int.fract_add_intCast]

/-- Orbit points of an irrational are irrational. -/
theorem orbit_irrational (g : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α) (n : ℕ) :
    Irrational (orbit g α n) := by
  have h1 : Irrational (α * (g : ℝ) ^ n) := by
    have := hα.mul_natCast (m := g ^ n) (pow_ne_zero n (by omega))
    push_cast at this
    exact this
  exact h1.sub_intCast _

/-- The orbit of `m·α` is the fractional part of `m` times the orbit of `α`. -/
theorem orbit_nat_mul (g : ℕ) (α : ℝ) (m n : ℕ) :
    orbit g ((m : ℝ) * α) n = Int.fract ((m : ℝ) * orbit g α n) := by
  unfold orbit
  have h := Int.floor_add_fract (α * (g : ℝ) ^ n)
  have : (m : ℝ) * α * (g : ℝ) ^ n
      = (m : ℝ) * Int.fract (α * (g : ℝ) ^ n) + ((m * ⌊α * (g : ℝ) ^ n⌋ : ℤ) : ℝ) := by
    push_cast
    linear_combination (-(m : ℝ)) * h
  rw [this, Int.fract_add_intCast]

/-- **The escape lemma.**  The `×g` orbit of an irrational cannot stay, from
some point on, within `1/(q D)` of a rational `p/q` with `q ≤ Q`, once
`D ≥ (g+1) Q`: consecutive shadow rationals are then forced to be the `×g`
images of each other, so the defect grows geometrically. -/
theorem orbit_escapes (g : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (Q : ℕ) (D : ℝ) (hD : ((g : ℝ) + 1) * Q ≤ D) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ Q ∧
      D * |(q : ℝ) * orbit g α n - p| < 1) : False := by
  choose! p q hq1 hqQ hcl using h
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hD0 : (0 : ℝ) < D := by
    -- some `q ≥ 1` exists at `n = N₀`, so `Q ≥ 1`
    have hQ1 : 1 ≤ Q := le_trans (hq1 N₀ le_rfl) (hqQ N₀ le_rfl)
    have : (0 : ℝ) < ((g : ℝ) + 1) * Q := by
      have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
      positivity
    linarith
  set x : ℕ → ℝ := orbit g α with hxdef
  have hqR : ∀ n, N₀ ≤ n → (0 : ℝ) < q n := fun n hn => by exact_mod_cast hq1 n hn
  have hqQR : ∀ n, N₀ ≤ n → (q n : ℝ) ≤ Q := fun n hn => by exact_mod_cast hqQ n hn
  -- the defect `e n := q n * x n − p n` has `|e n| < 1/D`
  have he : ∀ n, N₀ ≤ n → |(q n : ℝ) * x n - p n| < 1 / D := by
    intro n hn
    rw [lt_div_iff₀ hD0, mul_comm]
    exact hcl n hn
  have hstep : ∀ n, x (n + 1) = (g : ℝ) * x n - ⌊(g : ℝ) * x n⌋ := by
    intro n; rw [hxdef, orbit_succ]; rfl
  -- the recursion `ε (n+1) = g ε n` for the normalized defect `ε n = x n − p n / q n`
  have hrec : ∀ n, N₀ ≤ n →
      x (n + 1) - p (n + 1) / q (n + 1) = (g : ℝ) * (x n - p n / q n) := by
    intro n hn
    have hn' : N₀ ≤ n + 1 := by omega
    have hqn := hqR n hn
    have hqn' := hqR (n + 1) hn'
    set I : ℤ := q (n + 1) * (g * p n - q n * ⌊(g : ℝ) * x n⌋) - q n * p (n + 1) with hIdef
    have hI : (I : ℝ) = (q n : ℝ) * ((q (n + 1) : ℝ) * x (n + 1) - p (n + 1))
        - (g : ℝ) * (q (n + 1) : ℝ) * ((q n : ℝ) * x n - p n) := by
      rw [hIdef, hstep n]; push_cast; ring
    have hIlt : |(I : ℝ)| < 1 := by
      have h1 := he n hn
      have h2 := he (n + 1) hn'
      have hb1 : |(q n : ℝ) * ((q (n + 1) : ℝ) * x (n + 1) - p (n + 1))|
          = (q n : ℝ) * |(q (n + 1) : ℝ) * x (n + 1) - p (n + 1)| := by
        rw [abs_mul, abs_of_pos hqn]
      have hb2 : |(g : ℝ) * (q (n + 1) : ℝ) * ((q n : ℝ) * x n - p n)|
          = (g : ℝ) * (q (n + 1) : ℝ) * |(q n : ℝ) * x n - p n| := by
        rw [abs_mul, abs_of_pos (by positivity)]
      calc |(I : ℝ)| ≤ |(q n : ℝ) * ((q (n + 1) : ℝ) * x (n + 1) - p (n + 1))|
            + |(g : ℝ) * (q (n + 1) : ℝ) * ((q n : ℝ) * x n - p n)| := by
              rw [hI]; exact abs_sub _ _
        _ = (q n : ℝ) * |(q (n + 1) : ℝ) * x (n + 1) - p (n + 1)|
            + (g : ℝ) * (q (n + 1) : ℝ) * |(q n : ℝ) * x n - p n| := by rw [hb1, hb2]
        _ < (q n : ℝ) * (1 / D) + (g : ℝ) * (q (n + 1) : ℝ) * (1 / D) := by
              gcongr
        _ = ((q n : ℝ) + (g : ℝ) * (q (n + 1) : ℝ)) / D := by ring
        _ ≤ (((g : ℝ) + 1) * Q) / D := by
              apply div_le_div_of_nonneg_right _ hD0.le
              have h3 := mul_le_mul_of_nonneg_left (hqQR (n + 1) hn')
                (by positivity : (0 : ℝ) ≤ g)
              linarith [hqQR n hn]
        _ ≤ D / D := by gcongr
        _ = 1 := div_self hD0.ne'
    have hI0 : I = 0 := by
      have : |I| < 1 := by exact_mod_cast hIlt
      exact Int.abs_lt_one_iff.1 this
    have hI0' : (I : ℝ) = 0 := by exact_mod_cast hI0
    rw [hI] at hI0'
    field_simp
    linear_combination hI0'
  -- hence `ε (N₀ + i) = gⁱ ε N₀`
  have hpow : ∀ i, x (N₀ + i) - p (N₀ + i) / q (N₀ + i)
      = (g : ℝ) ^ i * (x N₀ - p N₀ / q N₀) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [show N₀ + (i + 1) = (N₀ + i) + 1 from by omega, hrec (N₀ + i) (by omega), ih,
          pow_succ]
        ring
  -- the initial defect is nonzero (irrational vs rational) and each defect is `< 1/D`
  have hε0 : x N₀ - p N₀ / q N₀ ≠ 0 := by
    intro h0
    have hirr : Irrational (x N₀) := orbit_irrational g hg α hα N₀
    apply hirr.ne_rat ((p N₀ : ℚ) / (q N₀ : ℚ))
    push_cast
    linarith
  have hsmall : ∀ i, |x (N₀ + i) - p (N₀ + i) / q (N₀ + i)| < 1 / D := by
    intro i
    have hn : N₀ ≤ N₀ + i := by omega
    have hq := hqR _ hn
    have hq1' : (1 : ℝ) ≤ q (N₀ + i) := by exact_mod_cast hq1 _ hn
    have : x (N₀ + i) - p (N₀ + i) / q (N₀ + i)
        = ((q (N₀ + i) : ℝ) * x (N₀ + i) - p (N₀ + i)) / q (N₀ + i) := by
      field_simp
    rw [this, abs_div, abs_of_pos hq, div_lt_iff₀ hq]
    calc |(q (N₀ + i) : ℝ) * x (N₀ + i) - p (N₀ + i)| < 1 / D := he _ hn
      _ ≤ 1 / D * q (N₀ + i) := by
          rw [le_mul_iff_one_le_right (by positivity)]; exact hq1'
  -- geometric growth beats the bound
  have hpos : 0 < |x N₀ - p N₀ / q N₀| := abs_pos.2 hε0
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (1 / D / |x N₀ - p N₀ / q N₀|) (by linarith : (1 : ℝ) < g)
  have h1 := hsmall i
  rw [hpow i, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (g : ℝ) ^ i)] at h1
  rw [div_lt_iff₀ hpos] at hi
  linarith

/-- **Mahler's multiplier theorem, with the bound `(g+3)·gᵏ`.**  For every
irrational `α`, base `g ≥ 2`, and digit block `w` of length `k`, some
multiplier `1 ≤ m ≤ (g+3)·gᵏ` has `w` occurring infinitely often in the
base-`g` expansion of `m·α`.

Proof: if every multiple `m α`, `m ≤ M := (g+3)gᵏ`, avoids `w` from some
position `N₀` on, then every orbit point `x_n = {gⁿ α}`, `n ≥ N₀`, is "bad"
for the cell of `w`; the covering lemma (`near_rational_of_bad`) puts such a
point within `1/(q·(g+1)gᵏ)` of a rational with denominator `q ≤ gᵏ`, and
the escape lemma (`orbit_escapes`) shows the `×g` orbit of an irrational
cannot do that forever. -/
theorem mahler_multiplier (g : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ (g + 3) * g ^ w.length ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  set k := w.length with hkdef
  set W := blockNatVal g w with hWdef
  have hW : W < g ^ k := blockNatVal_lt g w hwd
  set M := (g + 3) * g ^ k with hMdef
  by_contra hcon
  push Not at hcon
  choose! Nf hNf using hcon
  set N₀ := (Finset.range (M + 1)).sup Nf with hN₀def
  have hN₀ : ∀ m, m ≤ M → Nf m ≤ N₀ := fun m hm =>
    Finset.le_sup (f := Nf) (Finset.mem_range.2 (by omega))
  have hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
    intro n hn m hm1 hmM hmem
    apply hNf m hm1 hmM n (le_trans (hN₀ m hmM) hn)
    rw [occursAt_iff_orbit_mem g hg _ w hwd n, orbit_nat_mul]
    exact hmem
  have hnear : ∀ n, N₀ ≤ n → ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ g ^ k ∧
      (((g : ℝ) + 1) * ((g ^ k : ℕ) : ℝ)) * |(q : ℝ) * orbit g α n - p| < 1 := by
    intro n hn
    obtain ⟨p, q, hq1, hqk, hlt⟩ := near_rational_of_bad g k W hg hW M (orbit g α n)
      (orbit_irrational g hg α hα n) (hbad n hn)
    refine ⟨p, q, hq1, hqk, ?_⟩
    have : ((M : ℝ) - 2 * (g : ℝ) ^ k) = ((g : ℝ) + 1) * ((g ^ k : ℕ) : ℝ) := by
      rw [hMdef]; push_cast; ring
    rw [← this]; exact hlt
  exact orbit_escapes g hg α hα (g ^ k) _ le_rfl N₀ hnear



end NormalNumbers.Mahler
