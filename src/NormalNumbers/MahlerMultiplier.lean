/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive

/-!
# Mahler's multiplier theorem, with the bound `g^(k+1)` 🧮

**Theorem** (`mahler_multiplier`).  For every irrational `α`, every base
`g ≥ 2`, and every block `w` of `k` base-`g` digits, some multiplier
`1 ≤ m ≤ g^(k+1)` has `w` occurring infinitely often in the base-`g`
expansion of `m·α`.

This is the theorem behind the whole adder/tower wing (Mahler 1973,
Theorem M, with `m ≤ g^(2k+1)`; sharpened by Berend–Boshernitzan 1994 to
`m ≤ 2·g^(k+1)` per our secondary sources — see `Literature.lean`).  The
bound proved here, `g^(k+1)`, is **half** the cited Berend–Boshernitzan
constant for every `g ≥ 2`, and `MahlerLowerBound.lean` proves that no
universal bound below `gᵏ − 1` is possible (`mahler_lower_bound`), so the
remaining room is at most the factor `g`.  The ledger edges are wired in
`LiteratureMahler.lean`.

## The proof (self-contained, elementary)

Write `x_n = {gⁿ α}` (`orbit g α n`) and `C = [W/gᵏ, (W+1)/gᵏ)` for the
cell of `w`.  `w` occurs at position `n` in `m α` iff `{m x_n} ∈ C`
(`occursAt_iff_orbit_mem` + `orbit_nat_mul`).  Suppose every `m ≤ M`
fails from position `N₀` on, so every `x_n`, `n ≥ N₀`, is **bad**:
`{m x_n} ∉ C` for all `1 ≤ m ≤ M`.

* **Universal covering lemma** (`defect_bound_of_bad`).  Let `p/q` be
  *any* reduced rational with `q ≤ gᵏ` and `η := q x − p`, `0 < |η| < g⁻ᵏ`.
  Writing `m = ℓ q + r`, the multiples `{m x}` fall into `q` arithmetic
  progressions of step `η`, one starting within `|η|` of each grid point
  `j/q` (`rp ≡ j mod q` is solvable since `gcd(p,q) = 1`).  Let `j/q` be
  the grid point just below the cell.  Either the progression through
  `j/q` climbs into the cell within the budget `m ≤ M`, or — since the
  climb needs more than `M` multiples — the *next* grid point `(j+1)/q`
  already lies inside the cell, and so does the start of its progression
  (`start_in_cell`).  The second alternative is guaranteed as soon as
  `(M + 1 − 2q)|η| ≥ 1 − q/gᵏ` (`sweep_pos` / `sweep_neg`).  So a bad `x`
  has `(M + 1 − 2q)|η| < 1 − q/gᵏ` for **every** such `p/q`.
* **Contraction** (`defect_contracts_of_bad`).  With `M = g^(k+1)` the
  bound reads `(g gᵏ + 1 − 2q)|η| < 1 − q/gᵏ`, which forces `g|η| < g⁻ᵏ`:
  every approximation of quality `g⁻ᵏ` is really of quality `g⁻ᵏ/g`.
* **Escape lemma** (`orbit_escapes`).  Start from Dirichlet's `ρ₀` at
  `N₀` and follow the *shadow* rational `ρ' = g ρ − ⌊g x_n⌋`, whose
  denominator divides `ρ.den`.  The normalized defect `x_n − ρ` is
  multiplied by exactly `g` at each step (`x_{n+1} − ρ' = g (x_n − ρ)`),
  and contraction keeps the shadow's defect `ρ'.den·|x_{n+1} − ρ'| ≤
  g·ρ.den·|x_n − ρ| < g⁻ᵏ` — so the shadow is again an approximation of
  quality `g⁻ᵏ`, forever.  But `|x_{N₀+i} − ρ_i| = gⁱ |x_{N₀} − ρ₀|` is
  unbounded (`x_{N₀}` irrational), while every defect is `< g⁻ᵏ`.

No ergodic theory, no compactness, and no "two close rationals coincide"
step: Dirichlet once, a modular inverse, and the `×g` recursion.  Every
theorem here audits `[propext, Classical.choice, Quot.sound]`.
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

/-- The progression through the grid point `j'/q` (`0 < j' < q`) starts at
`j'/q + r η/q ∈ [j'/q, j'/q + η)`, where `1 ≤ r < q` is the residue with
`r p ≡ j' (mod q)`.  Hence every interval `[lo, hi)` with `lo < j'/q` and
`j'/q + η ≤ hi ≤ 1` contains `{r x}`. -/
theorem start_in_cell (x : ℝ) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime p (q : ℤ))
    (hη0 : 0 < (q : ℝ) * x - p) (j' : ℤ) (hj'0 : 0 < j') (hj'q : j' < q)
    (lo hi : ℝ) (hlo : lo < (j' : ℝ) / q) (hhi : (j' : ℝ) / q + ((q : ℝ) * x - p) ≤ hi)
    (hhi1 : hi ≤ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m < q ∧ Int.fract ((m : ℝ) * x) ∈ Set.Ico lo hi := by
  set η : ℝ := (q : ℝ) * x - p with hηdef
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqx : (q : ℝ) * x = p + η := by rw [hηdef]; ring
  obtain ⟨r, hr0, hrq, t, ht⟩ := exists_residue_mul p q hq hcop j'
  have hr1 : 1 ≤ r := by
    by_contra hcon
    push Not at hcon
    have hr : r = 0 := by omega
    subst hr
    -- `q ∣ j'` with `0 < j' < q`: impossible
    obtain ⟨c', hc'⟩ : (q : ℤ) ∣ j' := ⟨-t, by linarith⟩
    rcases le_or_gt c' 0 with h | h
    · have : (q : ℤ) * c' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) h
      omega
    · have : (q : ℤ) * 1 ≤ (q : ℤ) * c' := mul_le_mul_of_nonneg_left h (by omega)
      omega
  have htR : (r : ℝ) * p - j' = q * t := by exact_mod_cast ht
  have hrR0 : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hrRq : (r : ℝ) < q := by exact_mod_cast hrq
  have hj'R : (0 : ℝ) < j' := by exact_mod_cast hj'0
  set s : ℝ := (j' : ℝ) / q + (r : ℝ) * η / q with hsdef
  have hs_eq : (q : ℝ) * s = j' + r * η := by rw [hsdef]; field_simp
  have hs_lo : (j' : ℝ) / q ≤ s := by
    have : 0 ≤ (r : ℝ) * η / q := by positivity
    rw [hsdef]; linarith
  have hs_hi : s < (j' : ℝ) / q + η := by
    have : (r : ℝ) * η / q < η := by rw [div_lt_iff₀ hqR]; nlinarith
    rw [hsdef]; linarith
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hs1 : s < 1 := by linarith
  have hrt : ((r.toNat : ℕ) : ℝ) = r := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
  have key : ((r.toNat : ℕ) : ℝ) * x = (t : ℝ) + s := by
    rw [hrt]
    apply mul_left_cancel₀ hqR.ne'
    linear_combination (r : ℝ) * hqx + htR - hs_eq
  refine ⟨r.toNat, by omega, by omega, ?_⟩
  rw [fract_eq_of_eq_int_add t key hs0 hs1]
  exact ⟨by linarith, by linarith⟩

/-- **The sweep lemma, positive-step form.**  Let `η = q x − p ∈ (0, g⁻ᵏ)`
with `p, q` coprime and `q ≤ gᵏ`.  Writing `m = ℓ q + r`, the multiples
`m x` form `q` arithmetic progressions of step `η`, one starting within `η`
above each grid point `j/q`.  Once `(M + 1 − 2q) η ≥ 1 − q/gᵏ`, some
`1 ≤ m ≤ M` lands in the cell `[W/gᵏ, (W+1)/gᵏ)`: either the progression
through the grid point just below the cell climbs into it within the
budget, or (if that takes more than `M` multiples) the *next* grid point
already lies inside the cell, together with the start of its progression. -/
theorem sweep_pos (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (x : ℝ) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hqk : q ≤ g ^ k) (hcop : IsCoprime p (q : ℤ))
    (hη0 : 0 < (q : ℝ) * x - p) (hη1 : (q : ℝ) * x - p < 1 / (g : ℝ) ^ k)
    (M : ℕ)
    (hcover : 1 - (q : ℝ) / (g : ℝ) ^ k ≤ ((M : ℝ) + 1 - 2 * q) * ((q : ℝ) * x - p)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧
      Int.fract ((m : ℝ) * x) ∈
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
  set η : ℝ := (q : ℝ) * x - p with hηdef
  set a : ℝ := (W : ℝ) / (g : ℝ) ^ k with hadef
  set c : ℝ := 1 / (g : ℝ) ^ k with hcdef
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 : 0 < c := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hcell : a + c = ((W : ℝ) + 1) / (g : ℝ) ^ k := by
    rw [hadef, hcdef, add_div]
  have hW1 : (W : ℝ) + 1 ≤ (g : ℝ) ^ k := by exact_mod_cast hW
  have ha1 : a + c ≤ 1 := by
    rw [hcell, div_le_one hgk]; exact hW1
  have hqc : (q : ℝ) * c ≤ 1 := by
    rw [hcdef, mul_one_div, div_le_one hgk]; exact_mod_cast hqk
  have hqc' : (q : ℝ) / (g : ℝ) ^ k = q * c := by rw [hcdef]; ring
  rw [hqc'] at hcover
  have hqx : (q : ℝ) * x = p + η := by rw [hηdef]; ring
  -- `2q ≤ M + 1` is forced by the covering hypothesis
  have hM2q : 2 * q ≤ M + 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : (M : ℝ) + 1 - 2 * q < 0 := by
      have : ((M : ℝ) + 1) < 2 * q := by exact_mod_cast hcon
      linarith
    have h2 : ((M : ℝ) + 1 - 2 * q) * η < 0 := mul_neg_of_neg_of_pos h1 hη0
    linarith
  have hqM : q ≤ M := by omega
  -- special case `W = 0`: the multiple `q x` has fractional part `η ∈ (0, g⁻ᵏ)`
  by_cases hW0 : W = 0
  · subst hW0
    refine ⟨q, hq, hqM, ?_⟩
    rw [fract_eq_of_eq_int_add p hqx hη0.le (by linarith)]
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
  have hs_hi : s < a + η := by
    have h1 : (j : ℝ) / q ≤ a := by rw [div_le_iff₀ hqR]; exact hj1
    have h2 : (r : ℝ) * η / q < η := by
      rw [div_lt_iff₀ hqR]; nlinarith
    rw [hsdef]; linarith
  have hs_eq : (q : ℝ) * s = j + r * η := by
    rw [hsdef]; field_simp
  have hrt : ((r.toNat : ℕ) : ℝ) = r := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
  -- the key identity: `(ℓ q + r) x = (ℓ p + t) + (s + ℓ η)`
  have key : ∀ ℓ : ℕ, (((ℓ * q + r.toNat : ℕ) : ℝ)) * x
      = (((ℓ : ℤ) * p + t : ℤ) : ℝ) + (s + ℓ * η) := by
    intro ℓ
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
        rcases this with ⟨c', hc'⟩
        have hc0' : 0 ≤ c' := by
          by_contra hneg; push Not at hneg
          have : j < 0 := by
            have : (q : ℤ) * c' ≤ (q : ℤ) * (-1) := by
              apply mul_le_mul_of_nonneg_left _ (by omega); omega
            omega
          omega
        have hc1' : c' < 1 := by
          by_contra hge; push Not at hge
          have : (q : ℤ) * 1 ≤ (q : ℤ) * c' := mul_le_mul_of_nonneg_left hge (by omega)
          omega
        have : c' = 0 := by omega
        subst this; simpa using hc'
      have : s = 0 := by rw [hsdef, hjz]; simp
      linarith
    refine ⟨r.toNat, by omega, by omega, ?_⟩
    have h0' : ((r.toNat : ℕ) : ℝ) * x = (t : ℝ) + s := by
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
    by_cases hℓM : ℓ * q + r.toNat ≤ M
    · -- within budget: `m = ℓ q + r`
      refine ⟨ℓ * q + r.toNat, ?_, hℓM, ?_⟩
      · have : q ≤ ℓ * q := Nat.le_mul_of_pos_left q hℓ1
        omega
      · rw [fract_eq_of_eq_int_add _ (key ℓ) (by positivity) (by linarith)]
        exact ⟨hy_lo, by linarith⟩
    · -- over budget: then the next grid point `(j+1)/q` lies inside the cell,
      -- and so does the start `s'` of the progression through it
      push Not at hℓM
      have hMR : (M : ℝ) + 1 ≤ (ℓ : ℝ) * q + r := by
        have h3 : ((M : ℝ) + 1) ≤ (ℓ : ℝ) * q + ((r.toNat : ℕ) : ℝ) := by
          exact_mod_cast hℓM
        rw [hrt] at h3; exact h3
      have hstep1 : ((M : ℝ) + 1) * η ≤ ((ℓ : ℝ) * q + r) * η :=
        mul_le_mul_of_nonneg_right hMR hη0.le
      have hstep2 : (q : ℝ) * (ℓ * η) < q * (a - s + η) :=
        mul_lt_mul_of_pos_left (by linarith) hqR
      -- hence `j + 1 + q η < q (a + c)`
      have hkey2 : (j : ℝ) + 1 + q * η < q * (a + c) := by
        have e1 : ((M : ℝ) + 1 - 2 * q) * η = ((M : ℝ) + 1) * η - 2 * (q * η) := by ring
        have e2 : ((ℓ : ℝ) * q + r) * η = q * (ℓ * η) + r * η := by ring
        have e3 : (q : ℝ) * (a - s + η) = q * a - q * s + q * η := by ring
        have e4 : (q : ℝ) * (a + c) = q * a + q * c := by ring
        linarith
      have hqη : 0 < (q : ℝ) * η := mul_pos hqR hη0
      have hj1q : (j : ℝ) + 1 < q := by
        have : (q : ℝ) * (a + c) ≤ q * 1 := mul_le_mul_of_nonneg_left ha1 hqR.le
        linarith
      have hj1q' : j + 1 < (q : ℤ) := by exact_mod_cast hj1q
      have hlo' : a < ((j : ℝ) + 1) / q := by rw [lt_div_iff₀ hqR]; linarith
      have hhi' : ((j : ℝ) + 1) / q + η ≤ a + c := by
        rw [div_add' _ _ _ hqR.ne', div_le_iff₀ hqR]; linarith
      obtain ⟨m, hm1, hmq, hmem⟩ := start_in_cell x p q hq hcop hη0 (j + 1) (by omega) hj1q'
        a (a + c) (by push_cast; exact hlo') (by push_cast; exact hhi') ha1
      rw [hcell] at hmem
      exact ⟨m, hm1, by omega, hmem⟩

/-- **The sweep lemma, negative-step form** (by reflection `x ↦ −x`, which
sends the cell `W` to the cell `gᵏ − 1 − W`); `x` irrational rules out the
endpoint. -/
theorem sweep_neg (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (x : ℝ) (hx : Irrational x) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hqk : q ≤ g ^ k)
    (hcop : IsCoprime p (q : ℤ))
    (hη0 : (q : ℝ) * x - p < 0) (hη1 : -(1 / (g : ℝ) ^ k) < (q : ℝ) * x - p)
    (M : ℕ)
    (hcover : 1 - (q : ℝ) / (g : ℝ) ^ k ≤ ((M : ℝ) + 1 - 2 * q) * ((p : ℝ) - q * x)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧
      Int.fract ((m : ℝ) * x) ∈
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hW1 : W + 1 ≤ g ^ k := hW
  have hW' : g ^ k - 1 - W < g ^ k := by omega
  have hcast : ((g ^ k - 1 - W : ℕ) : ℝ) = (g : ℝ) ^ k - 1 - W := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  obtain ⟨m, hm1, hmM, hmem⟩ := sweep_pos g k (g ^ k - 1 - W) hg hW' (-x) (-p) q hq hqk
    hcop.neg_left (by push_cast; linarith) (by push_cast; linarith) M
    (by convert hcover using 2; push_cast; ring)
  refine ⟨m, hm1, hmM, ?_⟩
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

/-- **The universal covering lemma.**  If none of the multiples `m x`,
`1 ≤ m ≤ M`, has its fractional part in the cell `[W/gᵏ, (W+1)/gᵏ)`, then
*every* reduced rational `p/q` with `q ≤ gᵏ` and `|q x − p| < g⁻ᵏ` satisfies
`(M + 1 − 2q)·|q x − p| < 1 − q/gᵏ`.  (For `q = gᵏ` the right-hand side is
`0`, so no such rational exists at all.) -/
theorem defect_bound_of_bad (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (M : ℕ) (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hqk : q ≤ g ^ k) (hcop : IsCoprime p (q : ℤ))
    (hη : |(q : ℝ) * x - p| < 1 / (g : ℝ) ^ k) :
    ((M : ℝ) + 1 - 2 * q) * |(q : ℝ) * x - p| < 1 - (q : ℝ) / (g : ℝ) ^ k := by
  by_contra hcon
  push Not at hcon
  have hne : (q : ℝ) * x - p ≠ 0 := by
    intro h0
    apply (hx.mul_natCast (by omega : q ≠ 0)).ne_int p
    linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hcov' : 1 - (q : ℝ) / (g : ℝ) ^ k ≤ ((M : ℝ) + 1 - 2 * q) * ((p : ℝ) - q * x) := by
      rw [abs_of_neg hneg, neg_sub] at hcon; exact hcon
    have hη1' : -(1 / (g : ℝ) ^ k) < (q : ℝ) * x - p := by
      have := neg_abs_le ((q : ℝ) * x - p)
      linarith
    obtain ⟨m, hm1, hmM, hmem⟩ :=
      sweep_neg g k W hg hW x hx p q hq hqk hcop hneg hη1' M hcov'
    exact hbad m hm1 hmM hmem
  · have hcov' : 1 - (q : ℝ) / (g : ℝ) ^ k ≤ ((M : ℝ) + 1 - 2 * q) * ((q : ℝ) * x - p) := by
      rw [abs_of_pos hpos] at hcon; exact hcon
    have hη1' : (q : ℝ) * x - p < 1 / (g : ℝ) ^ k := by
      have := le_abs_self ((q : ℝ) * x - p)
      linarith
    obtain ⟨m, hm1, hmM, hmem⟩ :=
      sweep_pos g k W hg hW x p q hq hqk hcop hpos hη1' M hcov'
    exact hbad m hm1 hmM hmem

/-- **Contraction at `M = g^(k+1)`.**  If the multiples `m x`, `m ≤ g^(k+1)`,
all miss the cell, then every rational `ρ` with `ρ.den ≤ gᵏ` whose defect
`|ρ.den·x − ρ.num|` is below `g⁻ᵏ` actually has it below `g⁻ᵏ/g`. -/
theorem defect_contracts_of_bad (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ g ^ (k + 1) →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (ρ : ℚ) (hden : ρ.den ≤ g ^ k)
    (hη : |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k) :
    (g : ℝ) * |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k := by
  have hcop : IsCoprime ρ.num (ρ.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact ρ.reduced
  have h := defect_bound_of_bad g k W hg hW (g ^ (k + 1)) x hx hbad ρ.num ρ.den ρ.pos hden
    hcop hη
  set E : ℝ := |(ρ.den : ℝ) * x - ρ.num| with hEdef
  set Q : ℝ := (g : ℝ) ^ k with hQdef
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hQ0 : 0 < Q := by
    have : (0 : ℝ) < g := by linarith
    positivity
  have hq1 : (1 : ℝ) ≤ ρ.den := by exact_mod_cast ρ.pos
  have hqQ : (ρ.den : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hden
  have hM : ((g ^ (k + 1) : ℕ) : ℝ) = (g : ℝ) * Q := by rw [hQdef]; push_cast; ring
  rw [hM] at h
  by_contra hcon
  push Not at hcon
  have hP : 0 ≤ (g : ℝ) * Q + 1 - 2 * ρ.den := by nlinarith
  have h2 : ((g : ℝ) * Q + 1 - 2 * ρ.den) * (1 / Q)
      ≤ ((g : ℝ) * Q + 1 - 2 * ρ.den) * (g * E) := mul_le_mul_of_nonneg_left hcon hP
  have h3 : ((g : ℝ) * Q + 1 - 2 * ρ.den) * (g * E)
      = g * (((g : ℝ) * Q + 1 - 2 * ρ.den) * E) := by ring
  have h4 : (g : ℝ) * (((g : ℝ) * Q + 1 - 2 * ρ.den) * E) < g * (1 - ρ.den / Q) :=
    mul_lt_mul_of_pos_left h (by linarith)
  have h5 : ((g : ℝ) * Q + 1 - 2 * ρ.den) * (1 / Q) < g * (1 - ρ.den / Q) := by linarith
  have h6 : (g : ℝ) * Q + 1 - 2 * ρ.den < g * Q - g * ρ.den := by
    have h7 := mul_lt_mul_of_pos_right h5 hQ0
    have e1 : ((g : ℝ) * Q + 1 - 2 * ρ.den) * (1 / Q) * Q = (g : ℝ) * Q + 1 - 2 * ρ.den := by
      field_simp
    have e2 : (g : ℝ) * (1 - ρ.den / Q) * Q = g * Q - g * ρ.den := by
      field_simp
    rw [e1, e2] at h7
    exact h7
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (g : ℝ) - 2) (by linarith : (0 : ℝ) ≤ ρ.den)]

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

/-- **The escape lemma.**  Suppose that from `N₀` on, every rational
approximation `ρ` of `x_n = orbit g α n` with `ρ.den ≤ Q` and defect
`|ρ.den·x_n − ρ.num| < 1/Q` in fact has defect `< 1/(g Q)`.  Then `α` is
rational.  Proof: start from Dirichlet's approximation at `N₀` and follow
the *shadow* `ρ' = g ρ − ⌊g x_n⌋` (denominator dividing `ρ.den`): the
normalized defect `|x_n − ρ|` is multiplied by exactly `g` at each step,
while the contraction keeps the shadow's defect below `1/Q` forever —
impossible once `gⁱ` exceeds `1/(Q |x_{N₀} − ρ₀|)`. -/
theorem orbit_escapes (g : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (Q : ℕ) (hQ : 1 ≤ Q) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → ∀ ρ : ℚ, ρ.den ≤ Q →
      |(ρ.den : ℝ) * orbit g α n - ρ.num| < 1 / Q →
      (g : ℝ) * |(ρ.den : ℝ) * orbit g α n - ρ.num| < 1 / Q) : False := by
  set x : ℕ → ℝ := orbit g α with hxdef
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hgR : (1 : ℝ) < g := by exact_mod_cast (by omega : 1 < g)
  have hg0 : (0 : ℝ) < g := by linarith
  -- the defect of `ρ` at `y` is `ρ.den · (y − ρ)`
  have hcast : ∀ (ρ : ℚ) (y : ℝ), (ρ.den : ℝ) * y - ρ.num = ρ.den * (y - ρ) := by
    intro ρ y
    have hd : (ρ.den : ℝ) ≠ 0 := by exact_mod_cast ρ.pos.ne'
    rw [Rat.cast_def]; field_simp
  have hdenpos : ∀ ρ : ℚ, (0 : ℝ) < ρ.den := fun ρ => by exact_mod_cast ρ.pos
  -- Dirichlet at `N₀`
  obtain ⟨ρ₀, hρ₀, hden₀⟩ := Real.exists_rat_abs_sub_le_and_den_le (x N₀) hQ
  set ε₀ : ℝ := |x N₀ - ρ₀| with hε₀
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀]; apply abs_pos.2; intro h0
    exact (orbit_irrational g hg α hα N₀).ne_rat ρ₀ (by linarith)
  -- the invariant: a rational of denominator `≤ Q`, defect `< 1/Q`, and
  -- normalized defect exactly `gⁱ ε₀`
  have hinv : ∀ i, ∃ ρ : ℚ, ρ.den ≤ Q ∧ |(ρ.den : ℝ) * x (N₀ + i) - ρ.num| < 1 / Q ∧
      |x (N₀ + i) - ρ| = (g : ℝ) ^ i * ε₀ := by
    intro i
    induction i with
    | zero =>
        refine ⟨ρ₀, hden₀, ?_, by simp [hε₀]⟩
        simp only [Nat.add_zero]
        rw [hcast, abs_mul, abs_of_pos (hdenpos ρ₀)]
        calc (ρ₀.den : ℝ) * |x N₀ - ρ₀|
            ≤ ρ₀.den * (1 / (((Q : ℝ) + 1) * ρ₀.den)) :=
              mul_le_mul_of_nonneg_left hρ₀ (hdenpos ρ₀).le
          _ = 1 / ((Q : ℝ) + 1) := by
              have hd : (ρ₀.den : ℝ) ≠ 0 := (hdenpos ρ₀).ne'
              field_simp
          _ < 1 / Q := by apply one_div_lt_one_div_of_lt hQR; linarith
    | succ i ih =>
        obtain ⟨ρ, hden, hsmall, hdef⟩ := ih
        have hn : N₀ ≤ N₀ + i := by omega
        have hcontr := h (N₀ + i) hn ρ hden hsmall
        -- the shadow rational
        set z : ℤ := ⌊(g : ℝ) * x (N₀ + i)⌋ with hzdef
        set ρ' : ℚ := (g : ℚ) * ρ - (z : ℚ) with hρ'def
        have hstep : x (N₀ + (i + 1)) = (g : ℝ) * x (N₀ + i) - z := by
          rw [hxdef, show N₀ + (i + 1) = N₀ + i + 1 from rfl, orbit_succ]; rfl
        have hρ'R : (ρ' : ℝ) = (g : ℝ) * ρ - z := by rw [hρ'def]; push_cast; ring
        have hdef' : x (N₀ + (i + 1)) - ρ' = (g : ℝ) * (x (N₀ + i) - ρ) := by
          rw [hstep, hρ'R]; ring
        have hden' : ρ'.den ≤ ρ.den := by
          have h1 : ρ'.den ∣ ((g : ℚ) * ρ).den * (z : ℚ).den := Rat.sub_den_dvd _ _
          have h2 : ((g : ℚ) * ρ).den ∣ (g : ℚ).den * ρ.den := Rat.mul_den_dvd _ _
          rw [Rat.den_intCast, mul_one] at h1
          rw [Rat.den_natCast, one_mul] at h2
          exact Nat.le_of_dvd ρ.pos (dvd_trans h1 h2)
        refine ⟨ρ', le_trans hden' hden, ?_, ?_⟩
        · rw [hcast, abs_mul, abs_of_pos (hdenpos ρ'), hdef', abs_mul, abs_of_pos hg0]
          rw [hcast, abs_mul, abs_of_pos (hdenpos ρ)] at hcontr
          have hden'R : (ρ'.den : ℝ) ≤ ρ.den := by exact_mod_cast hden'
          calc (ρ'.den : ℝ) * ((g : ℝ) * |x (N₀ + i) - ρ|)
              ≤ ρ.den * ((g : ℝ) * |x (N₀ + i) - ρ|) := by gcongr
            _ = g * (ρ.den * |x (N₀ + i) - ρ|) := by ring
            _ < 1 / Q := hcontr
        · rw [hdef', abs_mul, abs_of_pos hg0, hdef, pow_succ]; ring
  -- contradiction: `ρ.den · gⁱ ε₀ < 1/Q` for every `i`
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (1 / Q / ε₀) hgR
  obtain ⟨ρ, hden, hsmall, hdef⟩ := hinv i
  rw [hcast, abs_mul, abs_of_pos (hdenpos ρ), hdef] at hsmall
  have hden1 : (1 : ℝ) ≤ ρ.den := by exact_mod_cast ρ.pos
  rw [div_lt_iff₀ hε₀pos] at hi
  have : (g : ℝ) ^ i * ε₀ ≤ ρ.den * ((g : ℝ) ^ i * ε₀) :=
    le_mul_of_one_le_left (by positivity) hden1
  linarith

/-- **Mahler's multiplier theorem, with the bound `g^(k+1)`.**  For every
irrational `α`, base `g ≥ 2`, and digit block `w` of length `k`, some
multiplier `1 ≤ m ≤ g^(k+1)` has `w` occurring infinitely often in the
base-`g` expansion of `m·α`.

Proof: if every multiple `m α`, `m ≤ g^(k+1)`, avoids `w` from some
position `N₀` on, then every orbit point `x_n = {gⁿ α}`, `n ≥ N₀`, is "bad"
for the cell of `w`; the universal covering lemma then contracts the defect
of every rational approximation of `x_n` with denominator `≤ gᵏ`
(`defect_contracts_of_bad`), and the escape lemma (`orbit_escapes`) shows
the `×g` orbit of an irrational cannot sustain that. -/
theorem mahler_multiplier (g : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ (w.length + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  set k := w.length with hkdef
  set W := blockNatVal g w with hWdef
  have hW : W < g ^ k := blockNatVal_lt g w hwd
  set M := g ^ (k + 1) with hMdef
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
  have hgk : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  apply orbit_escapes g hg α hα (g ^ k) hgk N₀
  intro n hn ρ hden hsmall
  have hcastQ : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  rw [hcastQ] at hsmall ⊢
  exact defect_contracts_of_bad g k W hg hW (orbit g α n) (orbit_irrational g hg α hα n)
    (hbad n hn) ρ hden hsmall

end NormalNumbers.Mahler
