/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundGeneral

/-!
# Mahler multipliers, lower side: periodic background + Liouville burst 🧮

`MahlerLowerBoundGeneral.lean` studies `α = B · Σᵢ g^(−i!)`: a single integer
`N = m B` printed, right-aligned, into a sea of zeros.  This file adds a
**constant periodic background**: for `0 ≤ a ≤ g − 2`,

    α = a/(g − 1) + B · Σᵢ g^(−i!)        (`bgLiouville`)

whose base-`g` expansion is the constant string `a a a a …` with the digits of
`N` *added into it* (with carries) at each burst position `i!`.  Multiplying by
`m` keeps the shape: the background becomes the constant digit
`b = (m a) mod (g − 1)` (because `gⁿ ≡ 1 mod (g − 1)`), and the burst becomes
`N = m B`.

The payoff is that the background can be tuned to make a whole *residue class*
of digits unreachable.  With `a = 2` and `g` odd, `b = 2m mod (g − 1)` is always
**even and `< g − 1`**, so the digit `g − 1` never comes from the background at
all and the entire multiplier budget is spent on the burst.  Exact
computation (`experiments/mahler_bg_burst_family.py`) shows that this family is

    **`M(g,1) = Θ(g²)` for prime `g`** — not `Θ(g)`,

and in fact *attains the true value* of `M(g,1)` for `g = 5, 7, 13, 23`
(`6, 9, 35, 120`), against Berend–Boshernitzan 1994's Theorem 3.3 bound
`(3/2)(g − 1) = 6, 9, 18, 33`.  So the `Θ(g²)` prime-base lower side — the open
half of the Mahler chapter — is realised by a family that is a two-parameter
generalisation of the one already formalized here.

## The orbit identity (`orbit_bg_mem`)

Everything reduces to one clean statement.  Fix `m`, put `b = (m a) mod (g − 1)`,
`N = m B`, and for `d ≥ 1` let `S_d = 1 + g + ⋯ + g^(d−1)` and

    ρ(d) = (b · S_d + N) mod g^d          (`bgResidue`)

— the low `d` digits of "background `b` overwritten by `N`".  Then for every
late position `n` there is a `d ≥ 1` with

    orbit g (m α) n ∈ [ρ(d)/g^d, (ρ(d)+1)/g^d).

`d = (j+1)! − n` is the distance to the next burst, and the point is *pinned to
a single order-`d` cell*, not merely bounded — which is what lets an arbitrary
target block `w` (not just `(g−1)ᵏ`) be excluded, in either direction.

## The lower bound (`mahler_lower_bound_bg`)

If every one of those cells misses the target cell of `w`, no multiplier
`1 ≤ m ≤ M` puts `w` infinitely often into `m α`, so `M(g,k) > M`.  The
hypothesis is the two-sided, base-`g` arithmetic disjointness of
`[ρ, ρ+1)/g^d` from `[W, W+1)/g^k`, uniform in `d` (it covers `d < k` too).
-/

namespace NormalNumbers.Mahler

open LiouvilleNumber
open scoped Nat

/-- The base-`g` repunit `S_d = 1 + g + ⋯ + g^(d−1)`. -/
def repunit (g d : ℕ) : ℕ := ∑ i ∈ Finset.range d, g ^ i

theorem repunit_mul (g d : ℕ) (hg : 1 ≤ g) : (g - 1) * repunit g d + 1 = g ^ d := by
  induction d with
  | zero => simp [repunit]
  | succ d ih =>
    have hrep : repunit g (d + 1) = repunit g d + g ^ d := by
      simp [repunit, Finset.sum_range_succ]
    have hge : 1 ≤ g ^ d := Nat.one_le_pow _ _ hg
    have h1 : (g - 1) * g ^ d + g ^ d = g ^ d * g := by
      have : (g - 1) * g ^ d + g ^ d = ((g - 1) + 1) * g ^ d := by ring
      rw [this, Nat.sub_add_cancel hg]; ring
    rw [hrep, Nat.mul_add, pow_succ]
    omega

theorem repunit_cast (g d : ℕ) (hg : 2 ≤ g) :
    ((g : ℝ) - 1) * (repunit g d : ℝ) + 1 = (g : ℝ) ^ d := by
  have h := repunit_mul g d (by omega)
  have : (((g - 1) * repunit g d + 1 : ℕ) : ℝ) = ((g ^ d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub (show 1 ≤ g by omega)] at this
  linarith

/-- `α = a/(g−1) + B·Σ g^(−i!)`: constant background digit `a`, Liouville bursts
of the integer `B`. -/
noncomputable def bgLiouville (g a B : ℕ) : ℝ :=
  (a : ℝ) / ((g : ℝ) - 1) + (B : ℝ) * liouvilleNumber g

/-- The order-`d` cell index of `m · bgLiouville g a B` at distance `d` before a
burst: the low `d` base-`g` digits of "constant background `b`, plus `m B`". -/
def bgResidue (g a B m d : ℕ) : ℕ :=
  ((m * a % (g - 1)) * repunit g d + m * B) % g ^ d

theorem irrational_bgLiouville (g a B : ℕ) (hg : 2 ≤ g) (hB : 1 ≤ B) :
    Irrational (bgLiouville g a B) := by
  have hL : Irrational ((B : ℝ) * liouvilleNumber g) :=
    ((liouville_liouvilleNumber hg).irrational).natCast_mul (by omega)
  have hq : ((((a : ℚ) / ((g : ℚ) - 1)) : ℚ) : ℝ) = (a : ℝ) / ((g : ℝ) - 1) := by
    push_cast; ring
  rw [bgLiouville, ← hq]
  exact Irrational.ratCast_add (q := _) hL

/-- Real-arithmetic packaging of the final step: an integer plus `(ρ + θ)/G`
with `ρ + 1 ≤ G` and `0 ≤ θ < 1` has fractional part in `[ρ/G, (ρ+1)/G)`. -/
private theorem fract_mem_cell (G : ℝ) (I : ℤ) (ρ θ x : ℝ) (hG : 0 < G)
    (hρ0 : 0 ≤ ρ) (hρ : ρ + 1 ≤ G) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hx : x = (I : ℝ) + (ρ + θ) / G) :
    Int.fract x ∈ Set.Ico (ρ / G) ((ρ + 1) / G) := by
  have h0 : 0 ≤ (ρ + θ) / G := by positivity
  have h1 : (ρ + θ) / G < 1 := by rw [div_lt_one hG]; linarith
  rw [hx, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨h0, h1⟩]
  exact ⟨by gcongr; linarith, by gcongr⟩



/-- `br/(g−1) + T < 1` when `br ≤ g − 2` and `T < g⁻²`: the background digit
leaves room `1/(g−1)`, and the Liouville tail is smaller than that. -/
private theorem theta_lt_one (gr br T : ℝ) (hg : 2 ≤ gr) (hb0 : 0 ≤ br) (hb : br ≤ gr - 2)
    (hT0 : 0 ≤ T) (hT : T < 1 / gr ^ 2) : br / (gr - 1) + T < 1 := by
  have h1 : (0 : ℝ) < gr - 1 := by linarith
  have h2 : br / (gr - 1) ≤ (gr - 2) / (gr - 1) := by gcongr
  have h3 : (gr - 2) / (gr - 1) = 1 - 1 / (gr - 1) := by field_simp; ring
  have h4 : 1 / gr ^ 2 < 1 / (gr - 1) := by
    rw [div_lt_div_iff₀ (by positivity) h1]; nlinarith
  linarith

/-- The assembly identity: background `br/G₁` plus burst remainder `rr/X`
regroups as the integer `qq` plus the single cell `(ρ + θ)/X`. -/
private theorem bg_assemble (G1 X S br rr qq rho T : ℝ) (hG1 : G1 ≠ 0) (hX : X ≠ 0)
    (hS : G1 * S + 1 = X) (hR : br * S + rr = X * qq + rho) :
    br / G1 + rr / X + T = qq + (rho + (br / G1 + T * X)) / X := by
  field_simp
  linear_combination (-br) * hS + G1 * hR

/-- **The orbit identity.**  For `N = m B ≤ g^K` and every position
`n ≥ (K+k+2)!` there is a distance `d ≥ 1` to the next burst such that the
orbit point of `m · bgLiouville g a B` at `n` sits inside the *single* order-`d`
cell indexed by `bgResidue g a B m d`.  (Not merely bounded — pinned.) -/
theorem orbit_bg_mem (g k a B m K : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (ha : a + 2 ≤ g) (hm : 1 ≤ m) (hB : 1 ≤ B) (hNK : m * B ≤ g ^ K)
    (n : ℕ) (hn : (K + k + 2)! ≤ n) :
    ∃ d, 1 ≤ d ∧ orbit g ((m : ℝ) * bgLiouville g a B) n ∈
      Set.Ico ((bgResidue g a B m d : ℝ) / (g : ℝ) ^ d)
        (((bgResidue g a B m d : ℝ) + 1) / (g : ℝ) ^ d) := by
  set N : ℕ := m * B with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg1 : (1 : ℝ) < g := by linarith
  have hg0 : (0 : ℝ) < g := by linarith
  have hgN : 0 < g := by omega
  have hG1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  -- the index `j` with `j! ≤ n < (j+1)!`
  have hex : ∃ j, n < (j + 1)! := ⟨n, by have := Nat.self_le_factorial (n + 1); omega⟩
  obtain ⟨j, hj1, hjmin⟩ : ∃ j, n < (j + 1)! ∧ ∀ i, i < j → ¬ n < (i + 1)! :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjk : K + k + 2 ≤ j := by
    by_contra hlt
    push_neg at hlt
    have h1 : (j + 1)! ≤ (K + k + 2)! := Nat.factorial_le (by omega)
    omega
  have hj0 : j ! ≤ n := by
    have := hjmin (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    omega
  obtain ⟨d, hd1, hFn⟩ : ∃ d, 1 ≤ d ∧ (j + 1)! = n + d := ⟨(j + 1)! - n, by omega, by omega⟩
  refine ⟨d, hd1, ?_⟩
  -- split `L = partialSum + g^{-(j+1)!} + remainder (j+1)`
  obtain ⟨p, hp₀⟩ := partialSum_eq_rat hgN j
  have hp : partialSum (g : ℝ) j = (p : ℝ) / (g : ℝ) ^ (j !) := by
    rw [hp₀]; push_cast; ring
  have hL : liouvilleNumber (g : ℝ)
      = partialSum g j + 1 / (g : ℝ) ^ (j + 1)! + remainder g (j + 1) := by
    have h1 := partialSum_add_remainder hg1 j
    have h2 := partialSum_add_remainder hg1 (j + 1)
    rw [partialSum_succ] at h2
    linarith
  set Rm : ℝ := remainder (g : ℝ) (j + 1) with hRdef
  have hRpos : 0 < Rm := remainder_pos hg1 (j + 1)
  have hRlt : Rm < 1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := remainder_lt (j + 1) hgR
  set T : ℝ := (N : ℝ) * (g : ℝ) ^ n * Rm with hTdef
  have hgn : (0 : ℝ) < (g : ℝ) ^ n := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNg : (0 : ℝ) < (N : ℝ) * (g : ℝ) ^ n := mul_pos hN0 hgn
  have hT0 : 0 ≤ T := by positivity
  have hT : T < 1 / (g : ℝ) ^ (d + k + 1) := by
    have hNK' : (N : ℝ) ≤ (g : ℝ) ^ K := by exact_mod_cast hNK
    have hfac : 1 ≤ (j + 1)! := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have hexp : K + n + (d + k + 1) ≤ (j + 1)! * (j + 1) := by
      have h1 : K + k + 1 ≤ (j + 1)! * j := le_trans (by omega) (Nat.le_mul_of_pos_left j hfac)
      have h2 : (j + 1)! * (j + 1) = (j + 1)! * j + (j + 1)! := by ring
      omega
    have hpow : (g : ℝ) ^ K * (g : ℝ) ^ n * (g : ℝ) ^ (d + k + 1)
        ≤ ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := by
      rw [← pow_add, ← pow_add, ← pow_mul]
      exact pow_le_pow_right₀ hg1.le (by omega)
    have hpos : (0 : ℝ) < ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := by positivity
    calc T < (N : ℝ) * (g : ℝ) ^ n * (1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1)) :=
          mul_lt_mul_of_pos_left hRlt hNg
      _ ≤ (g : ℝ) ^ K * (g : ℝ) ^ n * (1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1)) := by gcongr
      _ ≤ 1 / (g : ℝ) ^ (d + k + 1) := by
          rw [mul_one_div, div_le_div_iff₀ hpos (by positivity), one_mul]
          exact hpow
  -- the Liouville contribution: integer + `r/g^d + T`
  set r := N % g ^ d with hrdef
  have hr_lt : r < g ^ d := Nat.mod_lt _ (by positivity)
  have hdiv : g ^ d * (N / g ^ d) + r = N := Nat.div_add_mod _ _
  have hgd : (0 : ℝ) < (g : ℝ) ^ d := by positivity
  have e1 : (g : ℝ) ^ n = (g : ℝ) ^ (j !) * (g : ℝ) ^ (n - j !) := by
    rw [← pow_add, Nat.add_sub_cancel' hj0]
  have e2 : (g : ℝ) ^ (j + 1)! = (g : ℝ) ^ n * (g : ℝ) ^ d := by rw [hFn, pow_add]
  have e3 : (N : ℝ) = (g : ℝ) ^ d * ((N / g ^ d : ℕ) : ℝ) + r := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hdiv
    push_cast at this
    linarith
  have h1 : (N : ℝ) * ((p : ℝ) / (g : ℝ) ^ (j !)) * (g : ℝ) ^ n
      = (N : ℝ) * p * (g : ℝ) ^ (n - j !) := by
    rw [e1]; field_simp
  have h2 : (N : ℝ) * (1 / (g : ℝ) ^ (j + 1)!) * (g : ℝ) ^ n = (N : ℝ) / (g : ℝ) ^ d := by
    rw [e2]; field_simp
  have h2' : (N : ℝ) / (g : ℝ) ^ d = ((N / g ^ d : ℕ) : ℝ) + (r : ℝ) / (g : ℝ) ^ d := by
    rw [e3]; field_simp
  have hLio : (N : ℝ) * liouvilleNumber g * (g : ℝ) ^ n
      = ((N * p * g ^ (n - j !) + N / g ^ d : ℕ) : ℝ) + ((r : ℝ) / (g : ℝ) ^ d + T) := by
    calc (N : ℝ) * liouvilleNumber g * (g : ℝ) ^ n
        = (N : ℝ) * ((p : ℝ) / (g : ℝ) ^ (j !)) * (g : ℝ) ^ n
          + (N : ℝ) * (1 / (g : ℝ) ^ (j + 1)!) * (g : ℝ) ^ n
          + (N : ℝ) * (g : ℝ) ^ n * Rm := by rw [hL, hp]; ring
      _ = (N : ℝ) * p * (g : ℝ) ^ (n - j !)
          + (((N / g ^ d : ℕ) : ℝ) + (r : ℝ) / (g : ℝ) ^ d) + T := by rw [h1, h2, h2']
      _ = ((N * p * g ^ (n - j !) + N / g ^ d : ℕ) : ℝ)
          + ((r : ℝ) / (g : ℝ) ^ d + T) := by push_cast; ring
  -- the background contribution: integer + `b/(g−1)`, since `gⁿ ≡ 1 (mod g−1)`
  set G : ℕ := g - 1 with hGdef
  set b := m * a % G with hbdef
  set u := m * a / G with hudef
  have hG0 : 1 ≤ G := by omega
  have hb_lt : b < G := Nat.mod_lt _ (by omega)
  obtain ⟨t, ht⟩ : ∃ t, g ^ n = G * t + 1 := by
    obtain ⟨t, ht⟩ : G ∣ g ^ n - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow g 1 n
    exact ⟨t, by have : 1 ≤ g ^ n := Nat.one_le_pow _ _ (by omega); omega⟩
  have hmb : G * u + b = m * a := Nat.div_add_mod _ _
  have hGR : (G : ℝ) = (g : ℝ) - 1 := by
    rw [hGdef, Nat.cast_sub (by omega)]; push_cast; ring
  have hmaR : (m : ℝ) * (a : ℝ) = ((g : ℝ) - 1) * (u : ℝ) + (b : ℝ) := by
    have hc : ((G * u + b : ℕ) : ℝ) = ((m * a : ℕ) : ℝ) := by exact_mod_cast hmb
    push_cast at hc
    rw [hGR] at hc
    linarith
  have hgnR : (g : ℝ) ^ n = ((g : ℝ) - 1) * (t : ℝ) + 1 := by
    have hc : ((g ^ n : ℕ) : ℝ) = ((G * t + 1 : ℕ) : ℝ) := by exact_mod_cast ht
    push_cast at hc
    rw [hGR] at hc
    linarith
  have hBg : (m : ℝ) * ((a : ℝ) / ((g : ℝ) - 1)) * (g : ℝ) ^ n
      = ((u * G * t + u + b * t : ℕ) : ℝ) + (b : ℝ) / ((g : ℝ) - 1) := by
    have hIc : ((u * G * t + u + b * t : ℕ) : ℝ)
        = (u : ℝ) * ((g : ℝ) - 1) * (t : ℝ) + (u : ℝ) + (b : ℝ) * (t : ℝ) := by
      push_cast; rw [hGR]
    rw [hIc, show (m : ℝ) * ((a : ℝ) / ((g : ℝ) - 1)) * (g : ℝ) ^ n
        = ((m : ℝ) * (a : ℝ)) * (g : ℝ) ^ n / ((g : ℝ) - 1) by ring, hmaR, hgnR]
    field_simp
    ring
  -- assemble
  have hx : (m : ℝ) * bgLiouville g a B * (g : ℝ) ^ n
      = (((u * G * t + u + b * t) + (N * p * g ^ (n - j !) + N / g ^ d) : ℕ) : ℝ)
        + ((b : ℝ) / ((g : ℝ) - 1) + (r : ℝ) / (g : ℝ) ^ d + T) := by
    have hsplit : (m : ℝ) * bgLiouville g a B * (g : ℝ) ^ n
        = (m : ℝ) * ((a : ℝ) / ((g : ℝ) - 1)) * (g : ℝ) ^ n
          + (N : ℝ) * liouvilleNumber g * (g : ℝ) ^ n := by
      rw [bgLiouville, hNdef]; push_cast; ring
    rw [hsplit, hBg, hLio]; push_cast; ring
  -- the repunit identity, and the cell index
  have hS : ((g : ℝ) - 1) * (repunit g d : ℝ) + 1 = (g : ℝ) ^ d := repunit_cast g d hg
  obtain ⟨Rn, hRndef⟩ : ∃ x : ℕ, x = b * repunit g d + r := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ x : ℕ, x = Rn % g ^ d := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ x : ℕ, x = Rn / g ^ d := ⟨_, rfl⟩
  have hRnq : g ^ d * q + ρ = Rn := by rw [hρdef, hqdef]; exact Nat.div_add_mod _ _
  have hRnR : (b : ℝ) * (repunit g d : ℝ) + (r : ℝ) = (g : ℝ) ^ d * (q : ℝ) + (ρ : ℝ) := by
    have hc : ((g ^ d * q + ρ : ℕ) : ℝ) = ((b * repunit g d + r : ℕ) : ℝ) := by
      rw [hRnq, hRndef]
    push_cast at hc
    linarith
  set θ : ℝ := (b : ℝ) / ((g : ℝ) - 1) + T * (g : ℝ) ^ d with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by
    have hbR : (b : ℝ) ≤ (g : ℝ) - 2 := by
      have hbn : b + 2 ≤ g := by omega
      have h := (Nat.cast_le (α := ℝ)).2 hbn
      push_cast at h; linarith
    have hTd : T * (g : ℝ) ^ d < 1 / (g : ℝ) ^ 2 := by
      have hpow : (g : ℝ) ^ (d + k + 1) = (g : ℝ) ^ d * (g : ℝ) ^ (k + 1) := by
        rw [← pow_add]; ring_nf
      have hmul := mul_lt_mul_of_pos_right hT hgd
      rw [hpow] at hmul
      have hstep : T * (g : ℝ) ^ d < 1 / (g : ℝ) ^ (k + 1) := by
        calc T * (g : ℝ) ^ d < 1 / ((g : ℝ) ^ d * (g : ℝ) ^ (k + 1)) * (g : ℝ) ^ d := hmul
          _ = 1 / (g : ℝ) ^ (k + 1) := by field_simp
      have hk2 : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ (k + 1) := pow_le_pow_right₀ hg1.le (by omega)
      have hq2 : 1 / (g : ℝ) ^ (k + 1) ≤ 1 / (g : ℝ) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hk2
      linarith
    rw [hθdef]
    exact theta_lt_one (g : ℝ) (b : ℝ) (T * (g : ℝ) ^ d) hgR (by positivity) hbR
      (by positivity) hTd
  have hρlt : ρ < g ^ d := by rw [hρdef]; exact Nat.mod_lt _ (by positivity)
  have hρR : (ρ : ℝ) + 1 ≤ (g : ℝ) ^ d := by
    have hle : ρ + 1 ≤ g ^ d := hρlt
    exact_mod_cast hle
  have hres : bgResidue g a B m d = ρ := by
    rw [bgResidue, hρdef, hRndef, hrdef, hNdef, ← hGdef, ← hbdef, Nat.add_mod_mod]
  rw [hres, orbit]
  refine fract_mem_cell ((g : ℝ) ^ d)
    ((((u * G * t + u + b * t) + (N * p * g ^ (n - j !) + N / g ^ d)) + q : ℕ) : ℤ)
    (ρ : ℝ) θ _ hgd (by positivity) hρR hθ0 hθ1 ?_
  rw [hx, hθdef]
  have hkey : (b : ℝ) / ((g : ℝ) - 1) + (r : ℝ) / (g : ℝ) ^ d + T
      = (q : ℝ) + ((ρ : ℝ) + ((b : ℝ) / ((g : ℝ) - 1) + T * (g : ℝ) ^ d)) / (g : ℝ) ^ d :=
    bg_assemble ((g : ℝ) - 1) ((g : ℝ) ^ d) (repunit g d : ℝ) (b : ℝ) (r : ℝ) (q : ℝ) (ρ : ℝ) T
      hG1.ne' hgd.ne' hS hRnR
  rw [hkey]
  simp only [Nat.cast_add, Int.cast_add, Int.cast_natCast]
  ring

/-- **The lower bound.**  If for every multiplier `1 ≤ m ≤ M` and every
distance `d ≥ 1` the order-`d` cell `[ρ, ρ+1)/g^d` of `bgResidue g a B m d` is
disjoint from the target cell `[W, W+1)/g^k` of the block `w` — stated as
base-`g` integer arithmetic, and uniformly in `d` so that `d < k` is covered
too — then no multiplier `1 ≤ m ≤ M` puts `w` infinitely often into
`m · bgLiouville g a B`.  Hence `M(g,k) > M`. -/
theorem mahler_lower_bound_bg (g k a B M K : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (ha : a + 2 ≤ g) (hB : 1 ≤ B) (hMK : M * B ≤ g ^ K)
    (w : List ℕ) (hlen : w.length = k) (hwd : ∀ e ∈ w, e < g)
    (havoid : ∀ m, 1 ≤ m → m ≤ M → ∀ d, 1 ≤ d →
      (bgResidue g a B m d + 1) * g ^ k ≤ blockNatVal g w * g ^ d ∨
      (blockNatVal g w + 1) * g ^ d ≤ bgResidue g a B m d * g ^ k) :
    Irrational (bgLiouville g a B) ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * bgLiouville g a B) w n := by
  refine ⟨irrational_bgLiouville g a B hg hB, ?_⟩
  intro m hm1 hmM
  refine ⟨(K + k + 2)!, fun n hn hocc => ?_⟩
  have hg0 : (0 : ℝ) < g := by
    have : (2 : ℝ) ≤ g := by exact_mod_cast hg
    linarith
  rw [occursAt_iff_orbit_mem g hg _ _ hwd n, hlen] at hocc
  obtain ⟨d, hd1, hcell⟩ := orbit_bg_mem g k a B m K hg hk ha hm1 hB
    (le_trans (Nat.mul_le_mul_right B hmM) hMK) n hn
  set W := blockNatVal g w with hWdef
  set ρ := bgResidue g a B m d with hρdef
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hgd : (0 : ℝ) < (g : ℝ) ^ d := by positivity
  rcases havoid m hm1 hmM d hd1 with hc | hc
  · have hcR : ((ρ : ℝ) + 1) * (g : ℝ) ^ k ≤ (W : ℝ) * (g : ℝ) ^ d := by
      have := (Nat.cast_le (α := ℝ)).2 hc
      push_cast at this; linarith
    have hdiv : ((ρ : ℝ) + 1) / (g : ℝ) ^ d ≤ (W : ℝ) / (g : ℝ) ^ k := by
      rw [div_le_div_iff₀ hgd hgk]; linarith
    linarith [hcell.2, hocc.1]
  · have hcR : ((W : ℝ) + 1) * (g : ℝ) ^ d ≤ (ρ : ℝ) * (g : ℝ) ^ k := by
      have := (Nat.cast_le (α := ℝ)).2 hc
      push_cast at this; linarith
    have hdiv : ((W : ℝ) + 1) / (g : ℝ) ^ k ≤ (ρ : ℝ) / (g : ℝ) ^ d := by
      rw [div_le_div_iff₀ hgk hgd]; linarith
    linarith [hcell.1, hocc.2]


/-! ### The single-digit (`k = 1`) specialization, as a finite certificate

For `k = 1` the cell condition collapses to "the base-`g` digit at distance
`d − 1` before the burst is not the target digit `W`", and that digit
*stabilizes*: once `b·S_d + N < g^d`, every later digit equals the background
`b`.  So the whole infinite family of conditions is a **finite check**. -/

/-- Once the background-plus-burst fits in `d` digits it fits in every longer
window. -/
theorem repunit_burst_lt (g b N D : ℕ) (hg : 2 ≤ g) (hbg : b + 1 ≤ g)
    (hD : b * repunit g D + N < g ^ D) :
    ∀ j, D ≤ j → b * repunit g j + N < g ^ j := by
  intro j hj
  induction j with
  | zero => simpa [show D = 0 by omega] using hD
  | succ j ih =>
    rcases eq_or_lt_of_le hj with h | h
    · rw [← h]; exact hD
    · have hij := ih (by omega)
      have hrep : repunit g (j + 1) = repunit g j + g ^ j := by
        simp [repunit, Finset.sum_range_succ]
      have hstep : b * repunit g (j + 1) + N = b * g ^ j + (b * repunit g j + N) := by
        rw [hrep]; ring
      have hle : (b + 1) * g ^ j ≤ g ^ (j + 1) := by
        rw [pow_succ]
        calc (b + 1) * g ^ j = g ^ j * (b + 1) := by ring
          _ ≤ g ^ j * g := Nat.mul_le_mul_left _ hbg
      have hexp : b * g ^ j + (b * repunit g j + N) < (b + 1) * g ^ j := by
        have : (b + 1) * g ^ j = b * g ^ j + g ^ j := by ring
        omega
      omega

/-- The stabilized digit: at distance `j+1` the leading digit is the
background digit `b`. -/
theorem bgResidue_digit_stab (g b N j : ℕ) (hg : 2 ≤ g) (hbg : b + 1 ≤ g)
    (hlt : b * repunit g j + N < g ^ j) :
    ((b * repunit g (j + 1) + N) % g ^ (j + 1)) / g ^ j = b := by
  have hrep : repunit g (j + 1) = repunit g j + g ^ j := by
    simp [repunit, Finset.sum_range_succ]
  have hstep : b * repunit g (j + 1) + N = g ^ j * b + (b * repunit g j + N) := by
    rw [hrep]; ring
  have hle : (b + 1) * g ^ j ≤ g ^ (j + 1) := by
    rw [pow_succ]
    calc (b + 1) * g ^ j = g ^ j * (b + 1) := by ring
      _ ≤ g ^ j * g := Nat.mul_le_mul_left _ hbg
  have hbnd : g ^ j * b + (b * repunit g j + N) < g ^ (j + 1) := by
    have : (b + 1) * g ^ j = g ^ j * b + g ^ j := by ring
    omega
  rw [hstep, Nat.mod_eq_of_lt hbnd, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlt]
  omega

/-- **`k = 1` lower bound from a finite certificate.**  `hdig` is a bounded
(hence `decide`-able) check over `1 ≤ d ≤ D` and `1 ≤ m ≤ M`; `hstab` says the
background-plus-burst fits in `D` digits; `hbg` says the background digit
itself is never the target.  Conclusion: `M(g,1) > M`. -/
theorem mahler_lower_bound_bg_digit (g a B M W D K : ℕ) (hg : 2 ≤ g) (ha : a + 2 ≤ g)
    (hB : 1 ≤ B) (hW : W < g) (hMK : M * B ≤ g ^ K)
    (hstab : ∀ m, m ≤ M → (m * a % (g - 1)) * repunit g D + m * B < g ^ D)
    (hdig : ∀ m, m ≤ M → ∀ d, d ≤ D → 1 ≤ d → bgResidue g a B m d / g ^ (d - 1) ≠ W)
    (hback : ∀ m, m ≤ M → m * a % (g - 1) ≠ W) :
    Irrational (bgLiouville g a B) ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * bgLiouville g a B) [W] n := by
  have hblk : blockNatVal g [W] = W := by simp [blockNatVal]
  -- every distance `d ≥ 1` has leading digit ≠ `W`
  have hall : ∀ m, m ≤ M → ∀ d, 1 ≤ d → bgResidue g a B m d / g ^ (d - 1) ≠ W := by
    intro m hm d hd
    rcases le_or_gt d D with h | h
    · exact hdig m hm d h hd
    · obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
      have hbg1 : m * a % (g - 1) + 1 ≤ g := by
        have : m * a % (g - 1) < g - 1 := Nat.mod_lt _ (by omega)
        omega
      have hlt := repunit_burst_lt g (m * a % (g - 1)) (m * B) D hg hbg1 (hstab m hm) j (by omega)
      have := bgResidue_digit_stab g (m * a % (g - 1)) (m * B) j hg hbg1 hlt
      simpa [bgResidue, this] using hback m hm
  refine mahler_lower_bound_bg g 1 a B M K hg le_rfl ha hB hMK [W] rfl
    (by intro e he; simp at he; omega) ?_
  intro m hm1 hmM d hd1
  have hgd1 : 0 < g ^ (d - 1) := by positivity
  have hpow : g ^ d = g ^ (d - 1) * g := by
    rw [← pow_succ, Nat.sub_add_cancel hd1]
  have hne := hall m hmM d hd1
  rw [hblk, pow_one]
  rcases lt_or_gt_of_ne hne with h | h
  · left
    have : bgResidue g a B m d < W * g ^ (d - 1) := by
      rw [Nat.div_lt_iff_lt_mul hgd1] at h; omega
    rw [hpow]
    calc (bgResidue g a B m d + 1) * g ≤ (W * g ^ (d - 1)) * g := by
          exact Nat.mul_le_mul_right g (by omega)
      _ = W * (g ^ (d - 1) * g) := by ring
  · right
    have : (W + 1) * g ^ (d - 1) ≤ bgResidue g a B m d := by
      have h' : W + 1 ≤ bgResidue g a B m d / g ^ (d - 1) := h
      rw [Nat.le_div_iff_mul_le hgd1] at h'; omega
    rw [hpow]
    calc (W + 1) * (g ^ (d - 1) * g) = ((W + 1) * g ^ (d - 1)) * g := by ring
      _ ≤ bgResidue g a B m d * g := Nat.mul_le_mul_right g this


end NormalNumbers.Mahler
