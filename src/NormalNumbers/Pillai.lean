/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.DigitInterval

/-!
# Pillai's theorem: simple normality at every power implies normality

**Target** (classical, not in mathlib/repo — see B–Y Tier 1 completion):
if `x` is simply normal in base `b^r` for every `r ≥ 1` (single-digit
frequency `→ 1/b^r`), then `x` is normal in base `b` (every block frequency
`→ b^{-length}`).

## Proof route (Niven–Zuckerman style, recorded here for the next lap)

Fix a block `w` of length `L` in base `b`. For `r ≥ L`, every base-`b` digit
position `i` decomposes uniquely as `i = q·r + s`, `0 ≤ s < r`. A window
`[i, i+L)` either sits entirely inside one base-`b^r` "digit" `c_q :=
digitOf (b^r) x q` (`digitOf_pow_eq_blockNatVal` below, the case `s ≤ r-L`)
or straddles two adjacent digits (`s > r-L`, at most `L-1` phases out of
`r`, so density `→ 0` as `r → ∞`).

In the non-straddling case, `window = w` at phase `s` ↔ `c_q`'s `[s,s+L)`
digit slice (as an `r`-digit base-`b` block) equals `w` — there are exactly
`b^(r-L)` values of `c_q ∈ [0,b^r)` with this property, so simple normality
at base `b^r` (a *finite sum* of individual digit-value frequencies, each
`→ 1/b^r`) gives the phase-`s` window frequency `→ b^{r-L}/b^r = b^{-L}`.
Summing over the `r-L+1` non-straddling phases and discarding the
`O(L/r)`-density straddling phases: window frequency `→ (r-L+1)/r · b^{-L}
→ b^{-L}` as `r → ∞` (a double limit in `r` then `N`, `ε`-managed).

## This file

`digitOf_pow_eq_blockNatVal`: the digit-correspondence foundation — the
`q`-th base-`b^r` digit of `x` equals the big-endian value of the `r`
base-`b` digits of `x` at positions `[r·q, r·q+r)`. Everything above builds
on this; the full assembly is future work (`PENDING_WORK.md`).
-/

namespace NormalNumbers

/-- **Digit-power correspondence**: the `q`-th base-`b^r` digit of `x` is
exactly the big-endian value of the `r` consecutive base-`b` digits of `x`
at positions `[r·q, r·q + r)`. The bridge between simple normality at a
composite base `b^r` and block frequency at base `b` (Pillai's theorem). -/
theorem digitOf_pow_eq_blockNatVal (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r)
    (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) (q : ℕ) :
    digitOf (b ^ r) y q
      = blockNatVal b (List.ofFn fun i : Fin r => digitOf b y (r * q + i)) := by
  have hbr2 : 2 ≤ b ^ r := by calc 2 ≤ b := hb
      _ ≤ b ^ r := Nat.le_self_pow (by omega) b
  set w : List ℕ := List.ofFn fun i : Fin r => digitOf b y (r * q + i) with hwdef
  have hwlen : w.length = r := List.length_ofFn
  have hwlt : ∀ d ∈ w, d < b := by
    intro d hd
    rw [hwdef] at hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact digitOf_lt b hb y _
  have hwval : blockNatVal b w < b ^ r := by
    have := blockNatVal_lt b w hwlt
    rwa [hwlen] at this
  -- expand `⌊y·b^{r(q+1)}⌋` in base `b`, split the sum at `r·q`
  have hexp : (r * (q + 1)) = r * q + r := by ring
  have hfloor := floor_eq_digitVal b hb y hy (r * (q + 1))
  rw [hexp] at hfloor
  rw [Finset.sum_range_add] at hfloor
  -- the low part (`j < r·q`) is divisible by `b^r`
  have hlowdvd : (b : ℤ) ^ r ∣ ∑ j ∈ Finset.range (r * q),
      (digitOf b y j : ℤ) * (b : ℤ) ^ (r * q + r - 1 - j) := by
    apply Finset.dvd_sum
    intro j hj
    have hjrq : j < r * q := Finset.mem_range.mp hj
    have hge : r ≤ r * q + r - 1 - j := by omega
    exact Dvd.dvd.mul_left (pow_dvd_pow (b : ℤ) hge) _
  -- the high part (`j = r·q + i`, `i < r`) is exactly `blockNatVal b w`
  have hhigh : ∑ i ∈ Finset.range r,
      (digitOf b y (r * q + i) : ℤ) * (b : ℤ) ^ (r * q + r - 1 - (r * q + i))
      = (blockNatVal b w : ℤ) := by
    have hsum := blockNatVal_eq_sum b w
    rw [hwlen] at hsum
    have heq2 : (blockNatVal b w : ℤ)
        = ∑ i ∈ Finset.range r, (w.getD i 0 : ℤ) * (b : ℤ) ^ (r - 1 - i) := by
      exact_mod_cast hsum
    rw [heq2]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hir : i < r := Finset.mem_range.mp hi
    have hgetD : w.getD i 0 = digitOf b y (r * q + i) := by
      rw [hwdef, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hir]
    rw [hgetD]
    congr 2
    omega
  rw [hhigh] at hfloor
  -- assemble: `⌊y·b^{r(q+1)}⌋ = (mult of b^r) + blockNatVal b w`, `blockNatVal b w < b^r`
  have hy0 : (0:ℝ) ≤ y := hy.1
  have hfloornn : 0 ≤ ⌊y * (b:ℝ) ^ (r * (q + 1))⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  unfold digitOf
  have hcast : ((b ^ r : ℕ) : ℝ) ^ (q + 1) = (b:ℝ) ^ (r * q + r) := by
    push_cast
    rw [← pow_mul, hexp]
  rw [hcast]
  obtain ⟨c, hc⟩ := hlowdvd
  rw [hc] at hfloor
  have hfloor' : ⌊y * (b:ℝ) ^ (r * q + r)⌋ = (b:ℤ) ^ r * c + (blockNatVal b w : ℤ) := hfloor
  rw [hfloor']
  have hsumnn : 0 ≤ ∑ j ∈ Finset.range (r * q),
      (digitOf b y j : ℤ) * (b : ℤ) ^ (r * q + r - 1 - j) := by positivity
  rw [hc] at hsumnn
  have hbrpos : (0:ℤ) < (b:ℤ) ^ r := by positivity
  have hcnn : 0 ≤ c := by nlinarith [hsumnn, hbrpos]
  have htoNat : ((b:ℤ) ^ r * c + (blockNatVal b w : ℤ)).toNat
      = b ^ r * c.toNat + blockNatVal b w := by
    have h1 : (0:ℤ) ≤ (b:ℤ) ^ r * c := by positivity
    have h2 : (0:ℤ) ≤ (blockNatVal b w : ℤ) := by positivity
    have hceq : c = (c.toNat : ℤ) := (Int.toNat_of_nonneg hcnn).symm
    rw [Int.toNat_add h1 h2]
    congr 1
    rw [hceq, ← Nat.cast_pow, ← Nat.cast_mul]
    exact Int.toNat_natCast (b ^ r * c.toNat)
  rw [htoNat, Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt hwval

end NormalNumbers
