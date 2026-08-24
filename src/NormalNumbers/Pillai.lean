/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.DigitInterval
import NormalNumbers.DaryDigits

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

/-- **Phase-decomposition**: the `s`-th base-`b` digit (big-endian, `s < r`)
of `c_q := digitOf (b^r) y q` is exactly the base-`b` digit of `y` at real
position `r*q+s`. The atomic correspondence underlying Pillai's theorem: a
base-`b^r` "digit" `c_q` is itself an `r`-digit base-`b` block, and its
`s`-th sub-digit is literally the `(r*q+s)`-th base-`b` digit of `y`. -/
theorem digitOf_pow_digitAt (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r)
    (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) (q s : ℕ) (hs : s < r) :
    digitOf (b ^ r) y q / b ^ (r - 1 - s) % b = digitOf b y (r * q + s) := by
  set w : List ℕ := List.ofFn fun i : Fin r => digitOf b y (r * q + i) with hwdef
  have hwlen : w.length = r := List.length_ofFn
  have hwlt : ∀ d ∈ w, d < b := by
    intro d hd
    rw [hwdef] at hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact digitOf_lt b hb y _
  have hgetD : w.getD s 0 = digitOf b y (r * q + s) := by
    rw [hwdef, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hs]
  have hq' := digitOf_pow_eq_blockNatVal b r hb hr y hy q
  rw [← hwdef] at hq'
  rw [hq']
  have hs' : s < w.length := by rw [hwlen]; exact hs
  have := blockNatVal_digit b w hwlt s hs'
  rw [hwlen] at this
  rw [this, hgetD]

/-- **Slice extraction**: the value of the length-`L` slice `w[s, s+L)` of a
digit block `w` is `blockNatVal b w` shifted right by `(len−s−L)` places and
masked to `L` digits. Generalizes `blockNatVal_digit` (the `L = 1` case)
from a single digit to an arbitrary contiguous sub-block. Pure list/nat
arithmetic, digit-independent — the combinatorial core of the
non-straddling window/slice correspondence in Pillai's theorem. -/
theorem blockNatVal_slice (b : ℕ) :
    ∀ (w : List ℕ), (∀ a ∈ w, a < b) → ∀ s L, s + L ≤ w.length →
      blockNatVal b w / b ^ (w.length - s - L) % b ^ L
        = blockNatVal b ((w.drop s).take L) := by
  intro w
  induction w with
  | nil =>
    intro _ s L hsL
    simp only [List.length_nil, Nat.le_zero, Nat.add_eq_zero_iff] at hsL
    obtain ⟨rfl, rfl⟩ := hsL
    simp [blockNatVal]
  | cons d w ih =>
    intro hw s L hsL
    have hbpos : 0 < b := lt_of_le_of_lt (Nat.zero_le d) (hw d List.mem_cons_self)
    rcases s with _ | s'
    · rcases L with _ | L'
      · simp [Nat.mod_one, blockNatVal]
      · have hL'w : L' ≤ w.length := by
          simp only [List.length_cons] at hsL; omega
        simp only [List.drop_zero]
        have htake : (d :: w).take (L' + 1) = d :: w.take L' := by simp
        rw [htake]
        have htklen : (w.take L').length = L' := by
          rw [List.length_take]; omega
        conv_rhs => rw [blockNatVal_cons]
        rw [blockNatVal_cons, htklen]
        have hlen1 : (d :: w).length - 0 - (L' + 1) = w.length - L' := by
          simp only [List.length_cons]; omega
        rw [hlen1]
        have hpow : b ^ w.length = b ^ (w.length - L') * b ^ L' := by
          rw [← pow_add]; congr 1; omega
        have hd : d * b ^ w.length = d * b ^ L' * b ^ (w.length - L') := by
          rw [hpow]; ring
        rw [hd, Nat.add_comm (d * b ^ L' * b ^ (w.length - L')),
          Nat.add_mul_div_right _ _ (pow_pos hbpos _)]
        have hVlt : blockNatVal b w < b ^ w.length :=
          blockNatVal_lt b w (fun a ha => hw a (List.mem_cons_of_mem d ha))
        have hlt1 : blockNatVal b w / b ^ (w.length - L') < b ^ L' := by
          rw [hpow] at hVlt
          exact Nat.div_lt_of_lt_mul hVlt
        have hdlt : d < b := hw d List.mem_cons_self
        have hpow2 : b ^ (L' + 1) = b * b ^ L' := by ring
        have hstep : (d + 1) * b ^ L' ≤ b * b ^ L' :=
          Nat.mul_le_mul_right (b ^ L') (by omega)
        have hsum_lt : d * b ^ L' + blockNatVal b w / b ^ (w.length - L') < b ^ (L' + 1) := by
          rw [hpow2]; nlinarith
        have hIH := ih (fun a ha => hw a (List.mem_cons_of_mem d ha)) 0 L' (by omega)
        simp only [Nat.sub_zero, List.drop_zero] at hIH
        rw [Nat.mod_eq_of_lt hlt1] at hIH
        rw [show blockNatVal b w / b ^ (w.length - L') + d * b ^ L'
              = d * b ^ L' + blockNatVal b w / b ^ (w.length - L') from by ring,
          Nat.mod_eq_of_lt hsum_lt, hIH]
    · simp only [List.length_cons] at hsL
      have hs'L : s' + L ≤ w.length := by omega
      have hdrop : (d :: w).drop (s' + 1) = w.drop s' := rfl
      rw [hdrop]
      have hlen2 : (d :: w).length - (s' + 1) - L = w.length - s' - L := by
        simp only [List.length_cons]; omega
      rw [hlen2, blockNatVal_cons]
      have hpow2 : b ^ w.length = b ^ (w.length - s' - L) * b ^ (s' + L) := by
        rw [← pow_add]; congr 1; omega
      have hd2 : d * b ^ w.length = d * b ^ s' * b ^ L * b ^ (w.length - s' - L) := by
        rw [hpow2, pow_add]; ring
      rw [hd2, Nat.add_comm (d * b ^ s' * b ^ L * b ^ (w.length - s' - L)) (blockNatVal b w),
        Nat.add_mul_div_right _ _ (pow_pos hbpos _), Nat.add_mul_mod_self_right]
      exact ih (fun a ha => hw a (List.mem_cons_of_mem d ha)) s' L hs'L

/-- **Non-straddling window correspondence** (Pillai's theorem, phase-`s`
case): for `s + L ≤ r`, a length-`L` window of `y`'s base-`b` digits at
`[r*q+s, r*q+s+L)` equals `w` iff the `L`-digit slice `[s,s+L)` of `c_q`'s
`r`-digit base-`b` expansion equals `w` — i.e. iff `c_q`'s value shifted
right by `r-s-L` and masked to `L` digits equals `blockNatVal b w`. This
turns "window frequency at phase `s`" into "digit-value frequency at base
`b^r`", the bridge simple normality at `b^r` acts on. -/
theorem digitOf_pow_slice_eq_blockNatVal (b r L s q : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r)
    (hL : s + L ≤ r) (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    digitOf (b ^ r) y q / b ^ (r - s - L) % b ^ L
      = blockNatVal b (List.ofFn fun i : Fin L => digitOf b y (r * q + s + i)) := by
  have hq' := digitOf_pow_eq_blockNatVal b r hb hr y hy q
  have hwlt : ∀ d ∈ (List.ofFn fun i : Fin r => digitOf b y (r * q + i)), d < b := by
    intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact digitOf_lt b hb y _
  have hslice := blockNatVal_slice b (List.ofFn fun i : Fin r => digitOf b y (r * q + i))
    hwlt s L (by rw [List.length_ofFn]; omega)
  rw [List.length_ofFn] at hslice
  rw [hq', hslice]
  congr 1
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, List.length_ofFn]; omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    simp only [Fin.val_mk]
    congr 1
    omega

/-- **Matching-value count**: among `c ∈ [0, b^r)`, exactly `b^(r−L)` values
have `c` (shifted right by `r−s−L`, masked to `L` digits) equal to a fixed
target `V < b^L`. Combinatorial fact underlying Pillai's frequency count:
fixing an `L`-digit slice of an `r`-digit base-`b` number leaves `b^(r−L)`
free choices for the remaining digits. Proved via the bijection
`c ↔ (c / D / b^L, c % D)` with `D := b^(r−s−L)`, splitting the free
digits into a length-`s` prefix and length-`(r−s−L)` suffix around the
fixed slice. -/
theorem card_matchingValues (b r L s V : ℕ) (hb : 2 ≤ b) (hL : s + L ≤ r)
    (hV : V < b ^ L) :
    ((Finset.range (b ^ r)).filter (fun c => c / b ^ (r - s - L) % b ^ L = V)).card
      = b ^ (r - L) := by
  set D : ℕ := b ^ (r - s - L) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hLpos : 0 < b ^ L := by positivity
  have hexp : b ^ r = b ^ s * b ^ L * D := by
    rw [hDdef, ← pow_add, ← pow_add]; congr 1; omega
  have hcard : (Finset.range (b ^ s) ×ˢ Finset.range D).card = b ^ (r - L) := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range, hDdef, ← pow_add]
    congr 1
    omega
  rw [← hcard]
  apply Finset.card_nbij' (fun c => (c / D / b ^ L, c % D))
    (fun p => (p.1 * b ^ L + V) * D + p.2)
  · intro c hc
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hc
    obtain ⟨hcr, hcmod⟩ := hc
    simp only [Finset.coe_product, Finset.mem_coe, Finset.mem_range, Set.mem_prod]
    refine ⟨?_, Nat.mod_lt _ hDpos⟩
    have hcD : c / D < b ^ s * b ^ L := by
      rw [Nat.div_lt_iff_lt_mul hDpos, ← hexp]; exact hcr
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hcD)
  · rintro ⟨k, t⟩ hkt
    simp only [Finset.coe_product, Finset.mem_coe, Finset.mem_range, Set.mem_prod] at hkt
    obtain ⟨hk, ht⟩ := hkt
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    have h1 : k * b ^ L + V < b ^ s * b ^ L := by
      have hstep : (k + 1) * b ^ L ≤ b ^ s * b ^ L := Nat.mul_le_mul_right (b ^ L) hk
      nlinarith
    refine ⟨?_, ?_⟩
    · calc (k * b ^ L + V) * D + t
          < (k * b ^ L + V + 1) * D := by nlinarith [ht]
        _ ≤ (b ^ s * b ^ L) * D := Nat.mul_le_mul_right D h1
        _ = b ^ r := by rw [hexp]
    · have hdiv : (k * b ^ L + V) * D + t = D * (k * b ^ L + V) + t := by ring
      rw [hdiv, Nat.mul_add_div hDpos, Nat.div_eq_of_lt ht, Nat.add_zero,
        Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hV]
  · intro c hc
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hc
    obtain ⟨hcr, hcmod⟩ := hc
    have hkey : c / D = c / D / b ^ L * b ^ L + V := by
      conv_lhs => rw [← Nat.div_add_mod (c / D) (b ^ L)]
      rw [hcmod, Nat.mul_comm]
    show (c / D / b ^ L * b ^ L + V) * D + c % D = c
    rw [← hkey, Nat.mul_comm, Nat.div_add_mod]
  · rintro ⟨k, t⟩ hkt
    simp only [Finset.coe_product, Finset.mem_coe, Finset.mem_range, Set.mem_prod] at hkt
    obtain ⟨hk, ht⟩ := hkt
    have hdiv : (k * b ^ L + V) * D + t = D * (k * b ^ L + V) + t := by ring
    have heq1 : ((k * b ^ L + V) * D + t) / D = k * b ^ L + V := by
      rw [hdiv, Nat.mul_add_div hDpos, Nat.div_eq_of_lt ht, Nat.add_zero]
    have heq2 : ((k * b ^ L + V) * D + t) % D = t := by
      rw [hdiv, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt ht
    have hdiv2 : (k * b ^ L + V) / b ^ L = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hLpos, Nat.div_eq_of_lt hV, Nat.zero_add]
    dsimp only
    rw [heq1, heq2, hdiv2]

/-- **Window-match ↔ matching-value membership**: for `q < Q`, the phase-`s`
window of `y`'s base-`b` digits at `q` equals `w` iff `digitOf (b^r) y q`
lies in the finite "matching values" set — the bridge that turns a window
count into a digit-value count at base `b^r`. -/
theorem count_windowMatch_eq_count_matchingValues (b r L s : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r)
    (hL : s + L ≤ r) (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) (w : List ℕ)
    (hwlen : w.length = L) (hwlt : ∀ d ∈ w, d < b) (Q : ℕ) :
    ((Finset.range Q).filter
        (fun q => List.ofFn (fun i : Fin L => digitOf b y (r * q + s + i)) = w)).card
      = ((Finset.range Q).filter
          (fun q => digitOf (b ^ r) y q / b ^ (r - s - L) % b ^ L = blockNatVal b w)).card := by
  congr 1
  apply Finset.filter_congr
  intro q _
  rw [digitOf_pow_slice_eq_blockNatVal b r L s q hb hr hL y hy]
  constructor
  · intro h; rw [h]
  · intro h
    have hwlt' : ∀ d ∈ List.ofFn fun i : Fin L => digitOf b y (r * q + s + i), d < b := by
      intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact digitOf_lt b hb y _
    exact blockNatVal_inj b (by omega) _ w (by rw [List.length_ofFn, hwlen]) hwlt' hwlt h

/-- **Phase-`s` window frequency, from simple normality at base `b^r`**:
if every digit value `c < b^r` occurs with frequency `→ 1/b^r` among the
first `Q` base-`b^r` digits of `y` (simple normality at `b^r`), then the
length-`L` window `w` occurs at phase `s` (`s+L≤r`) with frequency
`→ 1/b^L` among the first `Q` base-`b^r` positions. Combines
`count_windowMatch_eq_count_matchingValues` (window count = digit-value
count) with `card_matchingValues` (`b^(r-L)` matching values) via
`Finset.card_eq_sum_card_fiberwise` + `tendsto_finsetSum`. -/
theorem phaseWindowFreq_tendsto (b r L s : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r)
    (hL : s + L ≤ r) (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) (w : List ℕ)
    (hwlen : w.length = L) (hwlt : ∀ d ∈ w, d < b)
    (hsn : ∀ c < b ^ r, Filter.Tendsto
        (fun Q : ℕ => (((Finset.range Q).filter (fun q => digitOf (b ^ r) y q = c)).card : ℝ) / Q)
        Filter.atTop (nhds ((b : ℝ) ^ r)⁻¹)) :
    Filter.Tendsto
      (fun Q : ℕ => (((Finset.range Q).filter
          (fun q => List.ofFn (fun i : Fin L => digitOf b y (r * q + s + i)) = w)).card : ℝ) / Q)
      Filter.atTop (nhds ((b : ℝ) ^ L)⁻¹) := by
  have hVlt : blockNatVal b w < b ^ L := by
    have := blockNatVal_lt b w hwlt
    rwa [hwlen] at this
  set V : ℕ := blockNatVal b w with hVdef
  set mV : Finset ℕ := (Finset.range (b ^ r)).filter (fun c => c / b ^ (r - s - L) % b ^ L = V)
    with hmVdef
  have hmVcard : mV.card = b ^ (r - L) := card_matchingValues b r L s V hb hL hVlt
  have hbr2 : 2 ≤ b ^ r := le_trans hb (Nat.le_self_pow (by omega) b)
  have hcount_eq : ∀ Q, ((Finset.range Q).filter
      (fun q => List.ofFn (fun i : Fin L => digitOf b y (r * q + s + i)) = w)).card
      = ∑ c ∈ mV, ((Finset.range Q).filter (fun q => digitOf (b ^ r) y q = c)).card := by
    intro Q
    rw [count_windowMatch_eq_count_matchingValues b r L s hb hr hL y hy w hwlen hwlt Q]
    have hstep : ((Finset.range Q).filter (fun q => digitOf (b ^ r) y q ∈ mV)).card
        = ∑ c ∈ mV, ((Finset.range Q).filter (fun q => digitOf (b ^ r) y q = c)).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (s := (Finset.range Q).filter (fun q => digitOf (b ^ r) y q ∈ mV))
        (t := mV) (f := fun q => digitOf (b ^ r) y q)
        (fun q hq => (Finset.mem_filter.mp hq).2)]
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨ha, _⟩, hfa⟩; exact ⟨ha, hfa⟩
      · rintro ⟨ha, hfa⟩; exact ⟨⟨ha, hfa ▸ hc⟩, hfa⟩
    rw [← hstep]
    congr 1
    apply Finset.filter_congr
    intro q _
    simp only [hmVdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨digitOf_lt (b ^ r) hbr2 y q, h⟩, fun h => h.2⟩
  have hfun_eq : (fun Q : ℕ => (((Finset.range Q).filter
        (fun q => List.ofFn (fun i : Fin L => digitOf b y (r * q + s + i)) = w)).card : ℝ) / Q)
      = fun Q : ℕ => ∑ c ∈ mV,
          (((Finset.range Q).filter (fun q => digitOf (b ^ r) y q = c)).card : ℝ) / Q := by
    funext Q
    rw [hcount_eq Q]
    push_cast
    rw [Finset.sum_div]
  rw [hfun_eq]
  have hlim : Filter.Tendsto
      (fun Q : ℕ => ∑ c ∈ mV,
        (((Finset.range Q).filter (fun q => digitOf (b ^ r) y q = c)).card : ℝ) / Q)
      Filter.atTop (nhds (∑ _c ∈ mV, ((b : ℝ) ^ r)⁻¹)) := by
    apply tendsto_finsetSum
    intro c hc
    exact hsn c (Finset.mem_range.mp (Finset.mem_filter.mp hc).1)
  have hval : (∑ _c ∈ mV, ((b : ℝ) ^ r)⁻¹) = ((b : ℝ) ^ L)⁻¹ := by
    rw [Finset.sum_const, hmVcard]
    have hbpos : (0 : ℝ) < b := by positivity
    have hsplit : (b : ℝ) ^ r = (b : ℝ) ^ L * (b : ℝ) ^ (r - L) := by
      rw [← pow_add]; congr 1; omega
    rw [nsmul_eq_mul, Nat.cast_pow, hsplit]
    have hLpos : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have hrLpos : (0 : ℝ) < (b : ℝ) ^ (r - L) := by positivity
    field_simp
  rwa [hval] at hlim

/-- **Straddling-phase count**: among the `r` phases `s ∈ [0,r)`, exactly
`L-1` are "straddling" (`s + L > r`, i.e. the length-`L` window at that
phase crosses a base-`b^r` digit boundary rather than sitting inside one).
Density `(L-1)/r → 0` as `r → ∞` — this bounds the error from discarding
straddling phases in Pillai's assembly. -/
theorem card_straddling_phases (r L : ℕ) (hL1 : 1 ≤ L) (hLr : L ≤ r) :
    ((Finset.range r).filter (fun s => r < s + L)).card = L - 1 := by
  have hset : (Finset.range r).filter (fun s => r < s + L) = Finset.Ico (r - L + 1) r := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]
  omega

/-- The number of valid phase-`s` occurrences within `[0, N)`: values `q`
with `r*q + s + L ≤ N`, i.e. `q < (N - s - L)/r + 1` when `s ≤ N - L`
(else there are none). The bridge between the `Q`-scale (index into the
base-`b^r` digit sequence) used by `phaseWindowFreq_tendsto` and the
`N`-scale (real base-`b` digit position) used by `IsNormalSequence`. -/
def phaseOccCount (r L s N : ℕ) : ℕ :=
  if h : s + L ≤ N then (N - s - L) / r + 1 else 0

/-- **Real-position window count, decomposed by phase**: the number of
start positions `i` with `i + L ≤ N` where the base-`b` digit window of
`y` matches `w` equals the sum, over the `r` phases `s < r`, of the
phase-`s` window-match count among `q < phaseOccCount r L s N`. Pure
combinatorics (an `i ↔ (i/r, i%r)` bijection, same flavor as
`card_matchingValues`'s bijection) — no limits involved. This is the exact
identity Pillai's final assembly divides through by `N` and takes `N → ∞`
(phase-by-phase, via `phaseWindowFreq_tendsto`) then `r → ∞` (discarding
the `card_straddling_phases`-many straddling phases).

**Status (disclosed `sorry`, next lap's target)**: this identity plus the
subsequent `N → ∞, r → ∞` double-limit ε-management are the last
obligations for Pillai's theorem. The two already-proved ingredients
(`phaseWindowFreq_tendsto`, `card_straddling_phases`) are exactly what
this identity needs downstream to make the final assembly go through —
see the file docstring for the full route. -/
theorem windowCount_eq_sum_phaseCount (b r L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (y : ℝ) (w : List ℕ) (hwlen : w.length = L) (N : ℕ) :
    ((Finset.range (N + 1)).filter
        (fun i => i + L ≤ N ∧ List.ofFn (fun j : Fin L => digitOf b y (i + j)) = w)).card
      = ∑ s ∈ Finset.range r, ((Finset.range (phaseOccCount r L s N)).filter
          (fun q => List.ofFn (fun i : Fin L => digitOf b y (r * q + s + i)) = w)).card := by
  have hrpos : 0 < r := by omega
  rw [Finset.card_eq_sum_card_fiberwise
      (s := (Finset.range (N + 1)).filter
        (fun i => i + L ≤ N ∧ List.ofFn (fun j : Fin L => digitOf b y (i + j)) = w))
      (t := Finset.range r) (f := fun i => i % r)
      (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i hrpos))]
  apply Finset.sum_congr rfl
  intro s hs
  have hsr : s < r := Finset.mem_range.mp hs
  have hfiber_eq : ((Finset.range (N + 1)).filter
        (fun i => i + L ≤ N ∧ List.ofFn (fun j : Fin L => digitOf b y (i + j)) = w)).filter
        (fun i => i % r = s)
      = (Finset.range (N + 1)).filter
        (fun i => i + L ≤ N ∧ List.ofFn (fun j : Fin L => digitOf b y (i + j)) = w ∧ i % r = s) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  rw [hfiber_eq]
  -- Bijection `i ↔ i/r` between the flat fiber filter (fixed `i%r=s`) and the
  -- phase-`s` occurrence filter, via `i = r*(i/r)+s`.  Canonical decomposition
  -- is `Nat.div_add_mod i r : r*(i/r)+i%r = i` (factor order `r*(i/r)`); the one
  -- place `Nat.le_div_iff_mul_le` produces `(i/r)*r` is normalized back with an
  -- explicit `Nat.mul_comm`.
  apply Finset.card_nbij' (fun i => i / r) (fun q => r * q + s)
  · -- forward MapsTo: `i ↦ i/r` lands in the phase-`s` occurrence filter
    intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
    obtain ⟨_hiN1, hiN, hwin, hmod⟩ := hi
    have hqi : r * (i / r) + s = i := by rw [← hmod]; exact Nat.div_add_mod i r
    have hsLN : s + L ≤ N := by omega
    have hPO : phaseOccCount r L s N = (N - s - L) / r + 1 := by
      unfold phaseOccCount; exact dif_pos hsLN
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · have hle : i / r ≤ (N - s - L) / r := by
        rw [Nat.le_div_iff_mul_le hrpos, Nat.mul_comm]
        omega
      rw [hPO]; omega
    · rw [hqi]; exact hwin
  · -- backward MapsTo: `q ↦ r*q+s` lands in the flat fiber filter
    intro q hq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hq
    obtain ⟨hqP, hwin⟩ := hq
    have hsLN : s + L ≤ N := by
      by_contra h
      have h0 : phaseOccCount r L s N = 0 := by unfold phaseOccCount; exact dif_neg h
      omega
    have hPO : phaseOccCount r L s N = (N - s - L) / r + 1 := by
      unfold phaseOccCount; exact dif_pos hsLN
    rw [hPO] at hqP
    have hqle : q ≤ (N - s - L) / r := by omega
    have hmul : r * q ≤ N - s - L := by
      have h := (Nat.le_div_iff_mul_le hrpos).mp hqle
      rwa [Nat.mul_comm] at h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨?_, ?_, hwin, ?_⟩
    · omega
    · omega
    · rw [Nat.add_comm (r * q) s, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsr]
  · -- left inverse: `r*(i/r)+s = i` on the fiber
    intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
    obtain ⟨_hiN1, _hiN, _hwin, hmod⟩ := hi
    show r * (i / r) + s = i
    rw [← hmod]; exact Nat.div_add_mod i r
  · -- right inverse: `(r*q+s)/r = q`
    intro q _hq
    show (r * q + s) / r = q
    rw [Nat.mul_add_div hrpos, Nat.div_eq_of_lt hsr, Nat.add_zero]

end NormalNumbers
