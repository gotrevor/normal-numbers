/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.DigitInterval

/-!
# Disjunctivity: the topological twin of Wall's theorem (Track D, brick D0)

Companion to `docs/conditional-disjunctivity.md` §0 ("the orbit dictionary").
Where `IsNormal b x` asks for the multiply-by-`b` orbit `n ↦ bⁿ·x mod 1` to be
*equidistributed* mod 1 (Wall's theorem), **disjunctivity** asks only for the
orbit to be *dense* in `[0,1)`.  Equivalently, every finite base-`b` block occurs
somewhere in the expansion of `x` (density ⟺ every cylinder is visited).

This module is deliberately elementary and self-contained: it introduces
`IsDisjunctive` in the interval-visit form directly analogous to `Equidistributed`,
bridges it to occurrence of every finite digit word, records the dense-orbit
equivalence, and proves invariance under replacing `b` by a positive power.
Nothing here depends on the CF or Khinchin machinery; it sits beside `Wall.lean`.
-/

namespace NormalNumbers

open Filter Set

/-- The multiply-by-`b` orbit only sees the fractional part of `x` (local copy of
`Wall.orbit_fract`, kept here to avoid importing the full Wall stack). -/
theorem orbit_fract (b : ℕ) (x : ℝ) (n : ℕ) :
    orbit b (Int.fract x) n = orbit b x n := by
  unfold orbit
  have h : Int.fract x * (b : ℝ) ^ n
      = x * (b : ℝ) ^ n - ((⌊x⌋ * (b ^ n : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]

/-- The multiply-by-`b` orbit always lands in `[0,1)` — it is a fractional part. -/
theorem orbit_mem_Ico (b : ℕ) (x : ℝ) (n : ℕ) : orbit b x n ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **Disjunctive in base `b`** (interval-visit form).  Every subinterval
`[a, c) ⊆ [0, 1)` is visited by the multiply-by-`b` orbit `n ↦ bⁿ·x mod 1`.
This is the topological weakening of `Equidistributed (orbit b x)`: the latter
pins the *frequency* of every subinterval, the former only its non-emptiness of
visits.  As with `IsNormal`, the property only sees `Int.fract x`
(`isDisjunctive_fract`). -/
def IsDisjunctive (b : ℕ) (x : ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 → ∃ n, orbit b x n ∈ Set.Ico a c

/-- A real is **absolutely disjunctive** when it is disjunctive in every
integer base `b ≥ 2`. -/
def AbsolutelyDisjunctive (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsDisjunctive b x

/-- The finite word `w` occurs at position `n` in the canonical base-`b`
expansion of the fractional part of `x`. -/
def OccursAt (b : ℕ) (x : ℝ) (w : List ℕ) (n : ℕ) : Prop :=
  ∀ j (hj : j < w.length), digitOf b (Int.fract x) (n + j) = w[j]

/-- The orbit only sees the fractional part, so disjunctivity is a property of
`Int.fract x`. -/
theorem isDisjunctive_fract (b : ℕ) (x : ℝ) :
    IsDisjunctive b (Int.fract x) ↔ IsDisjunctive b x := by
  simp only [IsDisjunctive]
  have key : ∀ n, orbit b (Int.fract x) n = orbit b x n := orbit_fract b x
  constructor
  · intro h a c ha hac hc
    obtain ⟨n, hn⟩ := h a c ha hac hc
    rw [key] at hn; exact ⟨n, hn⟩
  · intro h a c ha hac hc
    obtain ⟨n, hn⟩ := h a c ha hac hc
    rw [← key] at hn; exact ⟨n, hn⟩

/-- A word occurs at position `n` exactly when the `n`-th orbit point lies
in the word's b-adic cylinder. -/
theorem occursAt_iff_orbit_mem (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) (n : ℕ) :
    OccursAt b x w n ↔ orbit b x n ∈
      Set.Ico ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length)
        (((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length) := by
  have hx : Int.fract x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have horb : orbit b (Int.fract x) n ∈ Set.Ico (0 : ℝ) 1 :=
    orbit_mem_Ico b (Int.fract x) n
  rw [← orbit_fract b x n, ← digits_prefix_iff b hb _ horb w hw]
  constructor
  · intro h j hj
    rw [digitOf_orbit b hb (Int.fract x) hx.1 n j, h j hj]
  · intro h j hj
    rw [← digitOf_orbit b hb (Int.fract x) hx.1 n j, h j hj]

/-- **Disjunctivity is the dense-orbit condition** (the topological twin of
Wall's theorem).  `x` is disjunctive in base `b` iff every point of `[0,1)` is a
limit of orbit points, i.e. `[0,1) ⊆ closure {bⁿ·x mod 1 : n}`.

Since the orbit is contained in `[0,1)` (`orbit_mem_Ico`), this says exactly that
the orbit is dense in the endpoint-identified unit interval.  In the ambient
real line its closure is `[0,1]`; an ω-limit formulation should therefore use
the circle, not claim equality with the nonclosed set `[0,1)`. -/
theorem isDisjunctive_iff_denseOrbit (b : ℕ) (x : ℝ) :
    IsDisjunctive b x ↔ Set.Ico (0 : ℝ) 1 ⊆ closure (Set.range (orbit b x)) := by
  constructor
  · -- disjunctive ⟹ dense: shrink to a half-open interval `[y, min 1 (y+ε))`.
    intro hdisj y hy
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := hdisj y (min 1 (y + ε)) hy.1
      (lt_min hy.2 (by linarith)) (min_le_left _ _)
    refine ⟨orbit b x n, ⟨n, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hlo : y ≤ orbit b x n := hn.1
    have hhi : orbit b x n < y + ε := lt_of_lt_of_le hn.2 (min_le_right _ _)
    exact ⟨by linarith, by linarith⟩
  · -- dense ⟹ disjunctive: aim at the midpoint of `[a, c)` with radius `(c-a)/2`.
    intro hdense a c ha hac hc
    set y : ℝ := (a + c) / 2 with hy
    have hya : a < y := by rw [hy]; linarith
    have hyc : y < c := by rw [hy]; linarith
    have hymem : y ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt (lt_of_le_of_lt ha hya),
      lt_of_lt_of_le hyc hc⟩
    have := hdense hymem
    rw [Metric.mem_closure_iff] at this
    obtain ⟨z, hzrange, hz⟩ := this ((c - a) / 2) (by linarith)
    obtain ⟨n, rfl⟩ := hzrange
    rw [Real.dist_eq, abs_lt] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [hy] at hz1 hz2
    have hlow : a < orbit b x n := by linarith [hz2]
    have hhigh : orbit b x n < c := by linarith [hz1]
    exact ⟨n, le_of_lt hlow, hhigh⟩

/-- **Word-occurrence characterization of disjunctivity.**  A real is
disjunctive in base `b` iff every finite word over the digits `< b` occurs in
its canonical base-`b` expansion.  The empty word is harmless on both sides. -/
theorem isDisjunctive_iff_forall_occursAt (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    IsDisjunctive b x ↔
      ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ n, OccursAt b x w n := by
  constructor
  · intro hdisj w hw
    have hval : blockNatVal b w < b ^ w.length := blockNatVal_lt b w hw
    have hpow : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
    have ha : (0 : ℝ) ≤ (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length := by
      positivity
    have hac : (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length <
        ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length := by
      rw [div_lt_div_iff₀ hpow hpow]
      nlinarith
    have hc : ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length ≤ 1 := by
      rw [div_le_one hpow]
      exact_mod_cast Nat.succ_le_of_lt hval
    obtain ⟨n, hn⟩ := hdisj _ _ ha hac hc
    exact ⟨n, (occursAt_iff_orbit_mem b hb x w hw n).2 hn⟩
  · intro hall
    rw [isDisjunctive_iff_denseOrbit]
    intro y hy
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hbR : (1 : ℝ) < b := by exact_mod_cast hb
    have hbase : (1 / (b : ℝ)) < 1 := (div_lt_one (by positivity)).2 hbR
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hbase
    set w : List ℕ := List.ofFn fun i : Fin k => digitOf b y i with hwdef
    have hlen : w.length = k := by simp [hwdef]
    have hw : ∀ d ∈ w, d < b := by
      intro d hd
      rw [hwdef, List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact digitOf_lt b hb y i
    have hyprefix : ∀ j (hj : j < w.length), digitOf b y j = w[j] := by
      intro j hj
      simp [hwdef]
    have hycell := (digits_prefix_iff b hb y hy w hw).1 hyprefix
    obtain ⟨n, hn⟩ := hall w hw
    have hncell := (occursAt_iff_orbit_mem b hb x w hw n).1 hn
    refine ⟨orbit b x n, ⟨n, rfl⟩, ?_⟩
    have hwidth :
        ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length -
            (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length =
          (1 / (b : ℝ)) ^ k := by
      rw [div_sub_div_same]
      simp only [add_sub_cancel_left, one_div, inv_pow, hlen]
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : orbit b x n - y < ε := by
        calc
          orbit b x n - y <
              ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length -
                (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length := by
                  linarith [hncell.2, hycell.1]
          _ = (1 / (b : ℝ)) ^ k := hwidth
          _ < ε := hk
      linarith
    · calc
        y - orbit b x n <
            ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length -
              (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length := by
                linarith [hycell.2, hncell.1]
        _ = (1 / (b : ℝ)) ^ k := hwidth
        _ < ε := hk

/-- Taking every `k`-th point of the base-`b` orbit gives the base-`b^k`
orbit. -/
theorem orbit_pow (b k : ℕ) (x : ℝ) (n : ℕ) :
    orbit (b ^ k) x n = orbit b x (k * n) := by
  unfold orbit
  congr 1
  push_cast
  rw [pow_mul]

/-! The hard direction of base-power invariance is a finite alignment trick.
For a base-`b` word `u` of length divisible by `k`, ask for `k + 1` copies of
`u`, separated by one zero.  Their starting positions advance by
`u.length + 1 ≡ 1 (mod k)`, so one copy starts at a multiple of `k`. -/

private def alignmentWord (copies : ℕ) (u : List ℕ) : List ℕ :=
  List.ofFn fun i : Fin (copies * (u.length + 1)) =>
    if h : i.val % (u.length + 1) < u.length then
      u[i.val % (u.length + 1)]
    else 0

private theorem length_alignmentWord (copies : ℕ) (u : List ℕ) :
    (alignmentWord copies u).length = copies * (u.length + 1) := by
  simp [alignmentWord]

private theorem alignmentWord_digits_lt {b copies : ℕ} (hb : 2 ≤ b)
    (u : List ℕ) (hu : ∀ d ∈ u, d < b) :
    ∀ d ∈ alignmentWord copies u, d < b := by
  intro d hd
  rw [alignmentWord, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  split_ifs with h
  · exact hu _ (List.getElem_mem h)
  · omega

private theorem occursAt_alignmentWord_copy {b : ℕ} {x : ℝ} {copies : ℕ}
    {u : List ℕ} {p i : ℕ} (hV : OccursAt b x (alignmentWord copies u) p)
    (hi : i < copies) : OccursAt b x u (p + i * (u.length + 1)) := by
  intro j hj
  have hindex : i * (u.length + 1) + j < (alignmentWord copies u).length := by
    rw [length_alignmentWord]
    calc
      i * (u.length + 1) + j < i * (u.length + 1) + (u.length + 1) := by omega
      _ = (i + 1) * (u.length + 1) := by ring
      _ ≤ copies * (u.length + 1) := Nat.mul_le_mul_right _ (by omega)
  have hmatch := hV (i * (u.length + 1) + j) hindex
  calc
    digitOf b (Int.fract x) (p + i * (u.length + 1) + j)
        = (alignmentWord copies u)[i * (u.length + 1) + j] := by
            simpa [Nat.add_assoc] using hmatch
    _ = u[j] := by
      simp only [alignmentWord, List.getElem_ofFn]
      have hjstep : j < u.length + 1 := by omega
      have hmod : (i * (u.length + 1) + j) % (u.length + 1) = j := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt hjstep]
      simp [hmod, hj]

private theorem alignment_start_mod (p k m : ℕ) (hk : 1 ≤ k) :
    (p + (k - p % k) * (k * m + 1)) % k = 0 := by
  have hr : p % k < k := Nat.mod_lt _ (by omega)
  by_cases hr0 : p % k = 0
  · simp [hr0, Nat.add_mod]
  · have hi : k - p % k < k := by omega
    have hk2 : 1 < k := by omega
    calc
      (p + (k - p % k) * (k * m + 1)) % k
          = (p % k + (k - p % k)) % k := by
              simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hi,
                Nat.mod_eq_of_lt hk2]
      _ = k % k := by rw [Nat.add_sub_of_le hr.le]
      _ = 0 := Nat.mod_self k

/-- **Disjunctivity is invariant under positive powers of the base.**
The exponent hypothesis excludes `k = 0`, when the right-hand base is `1`. -/
theorem isDisjunctive_pow_iff (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (x : ℝ) : IsDisjunctive b x ↔ IsDisjunctive (b ^ k) x := by
  have hbk : 2 ≤ b ^ k := by
    calc
      2 ≤ b := hb
      _ ≤ b ^ k := Nat.le_self_pow (by omega) b
  constructor
  · intro hdisj
    rw [isDisjunctive_iff_forall_occursAt (b ^ k) hbk x]
    intro W hW
    have hall := (isDisjunctive_iff_forall_occursAt b hb x).1 hdisj
    have hval : blockNatVal (b ^ k) W < (b ^ k) ^ W.length :=
      blockNatVal_lt (b ^ k) W hW
    have hval' : blockNatVal (b ^ k) W < b ^ (k * W.length) := by
      rwa [← pow_mul] at hval
    set u := padWord b (k * W.length) (blockNatVal (b ^ k) W) with hudef
    have hulen : u.length = k * W.length := length_padWord hb hval'
    have hult : ∀ d ∈ u, d < b := padWord_digits_lt hb _ _
    have huval : blockNatVal b u = blockNatVal (b ^ k) W := by
      rw [hudef, blockNatVal_padWord hb]
    set V := alignmentWord (k + 1) u with hVdef
    have hVlt : ∀ d ∈ V, d < b := by
      rw [hVdef]
      exact alignmentWord_digits_lt hb u hult
    obtain ⟨p, hp⟩ := hall V hVlt
    set i := k - p % k with hidef
    have hi : i < k + 1 := by
      rw [hidef]
      omega
    have huocc : OccursAt b x u (p + i * (u.length + 1)) := by
      apply occursAt_alignmentWord_copy (by simpa [hVdef] using hp) hi
    have hmod : (p + i * (u.length + 1)) % k = 0 := by
      rw [hidef, hulen]
      exact alignment_start_mod p k W.length hk
    obtain ⟨n, hn⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hucell := (occursAt_iff_orbit_mem b hb x u hult
      (p + i * (u.length + 1))).1 huocc
    have hpowR : (((b ^ k : ℕ) : ℝ) ^ W.length) =
        (b : ℝ) ^ (k * W.length) := by
      push_cast
      rw [pow_mul]
    have hBcell : orbit (b ^ k) x n ∈
        Set.Ico ((blockNatVal (b ^ k) W : ℝ) / ((b ^ k : ℕ) : ℝ) ^ W.length)
          (((blockNatVal (b ^ k) W : ℝ) + 1) /
            ((b ^ k : ℕ) : ℝ) ^ W.length) := by
      rw [orbit_pow, ← hn]
      rw [hpowR]
      simpa [huval, hulen] using hucell
    exact ⟨n, (occursAt_iff_orbit_mem (b ^ k) hbk x W hW n).2 hBcell⟩
  · intro hdisj a c ha hac hc
    obtain ⟨n, hn⟩ := hdisj a c ha hac hc
    refine ⟨k * n, ?_⟩
    rw [← orbit_pow b k x n]
    exact hn

end NormalNumbers
