/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC2
import NormalNumbers.MahlerLowerBoundGeneral

/-!
# Product blocks: the shape of `{2, 11}`, and why base 5 has no small one 🧱

A **product block** in base `g` is a finite multiplier set `S` such that for every
irrational `X`, a *single* `m ∈ S` has every base-`g` digit infinitely often in `m·X`.
`AdderTowerC2.c2_product_block` proves `{2, 11}` is one in base 3.  This file names the
notion, wires C2 in as an instance, and records the **lower side**: the Liouville witness
`B · Σ g^(−i!)` of Berend–Boshernitzan 1994 Thm 3.1 (`MahlerLowerBoundGeneral.lean`) forces
every product block to contain, for every `B ≥ 1`, an `m` whose product `m·B` uses every
nonzero digit.  At `B = 1` in base 5 that is `m ≥ 1234₅ = 194`.

Probe + write-up: `experiments/mahler_product_block.py`, `docs/base5-product-block-2026-10-05.md`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- `S` is a base-`g` **product block**: for every irrational `X`, some `m ∈ S` has every
base-`g` digit occurring infinitely often in `m·X`. -/
def IsProductBlock (g : ℕ) (S : Finset ℕ) : Prop :=
  ∀ X : ℝ, Irrational X → ∃ m ∈ S, ∀ d, d < g → ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * X) [d] n

/-- C2 restated: `{2, 11}` is a ternary product block. -/
theorem isProductBlock_three_two_eleven : IsProductBlock 3 {2, 11} := by
  intro X hX
  rcases c2_product_block X hX with h | h
  · exact ⟨2, by simp, by exact_mod_cast h⟩
  · exact ⟨11, by simp, by exact_mod_cast h⟩

/-- Scaling: if `S` is a product block then so is `c·S` (`c ≥ 1`), since `c·X` is irrational.
So `{4, 22}` is a ternary block too (the probe's second exact pair up to 40). -/
theorem IsProductBlock.image_mul {g : ℕ} {S : Finset ℕ} (hS : IsProductBlock g S) {c : ℕ}
    (hc : 1 ≤ c) : IsProductBlock g (S.image (c * ·)) := by
  intro X hX
  obtain ⟨m, hm, hall⟩ := hS ((c : ℝ) * X) (hX.natCast_mul (by omega))
  refine ⟨c * m, Finset.mem_image_of_mem _ hm, ?_⟩
  intro d hd N
  obtain ⟨n, hn, hocc⟩ := hall d hd N
  refine ⟨n, hn, ?_⟩
  rw [show ((c * m : ℕ) : ℝ) * X = (m : ℝ) * ((c : ℝ) * X) by push_cast; ring]
  exact hocc

/-- **Liouville cover (lower side).**  For every `B ≥ 1`, a product block contains some `m`
such that every nonzero base-`g` digit is a digit of `m·B`.

English proof (confidence 95%): take `X = B · liouvilleNumber g`, irrational.  For `m ∈ S`
with `m·B < g^K`, past position `(K+2)!` the base-`g` expansion of `m·X = (m B)·Σ g^(−i!)` is
the digit string of `m B` right-aligned at each `i!` with zero gaps between (no carries:
the copies are `≥ K` apart), so a nonzero digit `d` occurs infinitely often in `m·X` iff
`d ∈ Nat.digits g (m * B)`.  The block property for `X` therefore needs an `m` covering every
nonzero digit.  The formal route is `orbit_liouvilleMul_lt`'s argument with "no `k`-run of
`g−1`" replaced by "digit `d` absent from `m B`". -/
theorem IsProductBlock.liouville_cover {g : ℕ} (hg : 2 ≤ g) {S : Finset ℕ}
    (hS : IsProductBlock g S) (B : ℕ) (hB : 1 ≤ B) :
    ∃ m ∈ S, ∀ d, 1 ≤ d → d < g → d ∈ Nat.digits g (m * B) := by
  sorry

/-- No `m < 194` has all four nonzero base-5 digits (`194 = 1234₅`). -/
theorem base5_full_digits_ge (m : ℕ) (hm : ∀ d, 1 ≤ d → d < 5 → d ∈ Nat.digits 5 m) :
    194 ≤ m := by
  by_contra h
  push Not at h
  have key : ∀ m < 194, ¬ (1 ∈ Nat.digits 5 m ∧ 2 ∈ Nat.digits 5 m ∧ 3 ∈ Nat.digits 5 m ∧
      4 ∈ Nat.digits 5 m) := by decide +kernel
  exact key m h ⟨hm 1 le_rfl (by norm_num), hm 2 (by norm_num) (by norm_num),
    hm 3 (by norm_num) (by norm_num), hm 4 (by norm_num) (by norm_num)⟩

/-- **Base 5 has no small product block**: every base-5 product block contains a
multiplier `≥ 194`.  (Base 3's `{2, 11}` sits just above its analogue `12₃ = 5`.) -/
theorem IsProductBlock.base5_exists_ge {S : Finset ℕ} (hS : IsProductBlock 5 S) :
    ∃ m ∈ S, 194 ≤ m := by
  obtain ⟨m, hm, hd⟩ := hS.liouville_cover (by norm_num) 1 le_rfl
  exact ⟨m, hm, base5_full_digits_ge m (by simpa using hd)⟩

/-- **The joint reading of `B(b,k) = bᵏ(b+1)` is false**: `{1, …, 30}` is *not* a base-5
product block.  Bugeaud–Coons, *A Mahler miscellany* (Doc. Math. Extra Vol. Mahler Selecta,
2019), Thm 7.1 states Mahler's theorem in the joint form (one `m ≤ B` with every `k`-block i.o.)
and adds, citing Bugeaud's book §8.6, that one may take `B(b,k) = bᵏ(b+1)`; at `b = 5, k = 1`
that is `30`.  The bound is a per-block statement; jointly it needs some `m ≥ 194`. -/
theorem not_isProductBlock_five_Icc_thirty : ¬ IsProductBlock 5 (Finset.Icc 1 30) := by
  intro h
  obtain ⟨m, hm, h194⟩ := h.base5_exists_ge
  simp only [Finset.mem_Icc] at hm
  omega

/-- **Card lower bound from the Liouville family** (computational; confidence 93%).  A base-5
product block inside `[1, 625]` has at least five multipliers.

Evidence: `liouville_cover` for every `B ≤ 300` with `5 ∤ B` turns this into a set-cover
instance over the 500 multipliers `m ≤ 625`, `5 ∤ m` (a multiple `5m'` covers exactly what
`m'` does: same digits, shifted).  HiGHS solves it exactly with optimum 5 and dual bound 5
(`experiments/mahler_product_block.py ilp 5 625 300`).  The formal route is a `decide` over
the cover table, which is large; the statement is recorded so the bound has a Lean name. -/
theorem IsProductBlock.base5_card_ge_five {S : Finset ℕ} (hS : IsProductBlock 5 S)
    (hS625 : ∀ m ∈ S, m ≤ 625) : 5 ≤ S.card := by
  sorry

/-- **An explicit base-5 product block** (computational; confidence 95%: full re-check without
the symmetry reduction found no failing assignment).  For every irrational `X`, one of these 17 multiples of `X` has every base-5
digit infinitely often.  Compare the classical block `[1, 15624]` (`mahler_multiplier_lt` on the
word `01234`), and `base5_exists_ge` (every block needs a member `≥ 194`; here `2832 = 42312₅`).

Evidence: exact carry-automaton collapse of every assignment `S → digits` on some prefix (the
C2 method), found by `experiments/mahler_block_rs` (greedy) and recorded in
`docs/base5-product-block-2026-10-05.md`.  The formal route needs a sparse certificate checker:
`checkCertA` enumerates the ambient carry product, here about `10⁴⁰` states. -/
theorem isProductBlock_five_seventeen :
    IsProductBlock 5 {1, 2, 3, 4, 8, 16, 17, 23, 29, 1251, 1254, 1838, 2188, 2272, 2439, 2832,
      3028} := by
  sorry

/-- **The base-5 block, minimized to 15** (computational; confidence 95%): `isProductBlock_five_seventeen`
without `3` and `4`, each deletion re-verified by a full collapse search
(`mahler_block minimize`).  Inclusion-minimal: removing any one member leaves an assignment
with no collapse certificate. -/
theorem isProductBlock_five_fifteen :
    IsProductBlock 5 {1, 2, 8, 16, 17, 23, 29, 1251, 1254, 1838, 2188, 2272, 2439, 2832, 3028} := by
  sorry

/-- **The base-5 block at 14** (computational; confidence 95%): from `isProductBlock_five_fifteen`,
drop `1` and `8`, add `2428 = 34203₅` (`mahler_block swap21`, accepted by a full collapse
search).  Note `1 ∉ S`: no member is `x` itself. -/
theorem isProductBlock_five_fourteen :
    IsProductBlock 5 {2, 16, 17, 23, 29, 1251, 1254, 1838, 2188, 2272, 2428, 2439, 2832, 3028} := by
  sorry

end NormalNumbers.Adder
