/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline
import NormalNumbers.StonehamBoundary
import NormalNumbers.MahlerLowerBoundGeneral
import NormalNumbers.DisjunctiveCorollaries
import NormalNumbers.NormalMeager

/-!
# The landscape grid: one statement per region 🗺️

Companion to the grid section of `docs/how-irregular-is-a-number.html`.  The Venn on that page
crosses two chains, so the honest picture is a **grid**:

* **columns** (arithmetic): rational / algebraic irrational / transcendental, the last split on
  the page into *computable* and *uncomputable*;
* **rows** (expansion, in a **fixed** base `b`): not disjunctive / disjunctive but not normal /
  normal but not absolutely normal / absolutely normal.

The base quantifier is a third axis.  It only creates *new* regions in two places, so it gets a
two-row **strip** instead of tripling the grid: "disjunctive in no base" and "disjunctive in every
base, normal in none".

Every cell below is one of: a theorem (proved here or upstream in this repo), a cited
`Literature`-style `Prop` (faithful-or-weaker transcription, provenance tier P = PDF held in
`papers/`), or a named **open** `Prop`.

⚠️ **Computability is not formalized** in this repo (`ℝ` is not `Encodable`, so "computable real"
needs its own layer; `docs/irregularity-landscape.md` §1b).  So the computable/uncomputable split
of the transcendental column lives in docstrings, and the Lean content of every *uncomputable*
cell is the honest substitute: **the cell is uncountable**, and only countably many reals are
computable.
-/

namespace NormalNumbers.LandscapeGrid

open NormalNumbers Filter Set MeasureTheory
open scoped Nat

/-! ## Tools -/

/-- A residual subset of `ℝ` is uncountable: a countable set is a countable union of closed
nowhere-dense singletons, hence meagre, and a residual set is not meagre (Baire). -/
theorem not_countable_of_mem_residual {S : Set ℝ} (h : S ∈ residual ℝ) : ¬ S.Countable := by
  intro hc
  apply not_isMeagre_of_mem_residual h
  have hU : IsMeagre (⋃ x ∈ S, ({x} : Set ℝ)) :=
    isMeagre_biUnion hc fun x _ =>
      (isClosed_singleton.isNowhereDense_iff.mpr (interior_singleton x)).isMeagre
  simpa using hU

/-! ## The rational column -/

/-- **ℚ × not disjunctive: every rational.**  Disjunctive numbers are irrational. -/
theorem rat_not_isDisjunctive (b : ℕ) (q : ℚ) : ¬ IsDisjunctive b (q : ℝ) :=
  fun h => h.irrational ⟨q, rfl⟩

/-- **ℚ × {disjunctive, normal, absolutely normal}: empty.**  Normal implies disjunctive. -/
theorem rat_not_isNormal (b : ℕ) (hb : 2 ≤ b) (q : ℚ) : ¬ IsNormal b (q : ℝ) :=
  fun h => rat_not_isDisjunctive b q (h.isDisjunctive hb)

/-! ## The algebraic-irrational column: all four cells open

No algebraic irrational is known to be disjunctive in any base, and none is known *not* to be.
Borel's conjecture says the first three cells are empty and the last is everything. -/

/-- **open.**  Algebraic irrational × not disjunctive in base `b`.  Conjecturally empty. -/
def algebraic_notDisjunctive_open (b : ℕ) : Prop :=
  ∃ x : ℝ, IsAlgebraic ℤ x ∧ Irrational x ∧ ¬ IsDisjunctive b x

/-- **open.**  Algebraic × disjunctive but not normal in base `b`.  Conjecturally empty. -/
def algebraic_disjunctive_notNormal_open (b : ℕ) : Prop :=
  ∃ x : ℝ, IsAlgebraic ℤ x ∧ IsDisjunctive b x ∧ ¬ IsNormal b x

/-- **open.**  Algebraic × normal in base `b` but not absolutely normal.  Conjecturally empty. -/
def algebraic_normal_notAbsolutelyNormal_open (b : ℕ) : Prop :=
  ∃ x : ℝ, IsAlgebraic ℤ x ∧ IsNormal b x ∧ ¬ IsAbsolutelyNormal x

/-- **open.**  Borel (1950): every algebraic irrational is absolutely normal.  Not one algebraic
irrational is known to be even disjunctive in a single base (Waldschmidt, *Words and
Transcendence*, Conjecture 1.1 and the remark after it). -/
def borel_algebraic_conjecture : Prop :=
  ∀ x : ℝ, IsAlgebraic ℤ x → Irrational x → IsAbsolutelyNormal x

/-! ## The transcendental column -/

/-- **Core: no positive integer multiple of Liouville's number `Σ g^(-n!)` is disjunctive in
base `g`.**  For `N ≥ 1` pick `k` with `N + 2 ≤ gᵏ`; then `N` has no all-`(g−1)` window of length
`k`, so `orbit_liouvilleMul_lt` keeps the orbit of `N·λ_g` below `1 − g⁻ᵏ` from time
`(2k+2)!` on, while disjunctivity would revisit `[1 − g⁻ᵏ, 1)` arbitrarily late. -/
theorem natMul_liouvilleNumber_not_isDisjunctive (g N : ℕ) (hg : 2 ≤ g) (hN : 1 ≤ N) :
    ¬ IsDisjunctive g ((N : ℝ) * liouvilleNumber g) := by
  intro h
  obtain ⟨k, hk⟩ : ∃ k, N + 2 ≤ g ^ k :=
    ⟨N + 2, (Nat.lt_pow_self (by omega : 1 < g)).le⟩
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp at hk
    · exact hpos
  have hNK : N ≤ g ^ k := by omega
  have hmod : ∀ d, k ≤ d → N % g ^ d + g ^ (d - k) + 1 ≤ g ^ d := by
    intro d hd
    have hsplit : g ^ d = g ^ (d - k) * g ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    have hpos : 1 ≤ g ^ (d - k) := Nat.one_le_pow _ _ (by omega)
    have hmodle : N % g ^ d ≤ N := Nat.mod_le _ _
    have hprod : g ^ (d - k) * (N + 2) ≤ g ^ (d - k) * g ^ k := Nat.mul_le_mul_left _ hk
    nlinarith
  have hgR : (1 : ℝ) < g := by exact_mod_cast (by omega : 1 < g)
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hsmall : 0 < 1 / (g : ℝ) ^ k := by positivity
  have hle1 : 1 / (g : ℝ) ^ k ≤ 1 := by
    rw [div_le_one hgk]; exact one_le_pow₀ hgR.le
  obtain ⟨n, hn, hmem⟩ := h.exists_ge ((k + k + 2)!) (a := 1 - 1 / (g : ℝ) ^ k) (c := 1)
    (by linarith) (by linarith) le_rfl
  have hlt := Mahler.orbit_liouvilleMul_lt g k k N hg hk1 hN hNK hmod n hn
  exact absurd hmem.1 (not_le.2 hlt)

/-- **Transcendental × not disjunctive in base `b`** (computable witness): Liouville's number
`λ_b = Σ b^(-n!)`.  Transcendental by mathlib (`transcendental_liouvilleNumber`). -/
theorem liouvilleNumber_cell_notDisjunctive (b : ℕ) (hb : 2 ≤ b) :
    Transcendental ℤ (liouvilleNumber b) ∧ ¬ IsDisjunctive b (liouvilleNumber b) := by
  refine ⟨transcendental_liouvilleNumber hb, ?_⟩
  simpa using natMul_liouvilleNumber_not_isDisjunctive b 1 hb le_rfl

/-- **The "one of these multiples must be disjunctive" route is closed for general
irrationals.**  There is a transcendental `α` none of whose positive integer multiples is
disjunctive in base `g`.  Mahler/Berend–Boshernitzan put each *individual* block into *some*
small multiple `m·α`; this says no single multiple, and no finite list of multiples, can be
made to carry *all* blocks for every irrational.  A "one of `m₁α, …, m_rα` is disjunctive"
theorem for algebraic `α` would therefore need an input specific to algebraic numbers. -/
theorem exists_transcendental_no_multiple_disjunctive (g : ℕ) (hg : 2 ≤ g) :
    ∃ α : ℝ, Transcendental ℤ α ∧ ∀ m : ℕ, 1 ≤ m → ¬ IsDisjunctive g ((m : ℝ) * α) :=
  ⟨liouvilleNumber g, transcendental_liouvilleNumber hg,
    fun m hm => natMul_liouvilleNumber_not_isDisjunctive g m hg hm⟩

/-- **Uncomputable × not disjunctive in base `b`: uncountable**, hence (computable reals being
countable) it has uncomputable members.  **sorry, confidence 99%.**  English proof: the reals in
`[0,1)` whose base-`b` digits avoid the block `(b−1)(b−1)` form a Cantor set, which is
uncountable (it surjects onto `{0,1}^ℕ` by reading digits `0`/`1` at even positions with `0`
padding); every member is non-disjunctive, and removing the countably many algebraic members
leaves an uncountable set of transcendentals. -/
theorem uncountable_transcendental_notDisjunctive (b : ℕ) (hb : 2 ≤ b) :
    ¬ {x : ℝ | Transcendental ℤ x ∧ ¬ IsDisjunctive b x}.Countable := by
  sorry

/-- The residual set behind the strip and the second row: Liouville, disjunctive in every base,
normal in no base.  Intersection of three residual sets (mathlib's Liouville set,
`residual_absolutelyDisjunctive`, and the complements of the meagre normal sets). -/
theorem residual_liouville_absDisj_nowhereNormal :
    {x : ℝ | Liouville x ∧ AbsolutelyDisjunctive x ∧ ∀ b, 2 ≤ b → ¬ IsNormal b x}
      ∈ residual ℝ := by
  have habnormal : {x : ℝ | ∀ b, 2 ≤ b → ¬ IsNormal b x} ∈ residual ℝ := by
    rw [show {x : ℝ | ∀ b, 2 ≤ b → ¬ IsNormal b x} =
        ⋂ b : ℕ, {x : ℝ | 2 ≤ b → ¬ IsNormal b x} by ext x; simp]
    refine countable_iInter_mem.2 fun b => ?_
    by_cases hb : 2 ≤ b
    · rw [show {x : ℝ | 2 ≤ b → ¬ IsNormal b x} = {x : ℝ | IsNormal b x}ᶜ by ext x; simp [hb]]
      exact isMeagre_setOf_isNormal b hb
    · simp [hb]
  have hl : {x : ℝ | Liouville x} ∈ residual ℝ := eventually_residual_liouville
  filter_upwards [hl, residual_absolutelyDisjunctive, habnormal] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Strip row 2 / grid row 2, transcendental:** a Liouville (hence transcendental) number
that is disjunctive in every base and normal in none.  Non-constructive (Baire); the computable
version is the effective nested-interval construction of `docs/disjunctive-vs-normal.md` §3.3
with fast zero-runs added, which is not formalized. -/
theorem exists_liouville_absDisj_nowhereNormal :
    ∃ x : ℝ, Liouville x ∧ AbsolutelyDisjunctive x ∧ ∀ b, 2 ≤ b → ¬ IsNormal b x := by
  obtain ⟨x, hx⟩ := nonempty_of_not_isMeagre
    (not_isMeagre_of_mem_residual residual_liouville_absDisj_nowhereNormal)
  exact ⟨x, hx⟩

/-- **Uncomputable × disjunctive in every base, normal in none: uncountable.**  Hence it has
uncomputable members, and (row 2 of the grid) for every base `b` the cell
"transcendental, disjunctive in `b`, not normal in `b`" is uncountable too. -/
theorem uncountable_liouville_absDisj_nowhereNormal :
    ¬ {x : ℝ | Liouville x ∧ AbsolutelyDisjunctive x ∧ ∀ b, 2 ≤ b → ¬ IsNormal b x}.Countable :=
  not_countable_of_mem_residual residual_liouville_absDisj_nowhereNormal

/-! ### Cited inputs (tier P: PDFs in `papers/`) -/

/-- **Bailey–Borwein**, *Nonnormality of Stoneham constants*, Ramanujan J. 29 (2012) 409-422,
abstract and §3: `α₂,₃` is not 6-normal (first shown in their ref. [5]).  Tier P
(`papers/bailey-borwein-2012-nonnormality-stoneham.pdf`). -/
def baileyBorwein_stoneham23_not_normal_six : Prop := ¬ IsNormal 6 stoneham23

/-- **Coons**, *An arithmetical excursion via Stoneham numbers*, J. Aust. Math. Soc. 96 (2014)
303-315, Appendix A: every Stoneham number `α_{b,c}` is transcendental, by Mahler's method
(`F_c(x) = Σ x^(cⁿ)/cⁿ` is a transcendental Mahler function).  Stated for `α₂,₃`.  Tier P
(`papers/coons-2014-stoneham-excursion.pdf`). -/
def coons_stoneham23_transcendental : Prop := Transcendental ℤ stoneham23

/-- **Schmidt**, *On normal numbers*, Pacific J. Math. 10 (1960) 661-672, Theorem 1B: if `r`, `s`
are not powers of a common integer, the reals normal to base `r` but not even simply normal to
base `s` have the power of the continuum.  Transcribed weaker: "not normal" for "not simply
normal", "uncountable" for "continuum".  Tier P (`papers/schmidt-1960-on-normal-numbers.pdf`). -/
def schmidt1960_uncountable : Prop :=
  ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → (∀ p q : ℕ, 1 ≤ p → 1 ≤ q → r ^ p ≠ s ^ q) →
    ¬ {x : ℝ | IsNormal r x ∧ ¬ IsNormal s x}.Countable

/-- **Becher–Heiber–Slaman**, *A computable absolutely normal Liouville number*, Math. Comp. 84
(2015) 2939-2952, main Theorem.  The computability half is not expressible here (see the module
docstring), so this is the weaker existence statement, which Bugeaud (2002) had already proved
non-constructively.  Tier P (`papers/becher-heiber-slaman-2015-abs-normal-liouville.pdf`). -/
def becherHeiberSlaman_liouville_absNormal : Prop :=
  ∃ x : ℝ, Liouville x ∧ IsAbsolutelyNormal x

/-- **Borel 1909**: almost every real is absolutely normal.  Gives the uncomputable
absolutely-normal cell (a conull set is uncountable); Chaitin's `Ω` is a named member
(Martin-Löf random, hence absolutely normal).  Not yet formalized here
(`docs/irregularity-landscape.md` §3 item 2). -/
def borel1909 : Prop := ∀ᵐ x : ℝ, IsAbsolutelyNormal x

/-! ### Cells from the cited inputs -/

/-- **Transcendental × disjunctive but not normal, base 6** (computable witness): `α₂,₃`.
Disjunctive in base 6 is this repo's `isDisjunctive_six_stoneham23`. -/
theorem stoneham23_cell_base6
    (hBB : baileyBorwein_stoneham23_not_normal_six) (hC : coons_stoneham23_transcendental) :
    Transcendental ℤ stoneham23 ∧ IsDisjunctive 6 stoneham23 ∧ ¬ IsNormal 6 stoneham23 :=
  ⟨hC, isDisjunctive_six_stoneham23, hBB⟩

/-- **Transcendental × normal in base 2 but not absolutely normal** (computable witness):
`α₂,₃`.  Normal in base 2 is this repo's `isNormal_two_stoneham23` (Bailey–Crandall 2002). -/
theorem stoneham23_cell_base2
    (hBB : baileyBorwein_stoneham23_not_normal_six) (hC : coons_stoneham23_transcendental) :
    Transcendental ℤ stoneham23 ∧ IsNormal 2 stoneham23 ∧ ¬ IsAbsolutelyNormal stoneham23 :=
  ⟨hC, isNormal_two_stoneham23, fun h => hBB (h 6 (by norm_num))⟩

/-! ## The strip: regions that exist only once the base is quantified -/

/-- **open, including whether it is empty** (`docs/disjunctive-vs-normal.md` §4.2, literature
sweep 2026-08-25, ~75% that it is genuinely open): an irrational disjunctive in **no** base.
⚠️ Liouville's `λ` and Thue–Morse are *not* known members: each is non-disjunctive in one base
family only.  The Venn on the page drew them here until 2026-10-05. -/
def exists_irrational_disjunctive_in_no_base : Prop :=
  ∃ x : ℝ, Irrational x ∧ ∀ b, 2 ≤ b → ¬ IsDisjunctive b x

end NormalNumbers.LandscapeGrid
