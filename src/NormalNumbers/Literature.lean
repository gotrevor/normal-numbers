/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline
import NormalNumbers.AdderTowerC1

/-!
# The literature ledger: STATEMENTS of adjacent known results 📚

Brief: `BRIEF-literature-statements.md`.  This is the repo's
machine-readable novelty tripwire: precise formalizations of the
**statements** of known theorems (and named open problems) adjacent to
this repo's work, as plain `Prop`-valued `def`s — **not proved** unless a
theorem we already hold discharges one (then a `…_holds` edge is wired,
upgrading "we cite it" to "we independently verified it").

🚨 **Future briefs: check candidate theorems against this file before
claiming novelty** (the C1 rediscovery of 2026-08-30 is exactly what this
ledger exists to catch).

Provenance tiers per statement docstring:
* **tier P** — transcribed from a paper held locally in `papers/`;
* **tier S** — transcribed from our own docs quoting the paper (we do not
  hold the PDF); papers worth fetching are listed in the brief's RESULT.

Conventions: digits are read through `Int.fract` (repo standard); i.o. is
spelled `∀ N, ∃ n, N ≤ n ∧ …`; base explicit.
-/

namespace NormalNumbers.Literature

open NormalNumbers Filter

/-! ## Mahler 1973 and Berend–Boshernitzan 1994 (the C-tower's ancestors) -/

/-- **Mahler 1973, Theorem M** (*Arithmetical properties of the digits of
the multiples of an irrational number*, Bull. Austral. Math. Soc. 8).
For any real irrational `α`, any base `g ≥ 2`, and any block `w` of `k`
digits, some positive integer `m ≤ g^(2k+1)` has `w` occurring infinitely
often in the base-`g` expansion of `m·α`.

provenance: secondary (`docs/disjunctive-vs-normal.md` §1.1, quoting
Waldschmidt *Words and Transcendence* §1 [3, Theorem M]; PDF not held). -/
def mahler_theoremM : Prop :=
  ∀ (α : ℝ), Irrational α → ∀ (g : ℕ), 2 ≤ g → ∀ (w : List ℕ), w ≠ [] →
    (∀ d ∈ w, d < g) →
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ (2 * w.length + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n

/-- **Berend–Boshernitzan 1994** (*Renewal-type theorems…* / the Mahler
sharpening, Acta Arith. 66): Mahler's multiplier bound improves to
`m ≤ 2·g^(k+1)`.

The paper also shows the bound cannot beat `g^k − 1`; that lower bound's
exact quantifier structure is not pinned by our secondary sources, so per
the never-fabricate rule it is NOT transcribed (gap recorded in the brief's
RESULT).

provenance: secondary (`docs/adder-family-2026-08-29.md` folklore-check
section; `docs/disjunctive-vs-normal.md` §1.1). -/
def berendBoshernitzan_bound : Prop :=
  ∀ (α : ℝ), Irrational α → ∀ (g : ℕ), 2 ≤ g → ∀ (w : List ℕ), w ≠ [] →
    (∀ d ∈ w, d < g) →
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 2 * g ^ (w.length + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n

/-- **Berend–Boshernitzan 1994, `M(3,1) = 2` (upper half)**: for every
irrational `x` and every ternary digit `d`, `d` occurs infinitely often in
the base-3 expansion of `x` or of `2x` — i.e. multipliers `{1, 2}` suffice
for single digits in base 3.  (The paper also proves minimality — `{1}`
does not suffice — not transcribed here.)

provenance: secondary (`docs/mahler-sets-2026-08-29.md` via master
`c645528`; C1 reclassification note in `BRIEF-adder-tower.md`). -/
def berendBoshernitzan_M31 : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ d : ℕ, d < 3 →
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 x [d] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * x) [d] n)

/-- **Wired edge**: our tower claim C1 (`c1_ternary_digit`, kernel-tier
certificates) independently verifies Berend–Boshernitzan's `M(3,1) = 2`. -/
theorem berendBoshernitzan_M31_holds : berendBoshernitzan_M31 :=
  fun x hx d hd => Adder.c1_ternary_digit x hx d hd

/-! ## The Adamczewski–Rampersad boundary -/

/-- **The base-2 occurrence boundary**: the only blocks known to occur
infinitely often in the binary expansion of an arbitrary irrational are
`0`, `1`, `01`, `10` — and that is just non-eventual-periodicity.  For
any other word and any fixed (even algebraic) irrational, occurrence
i.o. is open.

Attribution: **classical/folklore, recorded (not proved) in §1 of**
Adamczewski–Rampersad, *On patterns occurring in binary algebraic
numbers*, PAMS 136 (2008), 3105–3109, as "the only known result …
somewhat trivial"; their own theorems are the 7/3-power results.  The
open frontier framing (any `W ∉ {0,1,01,10}`) is theirs.

provenance: primary (`papers/adamczewski-rampersad-2008-binary-patterns.pdf`
+ companion `.md`; verified against the text 2026-08-30).  This is the
openness frontier that makes each adder disjunct individually
unprovable by current methods. -/
def adamczewskiRampersad_boundary : Prop :=
  ∀ (x : ℝ), Irrational x →
    ∀ w ∈ [[0], [1], [0, 1], [1, 0]],
      ∀ N, ∃ n, N ≤ n ∧ OccursAt 2 x w n

section BoundaryWire

/-- A word occurs at `n` iff its digits are read off pointwise; single-word
form. -/
theorem occursAt_single_iff (b : ℕ) (x : ℝ) (d n : ℕ) :
    OccursAt b x [d] n ↔ digitOf b (Int.fract x) n = d := by
  constructor
  · intro h
    simpa using h 0 (by norm_num)
  · intro h j hj
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simpa using h

/-- Pair form. -/
theorem occursAt_pair_iff (b : ℕ) (x : ℝ) (d e n : ℕ) :
    OccursAt b x [d, e] n
      ↔ digitOf b (Int.fract x) n = d ∧ digitOf b (Int.fract x) (n + 1) = e := by
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ j hj
    have hj2 : j < 2 := by simpa using hj
    interval_cases j
    · simpa using h0
    · simpa using h1

private theorem binary_digit_cases (x : ℝ) (n : ℕ) :
    digitOf 2 (Int.fract x) n = 0 ∨ digitOf 2 (Int.fract x) n = 1 := by
  have := digitOf_lt 2 le_rfl (Int.fract x) n
  omega

/-- Eventually constant binary digits (from `N` on) contradict
irrationality — the `p = 1` case of the endgame. -/
private theorem not_irrational_of_eventually_constant (x : ℝ) (N : ℕ)
    (h : ∀ n, N ≤ n → digitOf 2 (Int.fract x) (n + 1) = digitOf 2 (Int.fract x) n) :
    ¬ Irrational x :=
  Adder.not_irrational_of_periodic_digits x N 1 one_pos fun m hm => h m hm

/-- If the transition `d → e` (`d ≠ e`) never happens after `N`, the digits
are eventually constant. -/
private theorem eventually_constant_of_no_switch (x : ℝ) (N : ℕ) (d : ℕ)
    (hd : d < 2)
    (h : ∀ n, N ≤ n → ¬ (digitOf 2 (Int.fract x) n = d ∧
      digitOf 2 (Int.fract x) (n + 1) = 1 - d)) :
    ¬ Irrational x := by
  by_cases hex : ∃ n, N ≤ n ∧ digitOf 2 (Int.fract x) n = d
  · -- once at `d`, stuck at `d`
    obtain ⟨n₀, hn₀, h₀⟩ := hex
    have hstay : ∀ m, n₀ ≤ m → digitOf 2 (Int.fract x) m = d := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact h₀
      | succ m hm ih =>
        by_cases hde : digitOf 2 (Int.fract x) (m + 1) = d
        · exact hde
        · have hne : digitOf 2 (Int.fract x) (m + 1) = 1 - d := by
            have := binary_digit_cases x (m + 1)
            omega
          exact absurd ⟨ih, hne⟩ (h m (le_trans hn₀ hm))
    exact not_irrational_of_eventually_constant x n₀ fun n hn => by
      rw [hstay (n + 1) (by omega), hstay n hn]
  · -- never at `d`: always at `1 − d`
    push Not at hex
    have hoth : ∀ n, N ≤ n → digitOf 2 (Int.fract x) n = 1 - d := by
      intro n hn
      have := hex n hn
      have := binary_digit_cases x n
      omega
    exact not_irrational_of_eventually_constant x N fun n hn => by
      rw [hoth (n + 1) (by omega), hoth n hn]

/-- **Wired edge**: the Adamczewski–Rampersad boundary words really do
occur i.o. in every irrational — proved from the repo's endgame (eventual
constancy / forbidden-switch argument), independently of the certificate
machinery. -/
theorem adamczewskiRampersad_boundary_holds : adamczewskiRampersad_boundary := by
  intro x hx w hw
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ := hcon
  fin_cases hw
  · -- `[0]`: digits eventually all 1
    refine eventually_constant_of_no_switch x N 0 (by norm_num) ?_ hx
    rintro n hn ⟨h0, -⟩
    exact hN n hn ((occursAt_single_iff 2 x 0 n).2 h0)
  · -- `[1]`: digits eventually all 0
    refine eventually_constant_of_no_switch x N 1 (by norm_num) ?_ hx
    rintro n hn ⟨h1, -⟩
    exact hN n hn ((occursAt_single_iff 2 x 1 n).2 h1)
  · -- `[0,1]`: the switch 0→1 is forbidden
    refine eventually_constant_of_no_switch x N 0 (by norm_num) ?_ hx
    rintro n hn ⟨h0, h1⟩
    exact hN n hn ((occursAt_pair_iff 2 x 0 1 n).2 ⟨h0, by simpa using h1⟩)
  · -- `[1,0]`: the switch 1→0 is forbidden
    refine eventually_constant_of_no_switch x N 1 (by norm_num) ?_ hx
    rintro n hn ⟨h1, h0⟩
    exact hN n hn ((occursAt_pair_iff 2 x 1 0 n).2 ⟨h1, by simpa using h0⟩)

end BoundaryWire

/-! ## Waldschmidt's Conjecture 1.1 (absolute disjunctivity of algebraics) -/

/-- **Waldschmidt, *Words and Transcendence*, Conjecture 1.1** (open): for
`x` a real algebraic irrational, `g ≥ 3`, and any digit `a < g`, the digit
`a` occurs (at least once) in the base-`g` expansion of `x`.  Waldschmidt
notes the full conjecture is equivalent to every block occurring i.o. in
every base — i.e. to absolute disjunctivity of algebraic irrationals.

provenance: secondary (`docs/disjunctive-vs-normal.md`, quoting
arXiv:0908.4034 §1). -/
def waldschmidt_conjecture_1_1 : Prop :=
  ∀ (x : ℝ), Irrational x → IsAlgebraic ℚ x → ∀ (g : ℕ), 3 ≤ g →
    ∀ a : ℕ, a < g → ∃ n : ℕ, digitOf g (Int.fract x) n = a

/-! ## Furstenberg 1967 (×2 ×3 rigidity, the dense-orbit theorem) -/

/-- **Furstenberg 1967** (*Disjointness in ergodic theory…*): for every
irrational `x`, the multiplicative orbit `{2^m 3^n x mod 1}` is dense in
`[0, 1]` (consequence of ×2, ×3 topological rigidity).  The measure
version (×p ×q conjecture) is famously open.

provenance: secondary (`docs/disjunctive-vs-normal.md` §1.2). -/
def furstenberg_dense_orbit : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    ∃ m n : ℕ, Int.fract ((2 : ℝ) ^ m * 3 ^ n * x) ∈ Set.Ico a c

/-! ## Becher–Yuhjtman 2019 (the Track-B Tier 1 headline) -/

/-- **Becher–Yuhjtman 2019, Theorem 1** (IMRN 2019(19), arXiv:1704.03622;
minus the O(n⁴) efficiency claim): there exists a real number that is
absolutely normal and continued-fraction normal.  (Their "absolutely
normal" is proved as simple normality to every base, classically
equivalent to the full normality stated here — see `papers/becher-…​.md`.)

provenance: primary (`papers/becher-yuhjtman-2019-abs-normal-cf-normal.md`
+ local PDF). -/
def becherYuhjtman_existence : Prop :=
  ∃ x : ℝ, IsAbsolutelyNormal x ∧ IsCFNormal x

/-- **Wired edge**: the repo's Tier 1 headline
(`exists_absolutely_normal_cf_normal`, witness `xstar`) proves the
Becher–Yuhjtman statement. -/
theorem becherYuhjtman_existence_holds : becherYuhjtman_existence :=
  exists_absolutely_normal_cf_normal

/-! ## Bailey–Misiurewicz 2006 (the weak hot spot theorem) -/

/-- **Bailey–Misiurewicz 2006, Theorem 1.1** (*A Strong Hot Spot Theorem*,
Proc. AMS 134): `x` is `b`-normal **iff** there is a constant `B` with
`limsup_n (visits of {bʲx} to [c,d) among j ≤ n)/n ≤ B(d−c)` for every
subinterval `[c,d)` of `[0,1)`.  (The repo's proven
`isNormal_of_visit_upper_bound` is the b-adic-interval corollary of the
“if” direction; the full iff over all intervals is transcribed here.)

provenance: primary (`papers/bailey-misiurewicz-2006-hot-spot.md` + local
PDF, complete AMS text).  **WIRED**: `baileyMisiurewicz_weak_hot_spot_holds`
(`LiteratureBMStrong.lean`) proves the full iff — `⟸` via
`isNormal_of_visit_upper_bound`, `⟹` via Wall's theorem — axiom-clean. -/
def baileyMisiurewicz_weak_hot_spot : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ x : ℝ,
    (IsNormal b x ↔
      ∃ B : ℝ, ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 →
        Filter.limsup
          (fun n => (visitCount (orbit b (Int.fract x)) c d n : ℝ) / n)
          Filter.atTop ≤ B * (d - c))

/-! ## Philipp 1967 (exponential ψ-mixing of the CF digits) -/

/-- **Philipp 1967, Satz 3** (= Scheerer 2017 §2, Theorem 2.1): the
continued-fraction digits are exponentially **ψ-mixing** under the Gauss
measure.  In the standard cylinder form used to state it, there is a rate
`ρ < 0.8` such that for every "past" word `u` (constraining digits
`0 … u.length−1`), every gap `n ≥ 1`, and every "future" word `v`
(constraining digits from position `u.length + n` onward),
`|γ(A ∩ B) − γ(A)·γ(B)| ≤ ρⁿ · γ(A)·γ(B)`, where `A = cfCylinder u` and
`B = cfCylinderFrom (u.length + n) v`.  (Cylinders generate the σ-algebras,
so the cylinder form is equivalent to the general past/future-σ-algebra
statement; rate later improved, Iosifescu–Kraaikamp Prop 2.3.7.)

provenance: tier S (`papers/scheerer-2017-cf-abs-normal.md` §2, quoting
W. Philipp, *Some metrical theorems in number theory*, Pacific J. Math. 20
(1967), Satz 3; primary PDF not held). -/
def philipp_psi_mixing : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 0.8 ∧
    ∀ (u v : List ℕ) (n : ℕ), 1 ≤ n →
      |(gaussMeasure (cfCylinder u ∩ cfCylinderFrom (u.length + n) v)).toReal
          - (gaussMeasure (cfCylinder u)).toReal
              * (gaussMeasure (cfCylinderFrom (u.length + n) v)).toReal|
        ≤ ρ ^ n * (gaussMeasure (cfCylinder u)).toReal
            * (gaussMeasure (cfCylinderFrom (u.length + n) v)).toReal

/-! ## Bailey–Misiurewicz 2006, §3 (the STRONG hot spot theorem) -/

/-- The scaled block-occurrence ratio behind the strong hot spot theorem:
`bᵐ · A(x,y,n,m) / n` in the `limsup` over `n`, where `A(x,y,n,m)` counts
(overlapping) occurrences of the length-`m` prefix of the digit sequence
`y` among the first `n` base-`b` digits of `x`.  `A` is bounded by `n`, so
the ratio is bounded by `bᵐ` and its `limsup` is a genuine real. -/
noncomputable def bmHotSpotRatio (b : ℕ) (x : ℝ) (y : ℕ → ℕ) (m : ℕ) : ℝ :=
  Filter.limsup
    (fun n =>
      ((b : ℝ) ^ m *
        (countOccurrences ((List.range m).map y)
          ((List.range n).map (digitOf b (Int.fract x))) : ℝ)) / n)
    Filter.atTop

/-- `y ∈ {0,…,b−1}^ℕ` is a **(sequence-space) hot spot** for `x`:
`liminf_m limsup_n bᵐ·A(x,y,n,m)/n = ∞`, i.e. the scaled prefix-visit ratio
of `bmHotSpotRatio` diverges as the prefix length grows (spelled as: it
eventually exceeds every bound `M`). -/
def IsSeqHotSpot (b : ℕ) (x : ℝ) (y : ℕ → ℕ) : Prop :=
  (∀ i, y i < b) ∧ ∀ M : ℝ, ∀ᶠ m in Filter.atTop, M ≤ bmHotSpotRatio b x y m

/-- **Bailey–Misiurewicz 2006, Theorem 3.4** (*A Strong Hot Spot Theorem*,
Proc. AMS 134): on the digit sequence space `Σ = {0,…,b−1}^ℕ`, `x` is
`b`-normal **iff** it has no sequence-space hot spot `y` (a non-normal `x`
has a pointwise hot spot `y` whose length-`m` prefixes occur with density
`≫ b⁻ᵐ`).  Proven in the paper via weak-* compactness + shift ergodicity +
a cylinder Besicovitch covering lemma.

provenance: primary (`papers/bailey-misiurewicz-2006-hot-spot.md` §3 +
local PDF, complete AMS text). -/
def baileyMisiurewicz_strong_hot_spot : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ x : ℝ,
    (IsNormal b x ↔ ¬ ∃ y : ℕ → ℕ, IsSeqHotSpot b x y)

/-- **Bailey–Misiurewicz 2006, Theorem 3.5** (the sufficient-condition form
actually used in §4): if the scaled block-occurrence ratio is uniformly
bounded — a single constant `C` with `limsup_n bᵐ·A(x,y,n,m)/n ≤ C` for
every `y ∈ {0,…,b−1}^ℕ` and every prefix length `m` — then `x` is
`b`-normal.  (In §4 this is applied to `stoneham23` with `C = 8`.)

provenance: primary (`papers/bailey-misiurewicz-2006-hot-spot.md` §3–4 +
local PDF).  **WIRED**: `baileyMisiurewicz_strong_hot_spot_criterion_holds`
(`LiteratureBMStrong.lean`) proves this from the repo's
`isNormal_of_visit_upper_bound`, axiom-clean — an independent verification. -/
def baileyMisiurewicz_strong_hot_spot_criterion : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ x : ℝ,
    (∃ C : ℝ, ∀ (y : ℕ → ℕ), (∀ i, y i < b) → ∀ m : ℕ,
        bmHotSpotRatio b x y m ≤ C) →
      IsNormal b x

/-! ## Vandehey 2017 (matrix actions preserve CF-normality) -/

/-- **Vandehey 2017, Theorem 1.1** (*Non-trivial matrix actions preserve
normality for continued fractions*, Compositio 153): if `x` is CF-normal
and `M = (a b; c d)` is an integer matrix with `det M ≠ 0` (and `Mx` is
defined), then `Mx = (ax+b)/(cx+d)` is CF-normal.  CF-normality is
extended to all of `ℝ` via `x ~ x − a₀(x)`, i.e. through `Int.fract`
(the repo's `IsCFNormal` is the B–Y window-frequency form on `[0,1)`).

provenance: primary (`papers/vandehey-2017-matrix-actions-cf-normality.md`
+ local PDF). -/
def vandehey_matrix_action : Prop :=
  ∀ (x : ℝ) (a b c d : ℤ), a * d - b * c ≠ 0 →
    (c : ℝ) * x + d ≠ 0 → IsCFNormal (Int.fract x) →
    IsCFNormal (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d)))

/-- A real is a quadratic irrational: irrational and a root of an integer
quadratic (Vandehey §7's coefficient class — the eventually-periodic CFs,
by Lagrange). -/
def IsQuadraticIrrational (q : ℝ) : Prop :=
  Irrational q ∧ ∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * q ^ 2 + b * q + c = 0

/-- **Vandehey 2017, §7 open problem 1** (OPEN — named in the attack map):
if `x` is CF-normal and `q, r` are quadratic irrationals with `q ≠ 0`,
must `q·x + r` be CF-normal?  Nothing is known even for `x ↦ φ·x`.

provenance: primary (`papers/vandehey-2017-matrix-actions-cf-normality.md`
§7; forward-citation crawl 2026-08-24 says still open). -/
def vandehey_quadratic_problem : Prop :=
  ∀ (x q r : ℝ), IsCFNormal (Int.fract x) →
    IsQuadraticIrrational q → IsQuadraticIrrational r → q ≠ 0 →
    IsCFNormal (Int.fract (q * x + r))

/-- **Vandehey 2017, §7 open problem 2 / Mendès France's original**
(OPEN): does rational arithmetic preserve CF-*simple* normality (correct
limiting frequency for each single digit)?  Stated with the single-digit
specialization of the repo's window-frequency form.

provenance: primary (`papers/vandehey-2017-matrix-actions-cf-normality.md`
§7). -/
def mendesFrance_simple_normality_problem : Prop :=
  ∀ (x : ℝ) (a b c d : ℤ), a * d - b * c ≠ 0 →
    (c : ℝ) * x + d ≠ 0 →
    (∀ k : ℕ, 1 ≤ k →
      Filter.Tendsto
        (fun p => (countOccurrences [k] ((List.range p).map (cfDigit (Int.fract x))) : ℝ) / p)
        Filter.atTop (nhds ((gaussMeasure (cfCylinder [k])).toReal))) →
    (∀ k : ℕ, 1 ≤ k →
      Filter.Tendsto
        (fun p => (countOccurrences [k]
          ((List.range p).map (cfDigit (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d))))) : ℝ) / p)
        Filter.atTop (nhds ((gaussMeasure (cfCylinder [k])).toReal)))

end NormalNumbers.Literature
