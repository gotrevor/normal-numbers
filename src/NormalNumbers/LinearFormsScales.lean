/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBad

/-!
# Linear forms in logarithms as scale separation (engine proposal E4): the freeze

Audit: `docs/LINEAR-FORMS-AUDIT-2026-10-04.md`.  Proposal: `docs/ENGINE-PROPOSALS-2026-10-04.md`
§E4.

## What is here

* `ScaleSeparation p q`: `|pᵐ − qⁿ| ≥ pᵐ / (C (m+n)^κ)` for all `m, n ≥ 1`.
* `Literature.BakerScaleSeparation`: Baker's theorem in that weak form, for every pair of
  multiplicatively independent integers `p, q ≥ 2` (cited, never an axiom).
* Guard, the known-false sibling: `not_scaleSeparation_two_four` (`2² = 4¹`, a DEPENDENT pair).
* Wiring that consumes the cited Prop: `gap_of_scaleSeparation`, Tijdeman's gap principle for
  Furstenberg's semigroup `Σ = {2ᵘ3ᵛ}`: consecutive elements `s < s'` satisfy
  `s' − s ≥ s / (C · (exponent size)^κ)`.
* The elementary count that the avoidance engines actually consume, with no Baker input:
  `band_unique_u` (in a dyadic band each `v` contributes at most one `u`).
* The frozen headline `furstenbergLogAvoid_holds : FurstenbergLogAvoid` (`sorry`), its wiring
  to the published bounds (`moshchevitinPeresSchlag_of_logAvoid`, `badziahinHarrap_of_logAvoid`)
  and two siblings:
  `not_constAvoid_of_furstenberg` (independent pair: a constant rate is false, from cited
  Furstenberg) and `constAvoid_powersOfTwo` (dependent pair: a constant rate is true).

## The audit's verdict on E4, in one paragraph

Baker / Matveev bound only near-coincidences `2ᵐ ≈ 3ⁿ`.  The repo's avoidance engines
(`UniformBad.exists_avoid_of_stagePotential`) consume the NUMBER of obstacles charged to a
stage, and that count is elementary (`band_unique_u`); near-coincident scales neither add nor
remove obstacles.  The normality-profile questions for Stoneham numbers outside the
Bailey–Borwein region need short-orbit equidistribution of `3ⁿ mod 2ᶜ`, which separation does
not supply.  So `ScaleSeparation` is frozen as a cited input with one honest consumer
(`gap_of_scaleSeparation`), and the headline below is the best open question found in the
adjacent territory; it is NOT driven by linear forms in logarithms.

## The headline (frozen, `sorry`)

**Problem (exact source wording).**  N. Moshchevitin, *On some open problems in Diophantine
approximation*, arXiv:1202.4539v3 (2012), §1.5 item 4 ("Fürstenberg's sequence"): with
`s₀ < s₁ < …` the integers `2ᵐ3ⁿ` in increasing order, "Peres-Schlag's method gives the
following result: for an arbitrary sequence `η_q` … there exists irrational `θ` such that
`inf_{q ⩾ 2} √q log q ||s_q θ − η_q|| > 0`", followed by: "We do not know if the original
Theorem 9 and the results from 3), 4) with `η_q ≡ 0` are not optimal.  However I am sure that in
homogemeous setting the original Theorem 9 and the results from 3), 4) are not optimal and may be
improved on."  Restated in Gayfulin–Moshchevitin, *On Furstenberg's Diophantine result*,
arXiv:2301.08212v2 (2023), §2: the set `{α : inf_{q∈Σ} log q log log q · ||qα|| > 0}` has full
dimension (Moshchevitin, via Peres–Schlag); Badziahin–Harrap: `{α : inf (log q)^{1+ε} ||qα|| > 0}`
is Cantor-winning; "As far as we know it is not known if the set B is a Cantor-winning set or is
winning in some other game."

**Headline.**  `FurstenbergLogAvoid`: some irrational `α` and `c > 0` have
`‖qα‖ ≥ c / log q` for every `q ∈ Σ`, `q ≥ 2`.  Since `s_q ≈ exp(√(2 log 2 log 3 · q))`, this is
`inf √q ||s_q α|| > 0`: the homogeneous Peres–Schlag bound with the `log q` (i.e. `log log s`)
factor removed, the improvement Moshchevitin predicts.

**English proof sketch (not a proof).**  Nested `K`-adic windows as in `UniformBad`.  Stage `k`
carries the obstacles `|α − a/q| < c/(q log q)` with `q ∈ Σ ∩ [K^{k−1}, K^k)`: about `k`
denominators (`band_unique_u`), at most two obstacles each per window, each of relative size
about `c/k`.  Their total relative length is `O(c)`, so a constant fraction of each window is
free.  What is missing is a carrying rule that does not pay a power (`√` potential: rate
`(log q)^{−2}`; exponent-`γ` potential: `(log q)^{−1/γ}`, Badziahin–Harrap strength) or a log
(Lovász local lemma: Peres–Schlag, `log q · log log q`).  The homogeneous structure (obstacles sit
at reduced `S`-rationals `a/2ᵘ3ᵛ`, and `‖2qα‖ ≤ 2‖qα‖`) is the only extra leverage identified, and
no mechanism is known that converts it into a linear-cost carrying rule.

**Confidence.**  True: 55%.  Provable in a campaign of a few weeks: 7%.  Linear forms in
logarithms are not expected to enter.
-/

namespace NormalNumbers.LinearFormsScales

open NormalNumbers.UniformBad

/-! ## Scale separation and its citation -/

/-- `|pᵐ − qⁿ| ≥ pᵐ / (C (m+n)^κ)` for all `m, n ≥ 1`: polynomial (in the exponents) separation
of the two scales. -/
def ScaleSeparation (p q : ℕ) : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    (p : ℝ) ^ m / (C * ((m + n : ℕ) : ℝ) ^ κ) ≤ |(p : ℝ) ^ m - (q : ℝ) ^ n|

/-- `p` and `q` are multiplicatively independent: `pᵃ = qᵇ` only for `a = b = 0`. -/
def MulIndep (p q : ℕ) : Prop := ∀ a b : ℕ, p ^ a = q ^ b → a = 0 ∧ b = 0

/-- **Literature (cited, referee needed).**  Baker's theorem on linear forms in two logarithms,
in the weak form `ScaleSeparation`.  Sources: A. Baker, *Linear forms in the logarithms of
algebraic numbers I–IV*, Mathematika 13–15 (1966–68); explicit two-logarithm form: M. Laurent,
M. Mignotte, Yu. Nesterenko, J. Number Theory 55 (1995) 285–321, Corollaire 2; any number of
logarithms: E. M. Matveev, Izv. Math. 64 (2000) 1217–1269, Corollary 2.3.

Derivation of this weak form (faithful-or-weaker): put `Λ = n log q − m log p ≠ 0`
(independence); Baker gives `|Λ| ≥ (m+n)^{−κ₀}` for a constant `κ₀ = κ₀(p, q)`; and
`|qⁿ − pᵐ| = pᵐ |e^Λ − 1| ≥ pᵐ · min(|Λ|/e, 1 − 1/e)`. -/
def Literature.BakerScaleSeparation : Prop :=
  ∀ p q : ℕ, 2 ≤ p → 2 ≤ q → MulIndep p q → ScaleSeparation p q

/-- The `(2, 3)` instance of the citation. -/
theorem scaleSeparation_two_three (h : Literature.BakerScaleSeparation) :
    ScaleSeparation 2 3 := by
  refine h 2 3 le_rfl (by norm_num) ?_
  intro a b hab
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp only [pow_zero] at hab
    exact ⟨rfl, (Nat.pow_eq_one.mp hab.symm).resolve_left (by norm_num)⟩
  · exfalso
    have h2 : 2 ∣ 3 ^ b := hab ▸ dvd_pow_self 2 ha.ne'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega

/-! ## Guard: the known-false sibling (a dependent pair) -/

/-- `2` and `4` are multiplicatively DEPENDENT. -/
theorem not_mulIndep_two_four : ¬ MulIndep 2 4 := by
  intro h
  have := h 2 1 (by norm_num)
  omega

/-- **Guard.**  Scale separation FAILS for the dependent pair `(2, 4)`: `2² − 4¹ = 0`.  Any
mechanism that claims to use `ScaleSeparation` must fail on this sibling, so the independence
hypothesis in `Literature.BakerScaleSeparation` is load-bearing. -/
theorem not_scaleSeparation_two_four : ¬ ScaleSeparation 2 4 := by
  rintro ⟨C, κ, hC, hκ, h⟩
  have h21 := h 2 1 (by norm_num) (by norm_num)
  norm_num at h21
  have : (0 : ℝ) < 4 / (C * (3 : ℝ) ^ κ) := by positivity
  linarith

/-! ## Furstenberg's semigroup -/

/-- Furstenberg's semigroup `Σ = {2ᵘ3ᵛ}`. -/
def furstenbergSet : Set ℕ := {q | ∃ u v : ℕ, q = 2 ^ u * 3 ^ v}

/-- **The elementary count (no Baker input).**  For fixed `v`, at most one `u` puts `2ᵘ3ᵛ` in a
dyadic band `[X, 2X)`.  Hence a band holds at most `log₃(2X) + 1` elements of `Σ`: the stage
count that `UniformBad`-type engines consume is elementary, and separation of near-coincident
scales does not change it. -/
theorem band_unique_u (X : ℝ) (v u u' : ℕ)
    (hu : X ≤ (2 : ℝ) ^ u * 3 ^ v ∧ (2 : ℝ) ^ u * 3 ^ v < 2 * X)
    (hu' : X ≤ (2 : ℝ) ^ u' * 3 ^ v ∧ (2 : ℝ) ^ u' * 3 ^ v < 2 * X) : u = u' := by
  by_contra hne
  have key : ∀ a b : ℕ, a < b → X ≤ (2 : ℝ) ^ a * 3 ^ v → (2 : ℝ) ^ b * 3 ^ v < 2 * X → False := by
    intro a b hab ha hb
    have hpow : (2 : ℝ) ^ (a + 1) ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hab
    have h3 : (0 : ℝ) < 3 ^ v := by positivity
    have : 2 * ((2 : ℝ) ^ a * 3 ^ v) ≤ 2 ^ b * 3 ^ v := by
      rw [pow_succ] at hpow
      nlinarith
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact key u u' h hu.1 hu'.2
  · exact key u' u h hu'.1 hu.2

/-- **Wiring (consumes the cited Prop): Tijdeman's gap principle for `Σ`.**  If `2ᵃ3ᵇ < 2ᵃ'3ᵇ'`
then the gap is at least `2ᵃ3ᵇ / (C · N^κ)` with `N = a + b + a' + b' + 1`, i.e. consecutive
elements of `Σ` differ by a factor `1 + (log s)^{−κ}`.  (R. Tijdeman, *On integers with many
small prime factors*, Compositio Math. 26 (1973) 319–330, proves this from Baker.) -/
theorem gap_of_scaleSeparation (h : ScaleSeparation 2 3) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a b a' b' : ℕ, (2 : ℝ) ^ a * 3 ^ b < 2 ^ a' * 3 ^ b' →
      (2 : ℝ) ^ a * 3 ^ b / (C * ((a + b + a' + b' + 1 : ℕ) : ℝ) ^ κ)
        ≤ 2 ^ a' * 3 ^ b' - 2 ^ a * 3 ^ b := by
  obtain ⟨C, κ, hC, hκ, hsep⟩ := h
  simp only [Nat.cast_ofNat] at hsep
  refine ⟨max C 1, κ, lt_of_lt_of_le one_pos (le_max_right _ _), hκ, ?_⟩
  intro a b a' b' hlt
  set N : ℝ := ((a + b + a' + b' + 1 : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Nat.le_add_left 1 _
  have hNk : (1 : ℝ) ≤ N ^ κ := Real.one_le_rpow hN1 hκ.le
  have hD1 : (1 : ℝ) ≤ max C 1 * N ^ κ :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) hNk
  have hDpos : (0 : ℝ) < max C 1 * N ^ κ := lt_of_lt_of_le one_pos hD1
  have hs0 : (0 : ℝ) < 2 ^ a * 3 ^ b := by positivity
  -- comparison of a separation denominator with the uniform one
  have hcmp : ∀ x y : ℕ, 1 ≤ x + y → x + y ≤ a + b + a' + b' + 1 →
      C * ((x + y : ℕ) : ℝ) ^ κ ≤ max C 1 * N ^ κ := by
    intro x y hxy1 hxyN
    apply mul_le_mul (le_max_left _ _) _ (by positivity) (by positivity)
    exact Real.rpow_le_rpow (by positivity) (by rw [hNdef]; exact_mod_cast hxyN) hκ.le
  rcases le_or_gt a a' with ha | ha <;> rcases le_or_gt b b' with hb | hb
  · -- s divides s': the gap is at least s
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
    have hf : (2 : ℝ) ^ (a + x) * 3 ^ (b + y) = (2 ^ a * 3 ^ b) * ((2 ^ x * 3 ^ y : ℕ) : ℝ) := by
      push_cast; ring
    rw [hf] at hlt ⊢
    have hfgt : (1 : ℝ) < ((2 ^ x * 3 ^ y : ℕ) : ℝ) := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have hf2 : (2 : ℝ) ≤ ((2 ^ x * 3 ^ y : ℕ) : ℝ) := by
      have : 1 < 2 ^ x * 3 ^ y := by exact_mod_cast hfgt
      exact_mod_cast this
    have hgap : 2 ^ a * 3 ^ b ≤ (2 ^ a * 3 ^ b) * ((2 ^ x * 3 ^ y : ℕ) : ℝ) - 2 ^ a * 3 ^ b := by
      nlinarith
    calc (2 : ℝ) ^ a * 3 ^ b / (max C 1 * N ^ κ) ≤ 2 ^ a * 3 ^ b :=
          div_le_self hs0.le hD1
      _ ≤ _ := hgap
  · -- a ≤ a', b' < b: s = g 3^y, s' = g 2^x
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_lt hb
    set g : ℝ := (2 : ℝ) ^ a * 3 ^ b' with hg
    have hgpos : 0 < g := by positivity
    have hs : (2 : ℝ) ^ a * 3 ^ (b' + y + 1) = g * 3 ^ (y + 1) := by rw [hg]; ring
    have hs' : (2 : ℝ) ^ (a + x) * 3 ^ b' = g * 2 ^ x := by rw [hg]; ring
    rw [hs, hs'] at hlt ⊢
    have hxy : (3 : ℝ) ^ (y + 1) < 2 ^ x := by
      by_contra hcon; push Not at hcon; nlinarith
    have hx1 : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0
        have : (1 : ℝ) < 3 ^ (y + 1) := one_lt_pow₀ (by norm_num) (by omega)
        simp at hxy; linarith
      · exact h0
    have hsx := hsep x (y + 1) hx1 (by omega)
    rw [abs_of_pos (by linarith)] at hsx
    have hden := hcmp x (y + 1) (by omega) (by omega)
    have hpos1 : 0 < C * ((x + (y + 1) : ℕ) : ℝ) ^ κ := by positivity
    calc g * 3 ^ (y + 1) / (max C 1 * N ^ κ) ≤ g * 2 ^ x / (max C 1 * N ^ κ) := by
          apply div_le_div_of_nonneg_right _ hDpos.le
          nlinarith
      _ ≤ g * 2 ^ x / (C * ((x + (y + 1) : ℕ) : ℝ) ^ κ) :=
          div_le_div_of_nonneg_left (by positivity) hpos1 hden
      _ = g * (2 ^ x / (C * ((x + (y + 1) : ℕ) : ℝ) ^ κ)) := by ring
      _ ≤ g * (2 ^ x - 3 ^ (y + 1)) := mul_le_mul_of_nonneg_left hsx hgpos.le
      _ = g * 2 ^ x - g * 3 ^ (y + 1) := by ring
  · -- a' < a, b ≤ b': s = g 2^x, s' = g 3^y
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_lt ha
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
    set g : ℝ := (2 : ℝ) ^ a' * 3 ^ b with hg
    have hgpos : 0 < g := by positivity
    have hs : (2 : ℝ) ^ (a' + x + 1) * 3 ^ b = g * 2 ^ (x + 1) := by rw [hg]; ring
    have hs' : (2 : ℝ) ^ a' * 3 ^ (b + y) = g * 3 ^ y := by rw [hg]; ring
    rw [hs, hs'] at hlt ⊢
    have hxy : (2 : ℝ) ^ (x + 1) < 3 ^ y := by
      by_contra hcon; push Not at hcon; nlinarith
    have hy1 : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with h0 | h0
      · subst h0
        have : (1 : ℝ) < 2 ^ (x + 1) := one_lt_pow₀ (by norm_num) (by omega)
        simp at hxy; linarith
      · exact h0
    have hsx := hsep (x + 1) y (by omega) hy1
    rw [abs_of_neg (by linarith)] at hsx
    have hden := hcmp (x + 1) y (by omega) (by omega)
    have hpos1 : 0 < C * ((x + 1 + y : ℕ) : ℝ) ^ κ := by positivity
    calc g * 2 ^ (x + 1) / (max C 1 * N ^ κ)
        ≤ g * 2 ^ (x + 1) / (C * ((x + 1 + y : ℕ) : ℝ) ^ κ) :=
          div_le_div_of_nonneg_left (by positivity) hpos1 hden
      _ = g * (2 ^ (x + 1) / (C * ((x + 1 + y : ℕ) : ℝ) ^ κ)) := by ring
      _ ≤ g * (-(2 ^ (x + 1) - 3 ^ y)) := mul_le_mul_of_nonneg_left hsx hgpos.le
      _ = g * 3 ^ y - g * 2 ^ (x + 1) := by ring
  · -- s' divides s: impossible
    exfalso
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_lt ha
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_lt hb
    have h1 : (1 : ℝ) ≤ 2 ^ (x + 1) * 3 ^ (y + 1) := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    have : (2 : ℝ) ^ (a' + x + 1) * 3 ^ (b' + y + 1)
        = (2 ^ a' * 3 ^ b') * (2 ^ (x + 1) * 3 ^ (y + 1)) := by ring
    rw [this] at hlt
    have hpos : (0 : ℝ) < 2 ^ a' * 3 ^ b' := by positivity
    nlinarith

/-! ## Avoidance along `Σ`: the frozen headline and its siblings -/

/-- **Literature (cited, referee needed).**  H. Furstenberg, *Disjointness in ergodic theory,
minimal sets, and a problem in Diophantine approximation*, Math. Systems Theory 1 (1967) 1–49,
Part IV (Theorem IV.1 and its Diophantine corollary; elementary proof: M. Boshernitzan, Proc. AMS
122 (1994) 67–70): for irrational `α`, `{qα : q ∈ Σ}` is dense mod 1.  Weaker form used: the
orbit comes arbitrarily close to `0`. -/
def Literature.Furstenberg1967 : Prop :=
  ∀ α : ℝ, Irrational α → ∀ ε : ℝ, 0 < ε → ∃ q ∈ furstenbergSet, dnear (q * α) < ε

/-- **Literature (cited, referee needed).**  N. G. Moshchevitin, *Density modulo 1 of sublacunary
sequences: application of Peres–Schlag's arguments*, arXiv:0709.3419 (J. Math. Sci. 2012), via
Y. Peres, W. Schlag, Bull. LMS 42 (2010), arXiv:0706.0223: the set
`{α : inf_{q∈Σ} log q log log q · ‖qα‖ > 0}` has full Hausdorff dimension (restated as such in
Gayfulin–Moshchevitin arXiv:2301.08212 §2 and Moshchevitin arXiv:1202.4539 §1.5 item 4).  Weaker
form used: one irrational point, and only `q ≥ 16` (where `log log q ≥ 1`). -/
def Literature.MoshchevitinPeresSchlag : Prop :=
  ∃ α : ℝ, Irrational α ∧ ∃ c : ℝ, 0 < c ∧ ∀ q ∈ furstenbergSet, 16 ≤ q →
    c / (Real.log q * Real.log (Real.log q)) ≤ dnear (q * α)

/-- **Literature (cited, referee needed).**  D. Badziahin, S. Harrap, *Cantor-winning sets and
their applications*, arXiv:1503.04738v3, Theorem 17: for multiplicatively independent `a, b` and
every `ε > 0`, `Bad_{×a,×b}((log* q)^{1+ε}) ∩ [0,1]` is `ε/(1+ε)`-Cantor-winning (hence
uncountable).  Weaker form used: `(a, b) = (2, 3)`, one irrational point, `q ≥ 3`. -/
def Literature.BadziahinHarrap17 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, Irrational α ∧ ∃ c : ℝ, 0 < c ∧ ∀ q ∈ furstenbergSet, 3 ≤ q →
    c / Real.log q ^ (1 + ε) ≤ dnear (q * α)

/-- Avoidance of `0` along `Σ` at a CONSTANT rate.  False for irrational points (Furstenberg). -/
def ConstAvoid : Prop :=
  ∃ α : ℝ, Irrational α ∧ ∃ c : ℝ, 0 < c ∧ ∀ q ∈ furstenbergSet, c ≤ dnear (q * α)

/-- **The headline statement**: avoidance along `Σ` at rate `c / log q`.  See the module
docstring for the exact source wording and the confidence. -/
def FurstenbergLogAvoid : Prop :=
  ∃ α : ℝ, Irrational α ∧ ∃ c : ℝ, 0 < c ∧ ∀ q ∈ furstenbergSet, 2 ≤ q →
    c / Real.log q ≤ dnear (q * α)

/-- **HEADLINE (frozen, open).**  Some irrational `α` has `‖qα‖ ≥ c / log q` for all
`q = 2ᵘ3ᵛ ≥ 2`: the homogeneous Peres–Schlag bound for Furstenberg's sequence with the
`log log q` loss removed (Moshchevitin arXiv:1202.4539 §1.5 item 4 predicts an improvement).
Confidence: true 55%; provable in a campaign 7%.  Frozen statement: do not weaken, re-hypothesize,
rename or delete. -/
theorem furstenbergLogAvoid_holds : FurstenbergLogAvoid := by
  sorry

/-- **Wiring.**  The headline implies the published Moshchevitin / Peres–Schlag bound, so it is
a strengthening, never a restatement. -/
theorem moshchevitinPeresSchlag_of_logAvoid (h : FurstenbergLogAvoid) :
    Literature.MoshchevitinPeresSchlag := by
  obtain ⟨α, hα, c, hc, h⟩ := h
  refine ⟨α, hα, c, hc, fun q hq h16 => ?_⟩
  have hq16 : (16 : ℝ) ≤ q := by exact_mod_cast h16
  have hlog16 : Real.exp 1 ≤ Real.log q := by
    have h1 : Real.log 16 ≤ Real.log q := Real.log_le_log (by norm_num) hq16
    have h2 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have h3 := Real.log_two_gt_d9
    have h4 := Real.exp_one_lt_d9
    linarith
  have hL : 0 < Real.log q := lt_of_lt_of_le (Real.exp_pos 1) hlog16
  have hLL : 1 ≤ Real.log (Real.log q) := (Real.le_log_iff_exp_le hL).mpr hlog16
  calc c / (Real.log q * Real.log (Real.log q)) ≤ c / Real.log q := by
        apply div_le_div_of_nonneg_left hc.le hL
        nlinarith
    _ ≤ dnear (q * α) := h q hq (by omega)

/-- **Wiring.**  The headline also implies the Badziahin–Harrap `(log q)^{1+ε}` bound. -/
theorem badziahinHarrap_of_logAvoid (h : FurstenbergLogAvoid) :
    Literature.BadziahinHarrap17 := by
  intro ε hε
  obtain ⟨α, hα, c, hc, h⟩ := h
  refine ⟨α, hα, c, hc, fun q hq h3 => ?_⟩
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast h3
  have hL1 : 1 ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hpow : Real.log q ≤ Real.log q ^ (1 + ε) := by
    calc Real.log q = Real.log q ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log q ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  calc c / Real.log q ^ (1 + ε) ≤ c / Real.log q :=
        div_le_div_of_nonneg_left hc.le (by linarith) hpow
    _ ≤ dnear (q * α) := h q hq (by omega)

/-- **Guard (independent pair).**  Cited Furstenberg kills a constant rate, so the headline's
rate must tend to `0`: any mechanism for the headline that would also give `ConstAvoid` is wrong. -/
theorem not_constAvoid_of_furstenberg (hF : Literature.Furstenberg1967) : ¬ ConstAvoid := by
  rintro ⟨α, hα, c, hc, h⟩
  obtain ⟨q, hq, hlt⟩ := hF α hα c hc
  linarith [h q hq]

/-- **Sibling (dependent pair).**  Along the powers of `2` (the semigroup `{2ᵘ4ᵛ}`), the point
`1/3` stays at distance `≥ 1/3` from the integers: for a dependent pair a CONSTANT rate holds, so
the difficulty of the headline is Furstenberg's independence, not separation of scales. -/
theorem constAvoid_powersOfTwo (k : ℕ) : 1 / 3 ≤ dnear ((2 : ℝ) ^ k * (1 / 3)) := by
  unfold dnear
  set z : ℤ := round ((2 : ℝ) ^ k * (1 / 3))
  have hw : ((2 : ℤ) ^ k - 3 * z) ≠ 0 := by
    intro h0
    have h3 : (3 : ℤ) ∣ (2 : ℤ) ^ k := ⟨z, by linarith⟩
    have h3' : (3 : ℕ) ∣ 2 ^ k := by exact_mod_cast h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
    omega
  have h1 : (1 : ℤ) ≤ |(2 : ℤ) ^ k - 3 * z| := Int.one_le_abs hw
  have h1' : (1 : ℝ) ≤ |(2 : ℝ) ^ k - 3 * z| := by exact_mod_cast h1
  have heq : (2 : ℝ) ^ k * (1 / 3) - z = ((2 : ℝ) ^ k - 3 * z) / 3 := by ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith

end NormalNumbers.LinearFormsScales
