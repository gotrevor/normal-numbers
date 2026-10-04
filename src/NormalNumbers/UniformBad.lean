/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Bugeaud 10.36: one number, uniformly badly approximable to every integer base

**Source.**  Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge
Tracts in Math. 193 (2012), p. 219, verbatim:

> By Theorem 7.8, there exist real numbers which are b-badly approximable for every b ≥ 2.
> **Problem 10.36.** There exist a real number ξ and a positive real number c such that
> ‖bⁿξ‖ > b^{−c} for every base b ≥ 2 and every integer n ≥ 0 (resp., every integer n
> sufficiently large in terms of b).

The book's best known result, p. 149, **Theorem 7.8** ("essentially proved by Akhunzhanov",
Mat. Zametki 72 (2002) and 76 (2004)), verbatim: "There are uncountably many real numbers ξ
such that |ξ − p/q| > 1/(2¹⁵ q²) for all integers p, q with q ≥ 1, (7.15) and
‖ξbⁿ‖ > b^{−1100 b (log 3b)} for all integers b ≥ 2 and n ≥ 1. (7.16)"  Its proof plays
Schmidt's `(α, β)`-game base by base; the countable-intersection step is what lets the
constant decay super-exponentially in `b`.

**Headline.**  `bugeaud_10_36` is the problem as posed (the strong reading, every `n ≥ 0`);
`bugeaud_10_36_eventually` is the "resp." reading, a corollary.  Both rest on
`exists_uniformBad_allBases_24`: some `ξ ∈ [1/4, 3/4]` has `‖bⁿξ‖ > b^{−24}` for every `b ≥ 2`
and `n ≥ 0`.  `bugeaud_7_16_of_uniformBad24` checks that this strengthens (7.16).

**Freshness (2026-10-03 audit, about 60% that no written proof exists).**  No paper found
states a uniform `b^{−c}`, and none after 2012 calls 10.36 open or solved.  Closest:
Akhunzhanov `exp(−5000 b (log b)²)` (quoted in Bugeaud, Rev. Mat. Iberoam. 28 (2012) §3);
Broderick–Bugeaud–Fishman–Kleinbock–Weiss, MRL 2010 (arXiv 0909.4251), `exp(−κ b (log b)²)` on
fractals; Peres–Schlag, Bull. LMS 2010 (arXiv 0706.0223) Thm 2 and Moshchevitin arXiv 0709.3419
need a lacunary (or finite-union-of-lacunary) sequence with a uniform or monotone threshold,
and `{bⁿ}` contains every integer (`n = 1`), so neither applies.  **But the result is within
reach of published tools**: Falconer–Yavicoli, Math. Z. 301 (2022) (arXiv 2102.01186),
countable intersection of thick sets (`Σ τ_i^{−c}` small ⇒ nonempty), would give it from a
thickness bound `τ(E_b(C)) ≳ b^C` for `E_b(C) = {ξ : ‖bⁿξ‖ ≥ b^{−C} ∀ n}`.  That bound is not
in the literature (numerics only: `≈ (b−1)b^{C−1}/2`).  So experts may well call 10.36 an
exercise in post-2017 potential/thickness technology; the claim here is a written,
self-contained proof with `c = 24`, not a new method.  Instruments: OpenAlex/Semantic Scholar
citers of the book, Akhunzhanov, BBFKW, Yavicoli, Falconer–Yavicoli, BFS; arXiv API phrase
search; about 20 web searches; TeX grep of about 25 papers.  Google Scholar's full citer
list was not reached.

## Mechanism (a square-root potential on nested `K`-adic intervals, early charging)

`exists_avoid_of_stagePotential` is the generic engine.  Closed obstacles
`[c i − r i, c i + r i]` carry a *stage* `st i`.  Nested windows `J_k` of length
`ℓ_k = ℓ₀/Kᵏ`, `J_{k+1}` one of the `K` closed children of `J_k`.  The potential of `J_k` is
`Φ_k = Σ_{st i ≤ k, i meets J_k} √(r i/ℓ_k)` (`potential`).  The hypothesis is that the
obstacles *of stage `k`* meeting any window of length `ℓ_k` have potential `≤ A`, with
`A ≤ (1 − 2/√K)/√(2K)`.  The invariant `Φ_k < θ := 1/√(2K)` forces every carried obstacle to
have `r < ℓ_{k+1}/2`, so it meets at most 2 children, where its term grows by `√K`.  The
cheapest child carries old potential `≤ (2/√K)Φ_k`, plus `≤ A` of new obstacles
(`potential_step`).  In the limit point an obstacle that met `J_k` for all large `k` would
have a term `√(r/ℓ_k) → ∞`.

The application (`ctr`, `rad`, `stage`): obstacle `(b, n, a)` is
`[a/bⁿ − b^{−n−24}, a/bⁿ + b^{−n−24}]`, charged *early*, at the stage `k` with
`64^{k−1} ≤ bⁿ < 64^k`, where its relative size is `≤ 128 b^{−24}`.  At most 7 obstacles of one
base are charged to a stage and meet a given window (`encard_stage_meet_le`): at most
`⌈log_b 64⌉ ≤ 6` levels `n`, and one centre per level since the spacing `b^{−n} > 2ℓ_k` exceeds
the window.  So the stage potential is `≤ 7·√128·Σ_{b≥2} b^{−12} < 1/40` (`newPotential_le`),
below the engine's threshold `(3/4)/√128 ≈ 0.066` (`one_fortieth_le_threshold`).  The point is
that early charging puts each base's obstacles at stages where they are sparse, so the
potential sums over `b` like `Σ b^{−12}`; a game charging an obstacle at its own scale lets
infinitely many bases pile up.

## Difficulty check (known-false siblings, in the kernel)

* **Small `c` fails already at `b = 2`.**  Every `ξ` has `‖ξ‖ ≤ 1/3` or `‖2ξ‖ ≤ 1/3`
  (`dnear_le_third_or`), so no `c` with `2^{−c} ≥ 1/3`, i.e. `c ≤ log₂ 3`, works, in either
  reading (`not_uniformBad_of_third_le`, `not_uniformBad_eventually_of_third_le`; `c ≤ 1` is
  `not_uniformBad_of_le_one`).  The engine refuses it: `C ≤ log₂ 3` makes the stage potential
  of base 2 alone exceed the threshold.
* **The uniformity in `b` needs `c > 1` even after discarding finitely many bases**
  (Dirichlet, `n = 1`: `exists_large_dnear_le_inv`, `not_uniformBad_largeBases_of_le_one`).
  The engine's sum `Σ_b b^{−C/2}` needs `C > 2`, so it agrees with this direction.  The true
  threshold is not located: it lies in `[log₂ 3, 24]`.
* **Normality is impossible**: such `ξ` is disjunctive (rich) to no base, hence normal to no
  base (`not_isDisjunctive_of_uniformBad`, `not_isNormal_of_uniformBad`), consistent with
  Bugeaud's Cor. 7.9.  The mechanism claims nothing about normality.

No literature input is assumed: the file has no hypothesis `Prop`.
-/

open scoped ENNReal

namespace NormalNumbers.UniformBad

/-- Distance to the nearest integer, `‖x‖`. -/
noncomputable def dnear (x : ℝ) : ℝ := |x - round x|

theorem dnear_le_abs_sub (x : ℝ) (z : ℤ) : dnear x ≤ |x - z| := round_le x z

theorem dnear_nonneg (x : ℝ) : 0 ≤ dnear x := abs_nonneg _

theorem dnear_le_half (x : ℝ) : dnear x ≤ 1 / 2 := abs_sub_round x

/-! ## The generic avoidance engine -/

section Engine

variable {ι : Type*}

/-- The closed obstacle `[c i − r i, c i + r i]`. -/
def obstacle (c r : ι → ℝ) (i : ι) : Set ℝ := Set.Icc (c i - r i) (c i + r i)

/-- The stage-`k` window `[x, x + ℓ₀/Kᵏ]`. -/
def window (ℓ₀ : ℝ) (K k : ℕ) (x : ℝ) : Set ℝ := Set.Icc x (x + ℓ₀ / (K : ℝ) ^ k)

/-- Square-root potential of the stage-`k` window at `x`, counting the obstacles that meet it
and whose stage satisfies `P` (`(· ≤ k)` for the carried potential `Φ_k`, `(· = k)` for the
newly charged ones). -/
noncomputable def potential (c r : ι → ℝ) (st : ι → ℕ) (ℓ₀ : ℝ) (K : ℕ) (P : ℕ → Prop)
    (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' i : {i : ι // P (st i) ∧ (obstacle c r i ∩ window ℓ₀ K k x).Nonempty},
    ENNReal.ofReal (Real.sqrt (r i / (ℓ₀ / (K : ℝ) ^ k)))

/-- The invariant threshold `θ = 1/√(2K)`. -/
noncomputable def theta (K : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / Real.sqrt (2 * K))

/-- The potential is monotone in the stage predicate. -/
theorem potential_mono (c r : ι → ℝ) (st : ι → ℕ) (ℓ₀ : ℝ) (K : ℕ) {P Q : ℕ → Prop}
    (hPQ : ∀ n, P n → Q n) (k : ℕ) (x : ℝ) :
    potential c r st ℓ₀ K P k x ≤ potential c r st ℓ₀ K Q k x :=
  ENNReal.tsum_comp_le_tsum_of_injective
    (f := fun i : {i : ι // P (st i) ∧ (obstacle c r i ∩ window ℓ₀ K k x).Nonempty} =>
      (⟨i.1, hPQ _ i.2.1, i.2.2⟩ :
        {i : ι // Q (st i) ∧ (obstacle c r i ∩ window ℓ₀ K k x).Nonempty}))
    (fun a b h => Subtype.ext (congrArg Subtype.val h :))
    (fun i => ENNReal.ofReal (Real.sqrt (r i / (ℓ₀ / (K : ℝ) ^ k))))

/-- A single obstacle meeting the window bounds the potential from below. -/
theorem term_le_potential (c r : ι → ℝ) (st : ι → ℕ) (ℓ₀ : ℝ) (K : ℕ) {P : ℕ → Prop}
    {k : ℕ} {x y : ℝ} (i : ι) (hP : P (st i)) (hy : y ∈ obstacle c r i)
    (hyw : y ∈ window ℓ₀ K k x) :
    ENNReal.ofReal (Real.sqrt (r i / (ℓ₀ / (K : ℝ) ^ k))) ≤ potential c r st ℓ₀ K P k x :=
  ENNReal.le_tsum (f := fun j : {i : ι // P (st i) ∧ (obstacle c r i ∩ window ℓ₀ K k x).Nonempty} =>
    ENNReal.ofReal (Real.sqrt (r j / (ℓ₀ / (K : ℝ) ^ k)))) ⟨i, hP, y, hy, hyw⟩

/-- The set of obstacles counted by `potential`. -/
def potSet (c r : ι → ℝ) (st : ι → ℕ) (ℓ₀ : ℝ) (K : ℕ) (P : ℕ → Prop) (k : ℕ) (x : ℝ) :
    Set ι := {i | P (st i) ∧ (obstacle c r i ∩ window ℓ₀ K k x).Nonempty}

theorem potential_eq_tsum (c r : ι → ℝ) (st : ι → ℕ) (ℓ₀ : ℝ) (K : ℕ) (P : ℕ → Prop)
    (k : ℕ) (x : ℝ) :
    potential c r st ℓ₀ K P k x = ∑' i, (potSet c r st ℓ₀ K P k x).indicator
      (fun i => ENNReal.ofReal (Real.sqrt (r i / (ℓ₀ / (K : ℝ) ^ k)))) i :=
  tsum_subtype (potSet c r st ℓ₀ K P k x)
    (fun i => ENNReal.ofReal (Real.sqrt (r i / (ℓ₀ / (K : ℝ) ^ k))))

open Classical in
/-- A closed interval of length `< ℓ` meets at most two of the closed children. -/
theorem card_children_le (c r x ℓ : ℝ) (hr : 2 * r < ℓ) (K : ℕ) :
    ((Finset.range K).filter (fun j : ℕ =>
      (Set.Icc (c - r) (c + r) ∩ Set.Icc (x + j * ℓ) (x + j * ℓ + ℓ)).Nonempty)).card ≤ 2 := by
  have key : ∀ p q : ℕ, (Set.Icc (c - r) (c + r) ∩ Set.Icc (x + p * ℓ) (x + p * ℓ + ℓ)).Nonempty →
      (Set.Icc (c - r) (c + r) ∩ Set.Icc (x + q * ℓ) (x + q * ℓ + ℓ)).Nonempty → p ≤ q + 1 := by
    rintro p q ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ ⟨z, ⟨hz1, hz2⟩, hz3, hz4⟩
    by_contra h
    have : (q : ℝ) + 2 ≤ p := by exact_mod_cast (by omega : q + 2 ≤ p)
    nlinarith
  by_contra h
  push Not at h
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.1 h
  simp only [Finset.mem_filter] at ha hb hd
  have := key a b ha.2 hb.2; have := key b a hb.2 ha.2
  have := key a d ha.2 hd.2; have := key d a hd.2 ha.2
  have := key b d hb.2 hd.2; have := key d b hd.2 hb.2
  omega

/-- **Engine step.**  If the carried potential of a stage-`k` window is below `θ`, some child
window has carried potential below `θ`.

Proved.  Proof: write `Φ'_j` for the potential of child `j` (window at
`x + j ℓ_{k+1}`).  Split it as `old_j` (stage `≤ k`) plus `new_j` (stage `= k+1`); `new_j ≤ A`
by `hnew`.  An obstacle in `old_j` meets `J_k`, so its term `√(r/ℓ_k) ≤ Φ_k < θ`, i.e.
`r < ℓ_k/(2K) = ℓ_{k+1}/2`; a closed interval of length `< ℓ_{k+1}` meets at most 2 of the
closed children.  Its term in `old_j` is `√K·√(r/ℓ_k)`.  Summing over `j < K`,
`Σ_j old_j ≤ 2√K Φ_k`, so some `j` has `old_j ≤ (2/√K)Φ_k`.  Then
`Φ'_j ≤ (2/√K)Φ_k + A < (2/√K)θ + A ≤ θ` by `hA`. -/
theorem potential_step (c r : ι → ℝ) (st : ι → ℕ) {K : ℕ} (hK : 5 ≤ K) {ℓ₀ A : ℝ}
    (hℓ₀ : 0 < ℓ₀) (hA : A ≤ (1 - 2 / Real.sqrt K) / Real.sqrt (2 * K))
    (hnew : ∀ k x, potential c r st ℓ₀ K (· = k) k x ≤ ENNReal.ofReal A)
    {k : ℕ} {x : ℝ} (hk : potential c r st ℓ₀ K (· ≤ k) k x < theta K) :
    ∃ j : ℕ, j < K ∧
      potential c r st ℓ₀ K (· ≤ k + 1) (k + 1) (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1))) < theta K := by
  classical
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  set ℓ := ℓ₀ / (K : ℝ) ^ k with hℓ
  set ℓ' := ℓ₀ / (K : ℝ) ^ (k + 1) with hℓ'
  have hℓpos : 0 < ℓ := div_pos hℓ₀ (pow_pos hKpos k)
  have hℓ'pos : 0 < ℓ' := div_pos hℓ₀ (pow_pos hKpos (k + 1))
  have hℓK : ℓ = K * ℓ' := by simp only [hℓ, hℓ', pow_succ]; field_simp
  set f : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (Real.sqrt (r i / ℓ)) with hf
  set f' : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (Real.sqrt (r i / ℓ')) with hf'
  have hff' : ∀ i, f' i = ENNReal.ofReal (Real.sqrt K) * f i := by
    intro i
    simp only [hf, hf']
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul hKpos.le, hℓK]
    congr 2
    field_simp
  set Φ := potential c r st ℓ₀ K (· ≤ k) k x with hΦ
  set S : ℕ → Set ι := fun j => potSet c r st ℓ₀ K (· ≤ k) (k + 1) (x + j * ℓ') with hS
  set old : ℕ → ℝ≥0∞ := fun j => ∑' i, (S j).indicator f' i with hold
  -- split the child potential
  have hsplit : ∀ j : ℕ, potential c r st ℓ₀ K (· ≤ k + 1) (k + 1) (x + j * ℓ') ≤
      old j + potential c r st ℓ₀ K (· = k + 1) (k + 1) (x + j * ℓ') := by
    intro j
    rw [potential_eq_tsum, potential_eq_tsum, hold, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    simp only [Set.indicator_apply, potSet, hS, Set.mem_ofPred_eq]
    by_cases h1 : st i ≤ k + 1 ∧ (obstacle c r i ∩ window ℓ₀ K (k + 1) (x + j * ℓ')).Nonempty
    · rw [if_pos h1]
      rcases Nat.lt_or_ge (st i) (k + 1) with h | h
      · rw [if_pos ⟨by omega, h1.2⟩]; exact le_self_add
      · rw [if_neg (fun h' => by omega), if_pos ⟨by omega, h1.2⟩, zero_add]
    · rw [if_neg h1]; exact zero_le
  -- pointwise bound for the sum over children
  have hpt : ∀ i, ∑ j ∈ Finset.range K, (S j).indicator f' i ≤
      ENNReal.ofReal (2 * Real.sqrt K) * (potSet c r st ℓ₀ K (· ≤ k) k x).indicator f i := by
    intro i
    by_cases hi : i ∈ potSet c r st ℓ₀ K (· ≤ k) k x
    · rw [Set.indicator_of_mem hi]
      have hfi : f i < theta K := lt_of_le_of_lt
        (by obtain ⟨hP, y, hy, hyw⟩ := hi; exact term_le_potential c r st ℓ₀ K i hP hy hyw) hk
      have hθ : (0 : ℝ) < 1 / Real.sqrt (2 * K) := by positivity
      rw [hf, theta, ENNReal.ofReal_lt_ofReal_iff hθ, Real.sqrt_lt' hθ, div_pow, Real.sq_sqrt
        (by positivity), one_pow, div_lt_div_iff₀ hℓpos (by positivity), one_mul] at hfi
      have hr2 : 2 * r i < ℓ' := by
        rw [hℓK] at hfi
        have : 0 < (K : ℝ) := hKpos
        nlinarith
      have hcard := card_children_le (c i) (r i) x ℓ' hr2 K
      calc ∑ j ∈ Finset.range K, (S j).indicator f' i
          ≤ ∑ j ∈ Finset.range K, (if (Set.Icc (c i - r i) (c i + r i) ∩
              Set.Icc (x + j * ℓ') (x + j * ℓ' + ℓ')).Nonempty then f' i else 0) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [Set.indicator_apply]
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd h1.2 h2
            · exact zero_le
            · exact le_rfl
        _ = ((Finset.range K).filter (fun j : ℕ => (Set.Icc (c i - r i) (c i + r i) ∩
              Set.Icc (x + j * ℓ') (x + j * ℓ' + ℓ')).Nonempty)).card * f' i := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * f' i := by
            gcongr
            exact_mod_cast hcard
        _ = ENNReal.ofReal (2 * Real.sqrt K) * f i := by
            rw [hff', ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
    · rw [Set.indicator_of_notMem hi, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem ?_ _)
      rintro ⟨h1, y, hy, hy1, hy2⟩
      apply hi
      refine ⟨h1, y, hy, hy1.trans' ?_, hy2.trans ?_⟩
      · have := mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) hℓ'pos.le; linarith
      · have hj : (j : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.1 hj
        show x + j * ℓ' + ℓ₀ / (K:ℝ) ^ (k+1) ≤ x + ℓ₀ / (K:ℝ) ^ k
        rw [← hℓ, ← hℓ', hℓK]; nlinarith
  have hsum : ∑ j ∈ Finset.range K, old j ≤ ENNReal.ofReal (2 * Real.sqrt K) * Φ := by
    simp only [hold]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), hΦ, potential_eq_tsum,
      ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hpt
  have hKne : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  obtain ⟨j, hj, hjle⟩ := ENNReal.exists_le_of_sum_le hKne
    (f := fun j => ENNReal.ofReal K * old j)
    (g := fun _ => ENNReal.ofReal (2 * Real.sqrt K) * Φ) (by
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast]
      gcongr)
  refine ⟨j, Finset.mem_range.1 hj, lt_of_le_of_lt (hsplit j) ?_⟩
  -- arithmetic
  have hθpos : (0 : ℝ) < 1 / Real.sqrt (2 * K) := by positivity
  have hΦtop : Φ ≠ ⊤ := ne_top_of_lt hk
  have holdtop : old j ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by simp; omega)] at hjle
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦtop) (top_le_iff.1 hjle)
  set φ := Φ.toReal
  set o := (old j).toReal
  have hφ : Φ = ENNReal.ofReal φ := (ENNReal.ofReal_toReal hΦtop).symm
  have ho : old j = ENNReal.ofReal o := (ENNReal.ofReal_toReal holdtop).symm
  have hφ0 : 0 ≤ φ := ENNReal.toReal_nonneg
  have ho0 : 0 ≤ o := ENNReal.toReal_nonneg
  rw [hφ, ho, ← ENNReal.ofReal_mul hKpos.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hjle
  rw [hφ, theta, ENNReal.ofReal_lt_ofReal_iff hθpos] at hk
  set A' := max A 0
  have hsK : 2 < Real.sqrt K := by
    rw [Real.lt_sqrt (by norm_num)]; exact_mod_cast (by omega : 4 < K)
  have hA' : A' ≤ (1 - 2 / Real.sqrt K) / Real.sqrt (2 * K) := by
    refine max_le hA (div_nonneg ?_ (Real.sqrt_nonneg _))
    rw [sub_nonneg, div_le_one (by positivity)]; exact hsK.le
  calc old j + potential c r st ℓ₀ K (· = k + 1) (k + 1) (x + j * ℓ')
      ≤ ENNReal.ofReal o + ENNReal.ofReal A' := by
        rw [← ho]; gcongr; exact (hnew _ _).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (o + A') := (ENNReal.ofReal_add ho0 (le_max_right _ _)).symm
    _ < theta K := by
      rw [theta, ENNReal.ofReal_lt_ofReal_iff hθpos]
      set s := Real.sqrt K
      set t := Real.sqrt (2 * K)
      have hs : 0 < s := by positivity
      have ht : 0 < t := by positivity
      have hss : s * s = K := Real.mul_self_sqrt hKpos.le
      -- o ≤ 2 φ / s
      have ho' : o * s ≤ 2 * φ := by
        have : (s * s) * o ≤ 2 * s * φ := by rw [hss]; linarith
        nlinarith
      have hφt : φ * t < 1 := by rwa [lt_div_iff₀ ht] at hk
      have hA't : A' * t ≤ 1 - 2 / s := by rwa [le_div_iff₀ ht] at hA'
      rw [lt_div_iff₀ ht]
      have h1 : o * t * s < 2 := by nlinarith
      have h2 : o * t < 2 / s := by rw [lt_div_iff₀ hs]; linarith
      linarith

/-- **Generic avoidance engine.**  A family of closed intervals with a stage map, whose
newly charged square-root potential on every stage-`k` window is at most
`A ≤ (1 − 2/√K)/√(2K)`, is avoided by some point of the starting window.

This is the reusable hypothesis shape: a subfamily inherits `hnew` (fewer terms), so the same
engine gives the `S`-restricted version needed for Bugeaud 10.31, and the starting window is
arbitrary.

Proved from `potential_step`: `Φ₀ ≤ A < θ` from `hnew` at `k = 0` (stage
`≤ 0` is stage `= 0`).  Choose children by `potential_step`, giving windows
`J_k = [x_k, x_k + ℓ_k]`, nested, `x_k` nondecreasing and bounded; let `ξ = lim x_k ∈ ⋂ J_k`.
For an obstacle `i`, take `k ≥ st i` with `ℓ_k < 2K r_i`.  If `ξ ∈ obstacle i` then `i` meets
`J_k`, so `θ ≤ √(r_i/ℓ_k) ≤ Φ_k < θ`, a contradiction. -/
theorem exists_avoid_of_stagePotential (c r : ι → ℝ) (st : ι → ℕ) {K : ℕ} (hK : 5 ≤ K)
    {x₀ ℓ₀ A : ℝ} (hℓ₀ : 0 < ℓ₀) (hr : ∀ i, 0 < r i)
    (hA : A ≤ (1 - 2 / Real.sqrt K) / Real.sqrt (2 * K))
    (hnew : ∀ k x, potential c r st ℓ₀ K (· = k) k x ≤ ENNReal.ofReal A) :
    ∃ ξ ∈ Set.Icc x₀ (x₀ + ℓ₀), ∀ i, ξ ∉ obstacle c r i := by
  classical
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  set ℓ : ℕ → ℝ := fun k => ℓ₀ / (K : ℝ) ^ k with hℓ
  have hℓpos : ∀ k, 0 < ℓ k := fun k => div_pos hℓ₀ (pow_pos hKpos k)
  have hℓsucc : ∀ k, (K : ℝ) * ℓ (k + 1) = ℓ k := by
    intro k; simp only [hℓ, pow_succ]; field_simp
  have hθpos : (0 : ℝ) < 1 / Real.sqrt (2 * K) := by positivity
  have hAθ : A < 1 / Real.sqrt (2 * K) := by
    have h2 : 0 < 2 / Real.sqrt K := by positivity
    calc A ≤ (1 - 2 / Real.sqrt K) / Real.sqrt (2 * K) := hA
      _ < 1 / Real.sqrt (2 * K) := div_lt_div_of_pos_right (by linarith) (by positivity)
  have h0 : potential c r st ℓ₀ K (· ≤ 0) 0 x₀ < theta K :=
    calc potential c r st ℓ₀ K (· ≤ 0) 0 x₀ ≤ potential c r st ℓ₀ K (· = 0) 0 x₀ :=
          potential_mono c r st ℓ₀ K (fun n hn => Nat.le_zero.mp hn) 0 x₀
      _ ≤ ENNReal.ofReal A := hnew 0 x₀
      _ < theta K := (ENNReal.ofReal_lt_ofReal_iff hθpos).mpr hAθ
  have step := fun (k : ℕ) (x : ℝ) (hk : potential c r st ℓ₀ K (· ≤ k) k x < theta K) =>
    potential_step c r st hK hℓ₀ hA hnew hk
  let seq : ∀ k : ℕ, {x : ℝ // potential c r st ℓ₀ K (· ≤ k) k x < theta K} := fun k =>
    Nat.rec (motive := fun k => {x : ℝ // potential c r st ℓ₀ K (· ≤ k) k x < theta K})
      ⟨x₀, h0⟩
      (fun k s => ⟨s.1 + (Classical.choose (step k s.1 s.2) : ℕ) * (ℓ₀ / (K : ℝ) ^ (k + 1)),
        (Classical.choose_spec (step k s.1 s.2)).2⟩) k
  let x : ℕ → ℝ := fun k => (seq k).1
  have hpot : ∀ k, potential c r st ℓ₀ K (· ≤ k) k (x k) < theta K := fun k => (seq k).2
  have hxs : ∀ k, ∃ j : ℕ, j < K ∧ x (k + 1) = x k + j * ℓ (k + 1) := fun k =>
    ⟨_, (Classical.choose_spec (step k (seq k).1 (seq k).2)).1, rfl⟩
  have hmono : ∀ k, x k ≤ x (k + 1) := by
    intro k
    obtain ⟨j, -, hj⟩ := hxs k
    rw [hj]
    linarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (hℓpos (k + 1)).le]
  have hright : ∀ k, x (k + 1) + ℓ (k + 1) ≤ x k + ℓ k := by
    intro k
    obtain ⟨j, hj, hjx⟩ := hxs k
    rw [hjx, ← hℓsucc k]
    have : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
    nlinarith [hℓpos (k + 1)]
  have hxmono : Monotone x := monotone_nat_of_le_succ hmono
  have hranti : Antitone (fun k => x k + ℓ k) := antitone_nat_of_succ_le hright
  have hℓ0 : ℓ 0 = ℓ₀ := by simp [hℓ]
  have hx0 : x 0 = x₀ := rfl
  have hbdd : BddAbove (Set.range x) := by
    refine ⟨x₀ + ℓ₀, ?_⟩
    rintro _ ⟨k, rfl⟩
    have := hranti (Nat.zero_le k)
    simp only [hℓ0, hx0] at this
    linarith [hℓpos k]
  set ξ := ⨆ k, x k with hξ
  have hξlo : ∀ k, x k ≤ ξ := fun k => le_ciSup hbdd k
  have hξhi : ∀ k, ξ ≤ x k + ℓ k := by
    intro k
    refine ciSup_le fun m => ?_
    rcases le_total m k with hmk | hkm
    · linarith [hxmono hmk, hℓpos k]
    · linarith [hranti hkm, hℓpos m]
  have hξwin : ∀ k, ξ ∈ window ℓ₀ K k (x k) := fun k => ⟨hξlo k, hξhi k⟩
  refine ⟨ξ, ⟨hx0 ▸ hξlo 0, by have := hξhi 0; rwa [hℓ0, hx0] at this⟩, ?_⟩
  intro i hi
  have hri := hr i
  obtain ⟨k₁, hk₁⟩ := pow_unbounded_of_one_lt (ℓ₀ / (2 * K * r i)) hK1
  set k := max k₁ (st i)
  have hKk : (K : ℝ) ^ k₁ ≤ (K : ℝ) ^ k := pow_le_pow_right₀ hK1.le (le_max_left _ _)
  have hterm := term_le_potential c r st ℓ₀ K (P := (· ≤ k)) i (le_max_right _ _) hi (hξwin k)
  have hlt := lt_of_le_of_lt hterm (hpot k)
  rw [theta, ENNReal.ofReal_lt_ofReal_iff hθpos] at hlt
  have h1 : ℓ₀ < 2 * K * r i * (K : ℝ) ^ k := by
    rw [div_lt_iff₀ (by positivity)] at hk₁
    have h2Kr : (0 : ℝ) ≤ 2 * K * r i := by positivity
    linarith [mul_le_mul_of_nonneg_right hKk h2Kr]
  have hbig : 1 / (2 * K) < r i / (ℓ₀ / (K : ℝ) ^ k) := by
    rw [lt_div_iff₀ (div_pos hℓ₀ (pow_pos hKpos k)), div_mul_div_comm, one_mul,
      div_lt_iff₀ (by positivity)]
    nlinarith
  have hsq : Real.sqrt (1 / (2 * K)) < Real.sqrt (r i / (ℓ₀ / (K : ℝ) ^ k)) :=
    Real.sqrt_lt_sqrt (by positivity) hbig
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one] at hsq
  linarith

end Engine

/-! ## The application: all bases, `C = 24`, `K = 64` -/

/-- Obstacle index `(b, n, a)` with `b ≥ 2`. -/
abbrev Idx := {p : ℕ × ℕ × ℤ // 2 ≤ p.1}

/-- Centre `a / bⁿ`. -/
noncomputable def ctr (p : Idx) : ℝ := (p.1.2.2 : ℝ) / (p.1.1 : ℝ) ^ p.1.2.1

/-- Radius `b^{−(n+24)}`. -/
noncomputable def rad (p : Idx) : ℝ := ((p.1.1 : ℝ) ^ (p.1.2.1 + 24))⁻¹

/-- Early charging: obstacle `(b, n, a)` goes to the stage `k` with `64^{k−1} ≤ bⁿ < 64^k`. -/
def stage (p : Idx) : ℕ := Nat.log 64 (p.1.1 ^ p.1.2.1) + 1

theorem rad_pos (p : Idx) : 0 < rad p := by
  have hb : (0 : ℝ) < p.1.1 := by have := p.2; positivity
  exact inv_pos.mpr (pow_pos hb _)

/-- **Early charging constant.**  An obstacle charged at its stage `k` has relative size
`rad/ℓ_k ≤ 128 b^{−24}` (`ℓ_k = 64^{−k}/2`), since `64^{k−1} ≤ bⁿ`. -/
theorem rad_div_stageLen_le (p : Idx) :
    rad p / ((1 / 2) / (64 : ℝ) ^ stage p) ≤ 128 / (p.1.1 : ℝ) ^ 24 := by
  obtain ⟨⟨b, n, a⟩, hb⟩ := p
  simp only [rad, stage]
  have hL : ((64 ^ Nat.log 64 (b ^ n) : ℕ) : ℝ) ≤ ((b ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 64 (pow_ne_zero n (by omega))
  push_cast at hL
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos hbpos n
  have hb24 : (0 : ℝ) < (b : ℝ) ^ 24 := pow_pos hbpos 24
  have heq : ((b : ℝ) ^ (n + 24))⁻¹ / ((1 / 2) / (64 : ℝ) ^ (Nat.log 64 (b ^ n) + 1)) =
      128 * (64 : ℝ) ^ Nat.log 64 (b ^ n) / ((b : ℝ) ^ n * (b : ℝ) ^ 24) := by
    rw [pow_add, pow_succ]
    field_simp
    ring
  rw [heq, div_le_div_iff₀ (mul_pos hbn hb24) hb24]
  have := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 128)
  nlinarith

/-- **Per-base count.**  At most 7 obstacles of one base are charged to stage `k` and meet a
given stage-`k` window (`K = 64`, `ℓ₀ = 1/2`).

Proved.  Proof: stage `k` means `64^{k−1} ≤ bⁿ < 64^k`, and at most `6` (`b = 2`) and
in general `⌈log_b 64⌉ ≤ 6` exponents `n` satisfy it.  For each `n`, the obstacle meets
`[x, x + ℓ_k]` (`ℓ_k = 64^{−k}/2`) only if `a/bⁿ ∈ [x − r, x + ℓ_k + r]` with
`r = b^{−n−24} ≤ 64^{1−k} b^{−24}`, a window of length `ℓ_k + 2r < 2ℓ_k = 64^{−k} < b^{−n}`,
the spacing of the centres; so at most one `a`. -/
theorem encard_stage_meet_le (b : ℕ) (hb : 2 ≤ b) (k : ℕ) (x : ℝ) :
    {q : ℕ × ℤ | stage ⟨(b, q.1, q.2), hb⟩ = k ∧
      (obstacle ctr rad ⟨(b, q.1, q.2), hb⟩ ∩ window (1 / 2) 64 k x).Nonempty}.encard ≤ 7 := by
  set S := {q : ℕ × ℤ | stage ⟨(b, q.1, q.2), hb⟩ = k ∧
      (obstacle ctr rad ⟨(b, q.1, q.2), hb⟩ ∩ window (1 / 2) 64 k x).Nonempty} with hS
  set N := {n : ℕ | Nat.log 64 (b ^ n) + 1 = k} with hN
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  -- level bound
  have hNle : N.encard ≤ 6 := by
    rcases N.eq_empty_or_nonempty with h | h
    · simp [h]
    set m := sInf N
    have hm : m ∈ N := Nat.sInf_mem h
    have hsub : N ⊆ (Finset.Ico m (m + 6) : Set ℕ) := by
      intro n hn
      simp only [Finset.coe_Ico, Set.mem_Ico]
      refine ⟨Nat.sInf_le hn, ?_⟩
      by_contra hlt
      push Not at hlt
      have hm' : Nat.log 64 (b ^ m) + 1 = k := hm
      have hn' : Nat.log 64 (b ^ n) + 1 = k := hn
      have h1 : 64 ^ Nat.log 64 (b ^ m) ≤ b ^ m := Nat.pow_log_le_self 64 (by positivity)
      have h2 : b ^ n < 64 ^ (Nat.log 64 (b ^ n) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h3 : b ^ (m + 6) ≤ b ^ n := Nat.pow_le_pow_right (by omega) hlt
      have h4 : 2 ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hb 6
      rw [hn', ← hm', pow_succ] at h2
      rw [pow_add] at h3
      have h5 := Nat.mul_le_mul h1 h4
      norm_num at h5
      linarith
    calc N.encard ≤ ((Finset.Ico m (m + 6) : Finset ℕ) : Set ℕ).encard := Set.encard_le_encard hsub
      _ = 6 := by rw [Set.encard_coe_eq_coe_finsetCard]; simp
  have hinj : Set.InjOn Prod.fst S := by
    rintro ⟨n, a⟩ ⟨hst, y, ⟨hy1, hy2⟩, hy3, hy4⟩ ⟨n', a'⟩ ⟨hst', y', ⟨hy1', hy2'⟩, hy3', hy4'⟩ hnn
    change n = n' at hnn
    subst hnn
    change Nat.log 64 (b ^ n) + 1 = k at hst
    simp only [ctr, rad, Nat.cast_ofNat] at hy1 hy2 hy1' hy2' hy4 hy4'
    have hlt : b ^ n < 64 ^ k := by
      rw [← hst]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hlt' : ((b : ℝ) ^ n) < (64 : ℝ) ^ k := by exact_mod_cast hlt
    have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos hbpos n
    have h24 : (16 : ℝ) ≤ (b : ℝ) ^ 24 := by
      have : (2 : ℝ) ^ 24 ≤ (b : ℝ) ^ 24 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb) 24
      norm_num at this; linarith
    set u := (b : ℝ) ^ n
    -- r ≤ 1/(16 u)
    have hr : ((b : ℝ) ^ (n + 24))⁻¹ * u ≤ 1 / 16 := by
      rw [pow_add, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hbn.ne', one_mul]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    -- ℓ u < 1/2
    have hℓ : 1 / 2 / (64 : ℝ) ^ k * u < 1 / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    have hd : |(a : ℝ) - a'| < 1 := by
      have e : (a : ℝ) - a' = (a / u - a' / u) * u := by field_simp
      rw [e, abs_mul, abs_of_pos hbn]
      have : |(a : ℝ) / u - a' / u| ≤ 1 / 2 / (64 : ℝ) ^ k + 2 * ((b : ℝ) ^ (n + 24))⁻¹ := by
        rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg ((a : ℝ) / u - a' / u)]
    have : a = a' := by
      have := abs_lt.1 hd
      have h1 : a - a' < 1 := by exact_mod_cast (by push_cast; linarith : ((a - a' : ℤ) : ℝ) < 1)
      have h2 : -1 < a - a' := by exact_mod_cast (by push_cast; linarith : (-1 : ℝ) < ((a - a' : ℤ) : ℝ))
      omega
    rw [this]
  have himg : Prod.fst '' S ⊆ N := by
    rintro _ ⟨q, hq, rfl⟩; exact hq.1
  calc S.encard = (Prod.fst '' S).encard := (hinj.encard_image).symm
    _ ≤ N.encard := Set.encard_le_encard himg
    _ ≤ 6 := hNle
    _ ≤ 7 := by norm_num

/-- The base-weight sum: `Σ_{b≥2} 7·12/b¹² ≤ 1/40` (the `b = 2` term plus `ζ(2)` for `b ≥ 3`). -/
theorem tsum_base_weight_le :
    ∑' b : ℕ, (if 2 ≤ b then 7 * ENNReal.ofReal (12 / (b : ℝ) ^ 12) else 0) ≤
      ENNReal.ofReal (1 / 40) := by
  have hpt : ∀ b : ℕ, (if 2 ≤ b then 7 * ENNReal.ofReal (12 / (b : ℝ) ^ 12) else 0) ≤
      (if b = 2 then ENNReal.ofReal (84 / 4096) else 0) +
        ENNReal.ofReal (84 / 3 ^ 10 * (1 / (b : ℝ) ^ 2)) := by
    intro b
    split_ifs with h1 h2
    · subst h2; norm_num
      rw [← ENNReal.ofReal_ofNat 7, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
    · have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast (by omega : 3 ≤ b)
      rw [zero_add, ← ENNReal.ofReal_ofNat 7, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hb : (0 : ℝ) < b := by linarith
      have h10 : (3 : ℝ) ^ 10 ≤ (b : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hb3 10
      rw [show (b : ℝ) ^ 12 = (b : ℝ) ^ 10 * (b : ℝ) ^ 2 by ring]
      rw [show 7 * (12 / ((b : ℝ) ^ 10 * (b : ℝ) ^ 2)) = 84 / (b : ℝ) ^ 10 * (1 / (b : ℝ) ^ 2) by
        field_simp; norm_num]
      gcongr
    · exact zero_le
    · exact zero_le
  have hz : ∑' b : ℕ, ENNReal.ofReal (84 / 3 ^ 10 * (1 / (b : ℝ) ^ 2)) =
      ENNReal.ofReal (84 / 3 ^ 10 * (Real.pi ^ 2 / 6)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => by positivity)
      ((hasSum_zeta_two.mul_left _).summable), (hasSum_zeta_two.mul_left _).tsum_eq]
  calc _ ≤ ∑' b : ℕ, ((if b = 2 then ENNReal.ofReal (84 / 4096) else 0) +
        ENNReal.ofReal (84 / 3 ^ 10 * (1 / (b : ℝ) ^ 2))) := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (84 / 4096) + ENNReal.ofReal (84 / 3 ^ 10 * (Real.pi ^ 2 / 6)) := by
        rw [ENNReal.tsum_add, tsum_ite_eq, hz]
    _ = ENNReal.ofReal (84 / 4096 + 84 / 3 ^ 10 * (Real.pi ^ 2 / 6)) :=
        (ENNReal.ofReal_add (by norm_num) (by positivity)).symm
    _ ≤ ENNReal.ofReal (1 / 40) := by
        apply ENNReal.ofReal_le_ofReal
        have := Real.pi_lt_d2
        have := Real.pi_pos
        nlinarith

/-- **Stage potential.**  The newly charged obstacles of the all-bases family have square-root
potential `≤ 1/40` on every stage-`k` window.

Proved.  Proof: an obstacle `(b, n, a)` charged at stage `k` has
`rad/ℓ_k ≤ 128 b^{−24}` (`rad_div_stageLen_le`, proved), so its term is `≤ √128·b^{−12}`.  Split the tsum by
base (`Idx ≃ Σ b, ...`); by `encard_stage_meet_le` base `b` contributes at most 7 terms.  So
the potential is `≤ 7√128 Σ_{b≥2} b^{−12} ≤ 7·11.32·2^{−12}(1 + 2/11) < 0.023 < 1/40`, using
`Σ_{b≥3} b^{−12} ≤ ∫_2^∞ t^{−12} dt = 2^{−11}/11`. -/
theorem newPotential_le (k : ℕ) (x : ℝ) :
    potential ctr rad stage (1 / 2) 64 (· = k) k x ≤ ENNReal.ofReal (1 / 40) := by
  classical
  set T := potSet ctr rad stage (1 / 2) 64 (· = k) k x with hT
  set g : Idx → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (Real.sqrt (rad i / (1 / 2 / ((64 : ℕ) : ℝ) ^ k))) with hg
  set w : ℕ → ℝ≥0∞ := fun b => ENNReal.ofReal (12 / (b : ℝ) ^ 12) with hw
  have hgw : ∀ t : T, g t ≤ w t.1.1.1 := by
    rintro ⟨i, hik, -⟩
    have h := rad_div_stageLen_le i
    change stage i = k at hik
    rw [hik] at h
    apply ENNReal.ofReal_le_ofReal
    have hb : (0 : ℝ) < i.1.1 := by have := i.2; exact_mod_cast (by omega : 0 < i.1.1)
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    push_cast
    refine h.trans ?_
    rw [div_pow, ← pow_mul]
    gcongr; norm_num
  have hfib : ∀ b : ℕ, ((fun t : T => t.1.1.1) ⁻¹' {b}).encard ≤ if 2 ≤ b then 7 else 0 := by
    intro b
    split_ifs with hb
    · set F := {q : ℕ × ℤ | stage ⟨(b, q.1, q.2), hb⟩ = k ∧
        (obstacle ctr rad ⟨(b, q.1, q.2), hb⟩ ∩ window (1 / 2) 64 k x).Nonempty}
      have hinj : Set.InjOn (fun t : T => (t.1.1.2.1, t.1.1.2.2))
          ((fun t : T => t.1.1.1) ⁻¹' {b}) := by
        rintro ⟨⟨⟨b1, n1, a1⟩, h1⟩, _⟩ hb1 ⟨⟨⟨b2, n2, a2⟩, h2⟩, _⟩ hb2 he
        change b1 = b at hb1; change b2 = b at hb2
        simp only [Prod.mk.injEq] at he
        subst hb1 hb2; obtain ⟨rfl, rfl⟩ := he; rfl
      have himg : (fun t : T => (t.1.1.2.1, t.1.1.2.2)) ''
          ((fun t : T => t.1.1.1) ⁻¹' {b}) ⊆ F := by
        rintro _ ⟨⟨⟨⟨b1, n1, a1⟩, h1⟩, ht⟩, hb1, rfl⟩
        change b1 = b at hb1
        subst hb1
        exact ht
      calc _ = _ := (hinj.encard_image).symm
        _ ≤ F.encard := Set.encard_le_encard himg
        _ ≤ 7 := encard_stage_meet_le b hb k x
    · rw [nonpos_iff_eq_zero, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      rintro ⟨⟨⟨b1, n1, a1⟩, h1⟩, _⟩ hb1
      change b1 = b at hb1
      omega
  show ∑' t : T, g t ≤ _
  rw [← ENNReal.tsum_fiberwise _ (fun t : T => t.1.1.1)]
  calc ∑' b, ∑' t : (fun t : T => t.1.1.1) ⁻¹' {b}, g t
      ≤ ∑' b, ∑' t : (fun t : T => t.1.1.1) ⁻¹' {b}, w b := by
        refine ENNReal.tsum_le_tsum fun b => ENNReal.tsum_le_tsum fun t => ?_
        have := hgw t.1; have h2 : (t.1.1.1.1 : ℕ) = b := t.2; rwa [h2] at this
    _ = ∑' b, ((fun t : T => t.1.1.1) ⁻¹' {b}).encard * w b := by
        simp_rw [ENNReal.tsum_set_const]
    _ ≤ ∑' b : ℕ, (if 2 ≤ b then 7 * w b else 0) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        have h := hfib b
        split_ifs with hb
        · rw [if_pos hb] at h
          gcongr
          exact_mod_cast h
        · rw [if_neg hb, nonpos_iff_eq_zero] at h
          simp [h]
    _ ≤ _ := tsum_base_weight_le

/-- The engine threshold for `K = 64` clears `1/40`. -/
theorem one_fortieth_le_threshold :
    (1 / 40 : ℝ) ≤ (1 - 2 / Real.sqrt (64 : ℕ)) / Real.sqrt (2 * (64 : ℕ)) := by
  have h64 : Real.sqrt ((64 : ℕ) : ℝ) = 8 := by
    rw [show ((64 : ℕ) : ℝ) = 8 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h128 : Real.sqrt (2 * ((64 : ℕ) : ℝ)) ≤ 30 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hpos : 0 < Real.sqrt (2 * ((64 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by norm_num)
  rw [h64, le_div_iff₀ hpos]
  have := mul_le_mul_of_nonneg_left h128 (by norm_num : (0 : ℝ) ≤ 1 / 40)
  norm_num at this ⊢
  linarith

/-- **`C = 24`.**  Some `ξ ∈ [1/4, 3/4]` has `‖bⁿξ‖ > b^{−24}` for every base `b ≥ 2` and every
`n ≥ 0`.  Wiring: the engine with `K = 64`, `x₀ = 1/4`, `ℓ₀ = 1/2`, `A = 1/40`; the avoided
obstacle at `a = round(bⁿξ)` is exactly the inequality. -/
theorem exists_uniformBad_allBases_24 :
    ∃ ξ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4), ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ,
      (b : ℝ) ^ (-(24 : ℝ)) < dnear ((b : ℝ) ^ n * ξ) := by
  obtain ⟨ξ, hξ, havoid⟩ := exists_avoid_of_stagePotential ctr rad stage (K := 64) (by norm_num)
    (x₀ := 1 / 4) (ℓ₀ := 1 / 2) (A := 1 / 40) (by norm_num) rad_pos one_fortieth_le_threshold
    newPotential_le
  refine ⟨ξ, ⟨hξ.1, by linarith [hξ.2]⟩, fun b hb n => ?_⟩
  have hbpos : (0 : ℝ) < b := by positivity
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos hbpos n
  have h := havoid ⟨(b, n, round ((b : ℝ) ^ n * ξ)), hb⟩
  simp only [obstacle, ctr, rad, Set.mem_Icc, not_and_or, not_le] at h
  have hrpow : (b : ℝ) ^ (-(24 : ℝ)) = ((b : ℝ) ^ 24)⁻¹ := by
    rw [Real.rpow_neg hbpos.le]; norm_cast
  rw [hrpow, dnear]
  have hpow : ((b : ℝ) ^ (n + 24))⁻¹ * (b : ℝ) ^ n = ((b : ℝ) ^ 24)⁻¹ := by
    rw [pow_add]; field_simp
  set m : ℝ := (round ((b : ℝ) ^ n * ξ) : ℝ)
  have e1 : (b : ℝ) ^ n * (m / (b : ℝ) ^ n) = m := by field_simp
  have e2 : (b : ℝ) ^ n * ((b : ℝ) ^ (n + 24))⁻¹ = ((b : ℝ) ^ 24)⁻¹ := by
    rw [mul_comm]; exact hpow
  have hinv : 0 < ((b : ℝ) ^ 24)⁻¹ := by positivity
  rcases h with h | h
  · -- ξ < m/bⁿ − r, so bⁿξ < m − b^{−24}
    have := mul_lt_mul_of_pos_left h hbn
    rw [mul_sub, e1, e2] at this
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · have := mul_lt_mul_of_pos_left h hbn
    rw [mul_add, e1, e2] at this
    rw [abs_of_pos (by linarith)]
    linarith

/-- **Bugeaud 2012, Problem 10.36, as posed (strong reading).**  There exist a real `ξ` and
`c > 0` with `‖bⁿξ‖ > b^{−c}` for every base `b ≥ 2` and every integer `n ≥ 0`. -/
theorem bugeaud_10_36 :
    ∃ ξ : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ,
      (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by
  obtain ⟨ξ, -, h⟩ := exists_uniformBad_allBases_24
  exact ⟨ξ, 24, by norm_num, h⟩

/-- **Bugeaud 2012, Problem 10.36, "resp." reading**: every `n` sufficiently large in terms of
`b`.  Immediate from `bugeaud_10_36`. -/
theorem bugeaud_10_36_eventually :
    ∃ ξ : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ b : ℕ, 2 ≤ b → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by
  obtain ⟨ξ, c, hc, h⟩ := bugeaud_10_36
  exact ⟨ξ, c, hc, fun b hb => ⟨0, fun n _ => h b hb n⟩⟩

/-- Cross-check against the book: `C = 24` implies Akhunzhanov's (7.16),
`‖ξbⁿ‖ > b^{−1100 b log 3b}` for `b ≥ 2`, `n ≥ 1`. -/
theorem bugeaud_7_16_of_uniformBad24 {ξ : ℝ}
    (h : ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, (b : ℝ) ^ (-(24 : ℝ)) < dnear ((b : ℝ) ^ n * ξ))
    (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (_hn : 1 ≤ n) :
    (b : ℝ) ^ (-(1100 * b * Real.log (3 * b))) < dnear (ξ * (b : ℝ) ^ n) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hlog : 1 ≤ Real.log (3 * b) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hexp : -(1100 * (b : ℝ) * Real.log (3 * b)) ≤ -(24 : ℝ) := by
    nlinarith
  rw [show ξ * (b : ℝ) ^ n = (b : ℝ) ^ n * ξ from mul_comm _ _]
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hb1 hexp) (h b hb n)

/-! ## Guards: known-false siblings -/

/-- Every `ξ` has `‖ξ‖ ≤ 1/3` or `‖2ξ‖ ≤ 1/3`. -/
theorem dnear_le_third_or (ξ : ℝ) : dnear ξ ≤ 1 / 3 ∨ dnear (2 * ξ) ≤ 1 / 3 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have ht : |ξ - round ξ| ≤ 1 / 2 := abs_sub_round ξ
  have h1' : 1 / 3 < |ξ - round ξ| := h1
  rcases le_or_gt 0 (ξ - round ξ) with hs | hs
  · rw [abs_of_nonneg hs] at ht h1'
    have key : |2 * ξ - ((2 * round ξ + 1 : ℤ) : ℝ)| < 1 / 3 := by
      push_cast; rw [abs_lt]; constructor <;> linarith
    linarith [dnear_le_abs_sub (2 * ξ) (2 * round ξ + 1)]
  · rw [abs_of_neg hs] at ht h1'
    have key : |2 * ξ - ((2 * round ξ - 1 : ℤ) : ℝ)| < 1 / 3 := by
      push_cast; rw [abs_lt]; constructor <;> linarith
    linarith [dnear_le_abs_sub (2 * ξ) (2 * round ξ - 1)]

/-- **Guard (base 2 alone).**  No `c` with `2^{−c} ≥ 1/3` (i.e. `c ≤ log₂ 3`) works. -/
theorem not_uniformBad_of_third_le {c : ℝ} (hc : (1 : ℝ) / 3 ≤ (2 : ℝ) ^ (-c)) :
    ¬ ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by
  rintro ⟨ξ, h⟩
  have h0 := h 2 le_rfl 0
  have h1 := h 2 le_rfl 1
  simp only [pow_zero, one_mul, pow_one, Nat.cast_ofNat] at h0 h1
  rcases dnear_le_third_or ξ with h' | h' <;> linarith

/-- **Guard, "resp." reading.**  Also false for `2^{−c} ≥ 1/3` when only large `n` count. -/
theorem not_uniformBad_eventually_of_third_le {c : ℝ} (hc : (1 : ℝ) / 3 ≤ (2 : ℝ) ^ (-c)) :
    ¬ ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by
  rintro ⟨ξ, h⟩
  obtain ⟨N, hN⟩ := h 2 le_rfl
  have h0 := hN N le_rfl
  have h1 := hN (N + 1) (by omega)
  simp only [Nat.cast_ofNat] at h0 h1
  rw [pow_succ, mul_comm ((2 : ℝ) ^ N) 2, mul_assoc] at h1
  rcases dnear_le_third_or ((2 : ℝ) ^ N * ξ) with h' | h' <;> linarith

/-- **Guard.**  `c ≤ 1` is impossible (the sweep's "Dirichlet" sibling; base 2 already kills
it). -/
theorem not_uniformBad_of_le_one {c : ℝ} (hc : c ≤ 1) :
    ¬ ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by
  apply not_uniformBad_of_third_le
  have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_neg_one] at this
  linarith

/-- **Dirichlet, large bases.**  Every `ξ` has `‖bξ‖ ≤ 1/b` for arbitrarily large `b`.

Proof: if `‖kξ‖ = 0` for some `1 ≤ k < B' = max(B, 2)`, take `b = B'k`.  Otherwise
`δ = min_{1 ≤ k < B'} ‖kξ‖ > 0`, and Dirichlet (`Real.exists_int_int_abs_mul_sub_le`) with
`N > 1/δ` gives `1 ≤ b ≤ N` with `‖bξ‖ ≤ 1/(N+1) < δ`, forcing `b ≥ B'`, and
`‖bξ‖ ≤ 1/(N+1) ≤ 1/b`. -/
theorem exists_large_dnear_le_inv (ξ : ℝ) (B : ℕ) :
    ∃ b : ℕ, B ≤ b ∧ 2 ≤ b ∧ dnear ((b : ℝ) * ξ) ≤ 1 / b := by
  classical
  set B' := max B 2 with hB'
  have hBB' : B ≤ B' := le_max_left B 2
  have h2B' : 2 ≤ B' := le_max_right B 2
  by_cases hz : ∃ k ∈ Finset.Ico 1 B', dnear ((k : ℝ) * ξ) = 0
  · obtain ⟨k, hk, hk0⟩ := hz
    rw [Finset.mem_Ico] at hk
    refine ⟨B' * k, by nlinarith, by nlinarith, ?_⟩
    have hint : (k : ℝ) * ξ = round ((k : ℝ) * ξ) := by
      have : |(k : ℝ) * ξ - round ((k : ℝ) * ξ)| = 0 := hk0
      rwa [abs_eq_zero, sub_eq_zero] at this
    have h := dnear_le_abs_sub (((B' * k : ℕ) : ℝ) * ξ) (B' * round ((k : ℝ) * ξ))
    have h0 : ((B' * k : ℕ) : ℝ) * ξ - ((B' * round ((k : ℝ) * ξ) : ℤ) : ℝ) = 0 := by
      push_cast
      linear_combination (B' : ℝ) * hint
    rw [h0, abs_zero] at h
    have : (0 : ℝ) ≤ 1 / ((B' * k : ℕ) : ℝ) := by positivity
    linarith
  · push Not at hz
    obtain ⟨k₀, hk₀s, hmin⟩ := Finset.exists_min_image (Finset.Ico 1 B')
      (fun k : ℕ => dnear ((k : ℝ) * ξ)) ⟨1, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
    have hδ : 0 < dnear ((k₀ : ℝ) * ξ) :=
      lt_of_le_of_ne (dnear_nonneg _) (Ne.symm (hz k₀ hk₀s))
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / dnear ((k₀ : ℝ) * ξ))
    have hNpos : 0 < N := by
      have : (0 : ℝ) < N := lt_trans (by positivity) hN
      exact_mod_cast this
    obtain ⟨j, k, hk0, hkN, hkj⟩ := Real.exists_int_int_abs_mul_sub_le ξ hNpos
    lift k to ℕ using hk0.le
    push_cast at hkj hkN hk0
    have hd : dnear ((k : ℝ) * ξ) ≤ 1 / ((N : ℝ) + 1) := (dnear_le_abs_sub _ j).trans hkj
    have hNδ : 1 / ((N : ℝ) + 1) < dnear ((k₀ : ℝ) * ξ) := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hN
      nlinarith
    have hkB : B' ≤ k := by
      by_contra hlt
      push Not at hlt
      have hmem : k ∈ Finset.Ico 1 B' := Finset.mem_Ico.2 ⟨by omega, hlt⟩
      have := hmin k hmem
      linarith
    refine ⟨k, le_trans hBB' hkB, le_trans h2B' hkB, hd.trans ?_⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkN' : (k : ℝ) ≤ N + 1 := by exact_mod_cast (by omega : k ≤ N + 1)
    exact one_div_le_one_div_of_le hkpos hkN'

/-- **Guard (uniformity at large bases).**  For `c ≤ 1` no `ξ` works even after discarding
finitely many bases: the `b`-uniform constant needs `c > 1` at the large-`b` end. -/
theorem not_uniformBad_largeBases_of_le_one {c : ℝ} (hc : c ≤ 1) :
    ¬ ∃ ξ : ℝ, ∃ B : ℕ, ∀ b : ℕ, B ≤ b → 2 ≤ b → ∀ n : ℕ,
      (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by
  rintro ⟨ξ, B, h⟩
  obtain ⟨b, hBb, hb, hd⟩ := exists_large_dnear_le_inv ξ B
  have h1 := h b hBb hb 1
  rw [pow_one] at h1
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have : (b : ℝ) ^ (-1 : ℝ) ≤ (b : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  rw [Real.rpow_neg_one] at this
  rw [one_div] at hd
  linarith

/-- **Guard.**  A witness is disjunctive (rich) to no base: the orbit never enters
`[0, min(b^{−c}, 1))`. -/
theorem not_isDisjunctive_of_uniformBad {ξ c : ℝ} {b : ℕ} (hb2 : 2 ≤ b)
    (h : ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ)) : ¬ IsDisjunctive b ξ := by
  intro hd
  have hb : 0 < (b : ℝ) ^ (-c) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < b)) _
  obtain ⟨n, hn⟩ := hd 0 (min ((b : ℝ) ^ (-c)) 1) le_rfl (lt_min hb one_pos) (min_le_right _ _)
  have hn' := h n
  have hfr : dnear ((b : ℝ) ^ n * ξ) ≤ Int.fract (ξ * (b : ℝ) ^ n) := by
    have := dnear_le_abs_sub ((b : ℝ) ^ n * ξ) ⌊ξ * (b : ℝ) ^ n⌋
    rw [mul_comm ((b : ℝ) ^ n) ξ, Int.self_sub_floor,
      abs_of_nonneg (Int.fract_nonneg _)] at this
    rw [mul_comm ((b : ℝ) ^ n) ξ]
    exact this
  have : Int.fract (ξ * (b : ℝ) ^ n) < min ((b : ℝ) ^ (-c)) 1 := hn.2
  linarith [min_le_left ((b : ℝ) ^ (-c)) 1]

/-- **Guard.**  A witness is normal to no base (`IsNormal.isDisjunctive`). -/
theorem not_isNormal_of_uniformBad {ξ c : ℝ} {b : ℕ} (hb : 2 ≤ b)
    (h : ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ)) : ¬ IsNormal b ξ :=
  fun hn => not_isDisjunctive_of_uniformBad hb h (hn.isDisjunctive hb)

/-- The `S`-half of Bugeaud 10.31 for every `S` at once: an irrational number disjunctive to no
base. -/
theorem exists_irrational_not_isDisjunctive :
    ∃ ξ : ℝ, Irrational ξ ∧ ∀ b : ℕ, 2 ≤ b → ¬ IsDisjunctive b ξ := by
  obtain ⟨ξ, -, h⟩ := exists_uniformBad_allBases_24
  refine ⟨ξ, ?_, fun b hb => not_isDisjunctive_of_uniformBad hb (h b hb)⟩
  rintro ⟨q, rfl⟩
  -- `b = q.den + 1 ≥ 2`, `n = 1`, `bξ`... use `b = 2·den`, then `bξ ∈ ℤ`.
  have hb : 2 ≤ 2 * q.den := by have := q.pos; omega
  have h1 := h (2 * q.den) hb 1
  have hint : ((2 * q.den : ℕ) : ℝ) ^ 1 * (q : ℝ) = ((2 * q.num : ℤ) : ℝ) := by
    push_cast
    rw [pow_one, mul_assoc, ← Rat.cast_natCast q.den, ← Rat.cast_mul, Rat.den_mul_eq_num]
    push_cast; ring
  rw [hint] at h1
  have h0 := dnear_le_abs_sub ((2 * q.num : ℤ) : ℝ) (2 * q.num)
  rw [sub_self, abs_zero] at h0
  have := Real.rpow_nonneg (Nat.cast_nonneg (2 * q.den)) (-(24 : ℝ))
  linarith

end NormalNumbers.UniformBad
