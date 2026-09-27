/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Wall
import NormalNumbers.WeylCriterion
import NormalNumbers.WallCrux

/-!
# Wall: rational affine maps preserve normality

D. D. Wall (1949 thesis): if `x` is normal in base `b` and `q ≠ 0`, `r` are rational, then
`q * x + r` is normal in base `b`.  `Maze.lean` cited this ("normality survives rational
multiplication") as a `.cited` row; this file proves it.

## The decomposition

Everything is transported through Wall's theorem
(`isNormal_iff_equidistributed_orbit`), so the working currency is
`Equidistributed (orbit b ·)`.  Writing `q = u/v`, `r = p/w` and `V = v*w`,

    q * x + r = ((u*w) * x + v*p) / V,

so it suffices to handle an integer dilation, an integer translation, and a division by
a positive integer `V`.  Three of the four moves are cheap:

* **integer translation is free**: `orbit b (x + M) = orbit b x` for `M : ℤ`
  (`orbit_add_intCast`), because `b^n * M` is an integer;
* **integer dilation** is an interval decomposition: the preimage of `[a, c)` under
  `t ↦ {m t}` is the disjoint union of the `m` intervals `[(j+a)/m, (j+c)/m)`
  (`equidistributed_natMul`), plus a reflection for negative multipliers
  (`equidistributed_negFract`);
* **division by a `b`-smooth factor is free**: if `A ∣ b^κ`, `b^κ = A*c`, then
  `x / A = (c*x) / b^κ` and dividing by `b^κ` only shifts the orbit by `κ`
  (`equidistributed_of_shift`).

Splitting `V = A * B` with `A ∣ b^κ` and `gcd(B, b) = 1` (`exists_smooth_coprime_split`)
therefore reduces the whole theorem to one irreducible statement, the **crux**:

    IsNormal b x  →  gcd(B, b) = 1  →  IsNormal b ((x + M) / B).

## Why the crux is the crux

`orbit b ((x + M)/B) n = (r n + orbit b x n) / B` where
`r n = (⌊b^n x⌋ + b^n M) mod B` is the state of the long-division automaton.  So the
crux is exactly the *joint* equidistribution of the automaton state `r n` with the
future digits of `x` — and `r n` depends on the entire digit prefix, not on a bounded
window, which is what makes it inaccessible to a direct block count.  Weyl's criterion
does **not** linearise it: the Fourier test at frequency `h` for `(x+M)/B` is the
Fourier test at the *rational* frequency `h/B` for `x`, i.e. the same problem again.

The intended attack (recorded here so it survives the lap): since `gcd(B, b) = 1` there
is `T` with `b^T ≡ 1 (mod B)`, and then

    r (n + T*k) = r n + W (T*k) n   (mod B),   W l n = value of the digit block x[n, n+l),

so for a nontrivial additive character `χ` mod `B` the Cesàro mean
`A = lim (1/N) ∑_{n<N} χ (r n) * f (orbit b x n)` is, by shift invariance in `n`,
equal to `lim (1/N) ∑_n χ (r n) * (1/K) ∑_{k≤K} χ (W (T*k) n) * f (orbit b x (n+T*k))`.
Cauchy–Schwarz then reduces `|A|` to the off-diagonal block correlations
`(1/N) ∑_n χ (W (T*k) n) * conj (χ (W (T*k') n)) * …`, each of which is a *fixed-depth*
block average, hence computable from normality alone, and equal to a character sum over
a free digit range — geometrically small, `O(B * b^{-T*(k'-k)})`.  The engine for that
step is `tendsto_blockAverage` below.
-/

namespace NormalNumbers

open Filter Topology

namespace WallRational

/-! ### Cheap moves: translation, dilation, reflection, shift -/

/-- Fractional parts only see the fractional part, through an integer dilation. -/
theorem fract_intMul_fract (m : ℤ) (y : ℝ) :
    Int.fract ((m : ℝ) * y) = Int.fract ((m : ℝ) * Int.fract y) := by

  have h : (m : ℝ) * y = (m : ℝ) * Int.fract y + ((m * ⌊y⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_add_intCast]

/-- **Integer translations are free**: the orbit of `x + M` is the orbit of `x`. -/
theorem orbit_add_intCast (b : ℕ) (x : ℝ) (M : ℤ) (n : ℕ) :
    orbit b (x + (M : ℝ)) n = orbit b x n := by

  unfold orbit
  have h : (x + (M : ℝ)) * (b : ℝ) ^ n
      = x * (b : ℝ) ^ n + ((M * (b : ℤ) ^ n : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, Int.fract_add_intCast]

/-- The orbit of `m * x` is the `m`-dilation of the orbit of `x`. -/
theorem orbit_intMul (b : ℕ) (x : ℝ) (m : ℤ) (n : ℕ) :
    orbit b ((m : ℝ) * x) n = Int.fract ((m : ℝ) * orbit b x n) := by

  unfold orbit
  rw [← fract_intMul_fract]
  congr 1
  ring

/-- Dilating an equidistributed `[0,1)`-valued sequence by a positive integer, modulo
one, preserves equidistribution: the preimage of `[a, c)` is the disjoint union of the
`m` intervals `[(j+a)/m, (j+c)/m)`. -/
theorem equidistributed_natMul {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (h : Equidistributed u) {m : ℕ} (hm : 0 < m) :
    Equidistributed (fun k => Int.fract ((m : ℝ) * u k)) := by

  classical
  intro a c ha hac hc
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have expand : ∀ (v : ℕ → ℝ) (p q : ℝ) (n : ℕ), (visitCount v p q n : ℝ)
      = ∑ k ∈ Finset.range n, (if p ≤ v k ∧ v k < q then (1 : ℝ) else 0) := by
    intro v p q n
    rw [visitCount, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : p ≤ v k ∧ v k < q
    · simp [Set.mem_Ico, hk.1, hk.2]
    · simp [Set.mem_Ico, hk]
  have key : ∀ n : ℕ, (visitCount (fun k => Int.fract ((m : ℝ) * u k)) a c n : ℝ)
      = ∑ j ∈ Finset.range m,
          (visitCount u (((j : ℝ) + a) / m) (((j : ℝ) + c) / m) n : ℝ) := by
    intro n
    rw [expand]
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range m) => expand u
      (((j : ℝ) + a) / m) (((j : ℝ) + c) / m) n), Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨ht0, ht1⟩ := hu k
    have hmt0 : (0 : ℝ) ≤ (m : ℝ) * u k := by positivity
    have hmtm : (m : ℝ) * u k < m := by nlinarith
    have hJ0 : (0 : ℤ) ≤ ⌊(m : ℝ) * u k⌋ := Int.floor_nonneg.2 hmt0
    have hJm : ⌊(m : ℝ) * u k⌋ < (m : ℤ) := Int.floor_lt.2 (by push_cast; exact hmtm)
    set j0 : ℕ := (⌊(m : ℝ) * u k⌋).toNat with hj0def
    have hj0J : ((j0 : ℤ)) = ⌊(m : ℝ) * u k⌋ := Int.toNat_of_nonneg hJ0
    have hj0m : j0 < m := by omega
    have hj0R : ((j0 : ℝ)) = ((⌊(m : ℝ) * u k⌋ : ℤ) : ℝ) := by exact_mod_cast hj0J
    have hfr : Int.fract ((m : ℝ) * u k) = (m : ℝ) * u k - (j0 : ℝ) := by
      rw [Int.fract, hj0R]
    have hcond : ∀ j : ℕ, (((j : ℝ) + a) / m ≤ u k ∧ u k < ((j : ℝ) + c) / m)
        ↔ ((j : ℝ) + a ≤ (m : ℝ) * u k ∧ (m : ℝ) * u k < (j : ℝ) + c) := by
      intro j
      rw [div_le_iff₀ hmR, lt_div_iff₀ hmR]
      constructor
      · exact fun hj => ⟨by linarith [hj.1], by linarith [hj.2]⟩
      · exact fun hj => ⟨by linarith [hj.1], by linarith [hj.2]⟩
    rw [Finset.sum_eq_single_of_mem j0 (Finset.mem_range.2 hj0m) ?_]
    · by_cases hB : ((j0 : ℝ) + a) / m ≤ u k ∧ u k < ((j0 : ℝ) + c) / m
      · have hB' := (hcond j0).1 hB
        rw [if_pos hB, hfr]
        exact if_pos ⟨by linarith [hB'.1], by linarith [hB'.2]⟩
      · rw [if_neg hB, hfr]
        refine if_neg ?_
        intro hA
        exact hB ((hcond j0).2 ⟨by linarith [hA.1], by linarith [hA.2]⟩)
    · intro j hj hne
      rw [if_neg]
      intro hB
      rw [hcond j] at hB
      have hfl : ⌊(m : ℝ) * u k⌋ = (j : ℤ) := by
        rw [Int.floor_eq_iff]
        refine ⟨by push_cast; linarith [hB.1], by push_cast; linarith [hB.2]⟩
      exact hne (by omega)
  have hlim : ∀ j ∈ Finset.range m,
      Tendsto (fun n => (visitCount u (((j : ℝ) + a) / m) (((j : ℝ) + c) / m) n : ℝ) / n)
        atTop (𝓝 ((c - a) / m)) := by
    intro j hj
    have hjm : ((j : ℝ)) + 1 ≤ m := by
      have : (j : ℕ) + 1 ≤ m := Finset.mem_range.1 hj
      exact_mod_cast this
    have hval : ((j : ℝ) + c) / m - ((j : ℝ) + a) / m = (c - a) / m := by
      rw [div_sub_div_same]
      congr 1
      ring
    rw [← hval]
    refine h _ _ (by positivity) ?_ ?_
    · exact div_le_div_of_nonneg_right (by linarith) hmR.le
    · rw [div_le_one hmR]; linarith
  have hsum := tendsto_finset_sum (Finset.range m) hlim
  have hconst : (∑ _j ∈ Finset.range m, (c - a) / m) = c - a := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hconst] at hsum
  refine hsum.congr fun n => ?_
  rw [key n, Finset.sum_div]

/-- Level sets of an equidistributed sequence have density zero. -/
theorem density_level_zero {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (h : Equidistributed u) (t : ℝ) :
    Tendsto (fun n => (((Finset.range n).filter fun k => u k = t).card : ℝ) / n)
      atTop (𝓝 0) := by

  classical
  by_cases hmem : t ∈ Set.Ico (0 : ℝ) 1
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have ht1 : t < 1 := hmem.2
    set δ : ℝ := min (ε / 2) (1 - t) with hδdef
    have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
    have hδε : δ ≤ ε / 2 := min_le_left _ _
    have htδ : t + δ ≤ 1 := by
      have := min_le_right (ε / 2) (1 - t)
      rw [← hδdef] at this
      linarith
    have hvis := h t (t + δ) hmem.1 (by linarith) htδ
    rw [Metric.tendsto_atTop] at hvis
    obtain ⟨N, hN⟩ := hvis (ε / 2) (by linarith)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hd := hN n (le_trans (le_max_left _ _) hn)
    rw [Real.dist_eq, abs_lt] at hd
    have hsub : ((Finset.range n).filter fun k => u k = t)
        ⊆ (Finset.range n).filter fun k => u k ∈ Set.Ico t (t + δ) := by
      intro k hk
      simp only [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, by rw [hk.2]; exact ⟨le_refl t, by linarith⟩⟩
    have hcard : ((((Finset.range n).filter fun k => u k = t).card : ℕ) : ℝ)
        ≤ (visitCount u t (t + δ) n : ℝ) := by
      rw [visitCount]
      exact_mod_cast Finset.card_le_card hsub
    have hmono : ((((Finset.range n).filter fun k => u k = t).card : ℕ) : ℝ) / n
        ≤ (visitCount u t (t + δ) n : ℝ) / n :=
      div_le_div_of_nonneg_right hcard hnR.le
    have hnn : (0 : ℝ) ≤ ((((Finset.range n).filter fun k => u k = t).card : ℕ) : ℝ) / n := by
      positivity
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor
    · linarith
    · have : t + δ - t = δ := by ring
      rw [this] at hd
      linarith
  · have hzero : ∀ n : ℕ, ((Finset.range n).filter fun k => u k = t) = ∅ := by
      intro n
      rw [Finset.filter_eq_empty_iff]
      intro k _ hk
      exact hmem (by rw [← hk]; exact hu k)
    simp only [hzero, Finset.card_empty, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds

/-- Reflection `t ↦ {-t}` preserves equidistribution (the two exceptional endpoints and
the fixed point `0` form density-zero level sets). -/
theorem equidistributed_negFract {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (h : Equidistributed u) :
    Equidistributed (fun k => Int.fract (-(u k))) := by

  classical
  intro a c ha hac hc
  have hfract : ∀ t : ℝ, 0 < t → t < 1 → Int.fract (-t) = 1 - t := by
    intro t ht0 ht1
    have hfl : ⌊-t⌋ = (-1 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    rw [Int.fract, hfl]
    push_cast
    ring
  set c0 : ℕ → ℕ := fun n => ((Finset.range n).filter fun k => u k = 0).card with hc0
  set c1 : ℕ → ℕ := fun n => ((Finset.range n).filter fun k => u k = 1 - c).card with hc1
  set c2 : ℕ → ℕ := fun n => ((Finset.range n).filter fun k => u k = 1 - a).card with hc2
  set U : ℕ → Finset ℕ := fun n =>
    ((Finset.range n).filter fun k => u k = 0) ∪
      (((Finset.range n).filter fun k => u k = 1 - c) ∪
        ((Finset.range n).filter fun k => u k = 1 - a)) with hU
  have hUcard : ∀ n, (U n).card ≤ c0 n + (c1 n + c2 n) := by
    intro n
    refine le_trans (Finset.card_union_le _ _) ?_
    exact Nat.add_le_add_left (Finset.card_union_le _ _) _
  have hSsub : ∀ n, ((Finset.range n).filter fun k => Int.fract (-(u k)) ∈ Set.Ico a c)
      ⊆ ((Finset.range n).filter fun k => u k ∈ Set.Ico (1 - c) (1 - a)) ∪ U n := by
    intro n k hk
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico] at hk
    have hkn := hk.1
    have hka := hk.2.1
    have hkc := hk.2.2
    by_cases h0 : u k = 0
    · simp only [hU, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      exact Or.inr (Or.inl ⟨hkn, h0⟩)
    by_cases h1 : u k = 1 - c
    · simp only [hU, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      exact Or.inr (Or.inr (Or.inl ⟨hkn, h1⟩))
    by_cases h2 : u k = 1 - a
    · simp only [hU, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      exact Or.inr (Or.inr (Or.inr ⟨hkn, h2⟩))
    obtain ⟨hu0, hu1⟩ := hu k
    have hupos : 0 < u k := lt_of_le_of_ne hu0 (Ne.symm h0)
    have hfr := hfract (u k) hupos hu1
    rw [hfr] at hka hkc
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    refine Or.inl ⟨hkn, ?_, ?_⟩
    · linarith
    · rcases lt_or_eq_of_le (show u k ≤ 1 - a by linarith) with h | h
      · exact h
      · exact absurd h h2
  have hTsub : ∀ n, ((Finset.range n).filter fun k => u k ∈ Set.Ico (1 - c) (1 - a))
      ⊆ ((Finset.range n).filter fun k => Int.fract (-(u k)) ∈ Set.Ico a c) ∪ U n := by
    intro n k hk
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico] at hk
    have hkn := hk.1
    have hka := hk.2.1
    have hkc := hk.2.2
    by_cases h0 : u k = 0
    · simp only [hU, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      exact Or.inr (Or.inl ⟨hkn, h0⟩)
    by_cases h1 : u k = 1 - c
    · simp only [hU, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      exact Or.inr (Or.inr (Or.inl ⟨hkn, h1⟩))
    obtain ⟨hu0, hu1⟩ := hu k
    have hupos : 0 < u k := lt_of_le_of_ne hu0 (Ne.symm h0)
    have hfr := hfract (u k) hupos hu1
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, hfr]
    refine Or.inl ⟨hkn, ?_, ?_⟩
    · linarith
    · rcases lt_or_eq_of_le hka with h | h
      · linarith
      · exact absurd h.symm h1
  have hcardS : ∀ n, ((Finset.range n).filter fun k =>
        Int.fract (-(u k)) ∈ Set.Ico a c).card
      ≤ visitCount u (1 - c) (1 - a) n + (c0 n + (c1 n + c2 n)) := by
    intro n
    refine le_trans (Finset.card_le_card (hSsub n)) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    exact Nat.add_le_add_left (hUcard n) _
  have hcardT : ∀ n, visitCount u (1 - c) (1 - a) n
      ≤ ((Finset.range n).filter fun k => Int.fract (-(u k)) ∈ Set.Ico a c).card
        + (c0 n + (c1 n + c2 n)) := by
    intro n
    rw [visitCount]
    refine le_trans (Finset.card_le_card (hTsub n)) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    exact Nat.add_le_add_left (hUcard n) _
  have herr : Tendsto (fun n => ((c0 n + (c1 n + c2 n) : ℕ) : ℝ) / n) atTop (𝓝 0) := by
    have h0 := density_level_zero hu h 0
    have h1 := density_level_zero hu h (1 - c)
    have h2 := density_level_zero hu h (1 - a)
    have := (h0.add (h1.add h2))
    rw [add_zero, add_zero] at this
    refine this.congr fun n => ?_
    push_cast
    rw [hc0, hc1, hc2]
    ring
  have href := h (1 - c) (1 - a) (by linarith) (by linarith) (by linarith)
  have hval : (1 - a) - (1 - c) = c - a := by ring
  rw [hval] at href
  have hlow : Tendsto (fun n => (visitCount u (1 - c) (1 - a) n : ℝ) / n
      - ((c0 n + (c1 n + c2 n) : ℕ) : ℝ) / n) atTop (𝓝 (c - a)) := by
    have := href.sub herr
    rwa [sub_zero] at this
  have hhigh : Tendsto (fun n => (visitCount u (1 - c) (1 - a) n : ℝ) / n
      + ((c0 n + (c1 n + c2 n) : ℕ) : ℝ) / n) atTop (𝓝 (c - a)) := by
    have := href.add herr
    rwa [add_zero] at this
  have hSeq : ∀ n, visitCount (fun k => Int.fract (-(u k))) a c n
      = ((Finset.range n).filter fun k => Int.fract (-(u k)) ∈ Set.Ico a c).card := by
    intro n; rw [visitCount]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh ?_ ?_
  · intro n
    dsimp only
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have := hcardT n
    have hR : (visitCount u (1 - c) (1 - a) n : ℝ)
        ≤ (((Finset.range n).filter fun k => Int.fract (-(u k)) ∈ Set.Ico a c).card : ℝ)
          + ((c0 n + (c1 n + c2 n) : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [hSeq n, div_sub_div_same]
    exact div_le_div_of_nonneg_right (by linarith) hn
  · intro n
    dsimp only
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have := hcardS n
    have hR : (((Finset.range n).filter fun k =>
          Int.fract (-(u k)) ∈ Set.Ico a c).card : ℝ)
        ≤ (visitCount u (1 - c) (1 - a) n : ℝ) + ((c0 n + (c1 n + c2 n) : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [hSeq n, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hn

/-- Dropping the first `κ` terms cannot create equidistribution, and cannot destroy it. -/
theorem equidistributed_of_shift {u : ℕ → ℝ} (κ : ℕ)
    (h : Equidistributed fun n => u (n + κ)) : Equidistributed u := by

  classical
  intro a c ha hac hc
  have hg := h a c ha hac hc
  set C : ℕ := visitCount u a c κ with hC
  have hsplit : ∀ N : ℕ, visitCount u a c (κ + N)
      = C + visitCount (fun n => u (n + κ)) a c N := by
    intro N
    simp only [hC, visitCount, Finset.card_filter]
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.add_comm κ x]
  have hA : Tendsto (fun n : ℕ =>
      (visitCount (fun i => u (i + κ)) a c (n - κ) : ℝ) / ((n - κ : ℕ) : ℝ))
      atTop (𝓝 (c - a)) := hg.comp (Filter.tendsto_sub_atTop_nat κ)
  have hB : Tendsto (fun n : ℕ => (((n - κ : ℕ) : ℝ)) / (n : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 - (κ : ℝ) / (n : ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (κ : ℝ))
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (κ + 1)] with n hn
    have hκn : κ ≤ n := by omega
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hcast : ((n - κ : ℕ) : ℝ) = (n : ℝ) - (κ : ℝ) := by
      push_cast [hκn]
      ring
    rw [hcast]
    field_simp
  have hC0 : Tendsto (fun n : ℕ => (C : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)
  have hmain := hC0.add (hA.mul hB)
  rw [zero_add, mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (κ + 1)] with n hn
  have hκn : κ ≤ n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    positivity
  have hsub0 : ((n - κ : ℕ) : ℝ) ≠ 0 := by
    have h1 : 0 < n - κ := by omega
    have : (0 : ℝ) < ((n - κ : ℕ) : ℝ) := by exact_mod_cast h1
    exact ne_of_gt this
  have hn' : κ + (n - κ) = n := by omega
  have hst := hsplit (n - κ)
  rw [hn'] at hst
  rw [hst]
  push_cast
  field_simp

/-- Negation only sees the fractional part. -/
theorem fract_neg_fract (y : ℝ) : Int.fract (-y) = Int.fract (-(Int.fract y)) := by
  simpa using fract_intMul_fract (-1) y

/-! ### Normality-level consequences -/

/-- Integer translations preserve normality. -/
theorem isNormal_add_intCast (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (M : ℤ) (hx : IsNormal b x) :
    IsNormal b (x + (M : ℝ)) := by

  have heq : orbit b (x + (M : ℝ)) = orbit b x := funext (orbit_add_intCast b x M)
  rw [isNormal_iff_equidistributed_orbit b hb, heq,
    ← isNormal_iff_equidistributed_orbit b hb]
  exact hx

/-- Nonzero integer dilations preserve normality. -/
theorem isNormal_intMul (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (m : ℤ) (hm : m ≠ 0)
    (hx : IsNormal b x) : IsNormal b ((m : ℝ) * x) := by
  rw [isNormal_iff_equidistributed_orbit b hb] at hx
  rw [isNormal_iff_equidistributed_orbit b hb]
  have horb : ∀ n, orbit b x n ∈ Set.Ico (0 : ℝ) 1 :=
    fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · obtain ⟨m', hm'⟩ : ∃ k : ℕ, (k : ℤ) = -m := ⟨(-m).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hm'pos : 0 < m' := by omega
    have hv : Equidistributed (fun n => Int.fract ((m' : ℝ) * orbit b x n)) :=
      equidistributed_natMul horb hx hm'pos
    have hcast : ((m : ℤ) : ℝ) = -((m' : ℕ) : ℝ) := by
      have hz : m = -(m' : ℤ) := by omega
      exact_mod_cast hz
    have hvmem : ∀ n, Int.fract ((m' : ℝ) * orbit b x n) ∈ Set.Ico (0 : ℝ) 1 :=
      fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hneg' := equidistributed_negFract hvmem hv
    have heq : orbit b ((m : ℝ) * x)
        = fun n => Int.fract (-(Int.fract ((m' : ℝ) * orbit b x n))) := by
      funext n
      rw [orbit_intMul, hcast, neg_mul]
      exact fract_neg_fract _
    rw [heq]
    exact hneg'
  · obtain ⟨m', hm'⟩ : ∃ k : ℕ, (k : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg (by omega)⟩
    have hm'pos : 0 < m' := by omega
    have hv : Equidistributed (fun n => Int.fract ((m' : ℝ) * orbit b x n)) :=
      equidistributed_natMul horb hx hm'pos
    have hcast : ((m : ℤ) : ℝ) = ((m' : ℕ) : ℝ) := by
      have hz : m = (m' : ℤ) := by omega
      exact_mod_cast hz
    have heq : orbit b ((m : ℝ) * x)
        = fun n => Int.fract ((m' : ℝ) * orbit b x n) := by
      funext n
      rw [orbit_intMul, hcast]
    rw [heq]
    exact hv

/-- Division by a power of the base preserves normality (it shifts the orbit). -/
theorem isNormal_div_pow (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (κ : ℕ) (hx : IsNormal b x) :
    IsNormal b (x / (b : ℝ) ^ κ) := by

  rw [isNormal_iff_equidistributed_orbit b hb] at hx
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_shift κ ?_
  have heq : (fun n => orbit b (x / (b : ℝ) ^ κ) (n + κ)) = orbit b x := by
    funext n
    unfold orbit
    congr 1
    have hbpos : (0 : ℝ) < (b : ℝ) ^ κ := by
      have : (0 : ℝ) < (b : ℝ) := by
        have : (0 : ℕ) < b := by omega
        exact_mod_cast this
      positivity
    have hP : ((b : ℝ)) ^ κ ≠ 0 := ne_of_gt hbpos
    rw [pow_add, div_mul_eq_mul_div,
      show x * ((b : ℝ) ^ n * (b : ℝ) ^ κ) = x * (b : ℝ) ^ n * (b : ℝ) ^ κ from by ring,
      mul_div_assoc, div_self hP, mul_one]
  rw [heq]
  exact hx

/-! ### The arithmetic split of the denominator -/

/-- Every positive `V` factors as a `b`-smooth part times a part coprime to `b`. -/
theorem exists_smooth_coprime_split (b : ℕ) (hb : 2 ≤ b) (V : ℕ) (hV : 0 < V) :
    ∃ A B κ : ℕ, 0 < A ∧ 0 < B ∧ V = A * B ∧ A ∣ b ^ κ ∧ Nat.Coprime B b := by

  revert hV
  induction V using Nat.strong_induction_on with
  | _ V ih =>
    intro hV
    by_cases hc : Nat.Coprime V b
    · exact ⟨1, V, 0, one_pos, hV, (one_mul V).symm, one_dvd _, hc⟩
    · set d := Nat.gcd V b with hd
      have hdV : d ∣ V := Nat.gcd_dvd_left V b
      have hdb : d ∣ b := Nat.gcd_dvd_right V b
      have hd0 : d ≠ 0 := by
        rw [hd]
        intro h
        rw [Nat.gcd_eq_zero_iff] at h
        omega
      have hdne1 : d ≠ 1 := by rw [hd]; exact hc
      have hd1 : 1 < d := by omega
      obtain ⟨V', hV'⟩ := hdV
      have hV'pos : 0 < V' := by
        rcases Nat.eq_zero_or_pos V' with h | h
        · rw [h, Nat.mul_zero] at hV'; omega
        · exact h
      have hlt : V' < V := by
        have h2 : 1 * V' < d * V' := by
          first
            | exact (Nat.mul_lt_mul_right hV'pos).2 hd1
            | exact mul_lt_mul_of_pos_right hd1 hV'pos
            | exact Nat.mul_lt_mul_of_lt_of_le hd1 le_rfl hV'pos
        rw [hV']; simpa using h2
      obtain ⟨A, B, κ, hA, hB, hVAB, hAdvd, hBcop⟩ := ih V' hlt hV'pos
      refine ⟨d * A, B, κ + 1, Nat.mul_pos (by omega) hA, hB, ?_, ?_, hBcop⟩
      · rw [hV', hVAB]; ring
      · have hstep : A * d ∣ (b : ℕ) ^ κ * b := mul_dvd_mul hAdvd hdb
        rw [pow_succ, mul_comm d A]
        exact hstep

/-! ### The crux: division by a modulus coprime to the base -/

/-- The block of `l` digits of `x` starting at position `n`, as a natural number. -/
noncomputable def blockVal (b : ℕ) (x : ℝ) (n l : ℕ) : ℕ :=
  blockNatVal b ((List.range l).map fun i => digitOf b (Int.fract x) (n + i))

/-- **Engine for the crux.** For a normal `x`, the average of any function of the
length-`l` digit block at position `n` converges to its mean over all `b^l` blocks.
This is `IsNormalSequence` plus linearity, and it is what feeds the off-diagonal
estimate in the Cauchy–Schwarz step. -/
theorem tendsto_blockAverage (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormal b x)
    (l : ℕ) (hl : 0 < l) (F : ℕ → ℝ) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, F (blockVal b x n l)) / N) atTop
      (𝓝 (((b : ℝ) ^ l)⁻¹ * ∑ v ∈ Finset.range (b ^ l), F v)) := by

  classical
  set s : ℕ → ℕ := digitOf b (Int.fract x) with hs
  have hxs : IsNormalSequence b s := hx
  have hsb : ∀ i, s i < b := fun i => digitOf_lt b hb _ i
  have hbv : ∀ n, blockVal b x n l
      = blockNatVal b ((List.range l).map fun i => s (n + i)) := fun n => rfl
  have hmlen : ∀ n : ℕ, ((List.range l).map fun i => s (n + i)).length = l := by
    intro n; simp
  have hmlt : ∀ n : ℕ, ∀ d ∈ ((List.range l).map fun i => s (n + i)), d < b := by
    intro n d hd
    simp only [List.mem_map, List.mem_range] at hd
    obtain ⟨i, _, rfl⟩ := hd
    exact hsb _
  have hblt : ∀ n, blockVal b x n l < b ^ l := by
    intro n
    have h := blockNatVal_lt b ((List.range l).map fun i => s (n + i)) (hmlt n)
    rw [hmlen n] at h
    rw [hbv n]
    exact h
  have hmatch : ∀ (n v : ℕ), v < b ^ l →
      (MatchesAt s (padWord b l v) n ↔ blockVal b x n l = v) := by
    intro n v hv
    have hlp : (padWord b l v).length = l := length_padWord hb hv
    have hwlt : ∀ d ∈ padWord b l v, d < b := padWord_digits_lt hb l v
    constructor
    · intro hm
      have hlist : ((List.range l).map fun i => s (n + i)) = padWord b l v := by
        refine List.ext_getElem (by rw [hmlen n, hlp]) ?_
        intro i h1 h2
        have e1 : ((List.range l).map fun i => s (n + i))[i] = s (n + i) := by simp
        have e2 : (padWord b l v).getD i 0 = (padWord b l v)[i] :=
          List.getD_eq_getElem _ _ h2
        rw [e1, ← e2]
        rw [hmlen n] at h1
        exact hm i (by rw [hlp]; exact h1)
      rw [hbv n, hlist, blockNatVal_padWord hb l v]
    · intro hval
      have hveq : blockNatVal b ((List.range l).map fun i => s (n + i))
          = blockNatVal b (padWord b l v) := by
        rw [blockNatVal_padWord hb l v, ← hbv n]
        exact hval
      have hlist : ((List.range l).map fun i => s (n + i)) = padWord b l v :=
        blockNatVal_inj b (by omega) _ _ (by rw [hmlen n, hlp]) (hmlt n) hwlt hveq
      intro j hj
      rw [hlp] at hj
      have e2 : (padWord b l v).getD j 0
          = ((List.range l).map fun i => s (n + i)).getD j 0 := by rw [hlist]
      rw [e2]
      have hj' : j < ((List.range l).map fun i => s (n + i)).length := by
        rw [hmlen n]; exact hj
      rw [List.getD_eq_getElem _ _ hj']
      simp
  have hlim : ∀ v ∈ Finset.range (b ^ l),
      Tendsto (fun N => (((Finset.range N).filter fun n => blockVal b x n l = v).card : ℝ) / N)
        atTop (𝓝 (((b : ℝ) ^ l)⁻¹)) := by
    intro v hv
    have hv' : v < b ^ l := Finset.mem_range.1 hv
    have hlp : (padWord b l v).length = l := length_padWord hb hv'
    have hwne : padWord b l v ≠ [] := by
      intro hnil
      rw [hnil] at hlp
      simp at hlp
      omega
    have hwlt : ∀ d ∈ padWord b l v, d < b := padWord_digits_lt hb l v
    have hcount := hxs (padWord b l v) hwne hwlt
    have hle := fun N => card_filter_matchesAt_le s (padWord b l v) hwne N
    have htrans := tendsto_div_of_bounded_diff (fun N => (hle N).1) (fun N => (hle N).2) hcount
    rw [hlp] at htrans
    have hfe : ∀ N : ℕ, (Finset.range N).filter (MatchesAt s (padWord b l v))
        = (Finset.range N).filter fun n => blockVal b x n l = v := by
      intro N
      refine Finset.filter_congr fun n _ => ?_
      exact hmatch n v hv'
    refine htrans.congr fun N => ?_
    rw [hfe N]
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, F (blockVal b x n l))
      = ∑ v ∈ Finset.range (b ^ l),
          F v * (((Finset.range N).filter fun n => blockVal b x n l = v).card : ℝ) := by
    intro N
    have hone : ∀ v ∈ Finset.range (b ^ l),
        F v * (((Finset.range N).filter fun n => blockVal b x n l = v).card : ℝ)
        = ∑ n ∈ Finset.range N, (if blockVal b x n l = v then F v else 0) := by
      intro v _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl hone, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_ite_eq (Finset.range (b ^ l)) (blockVal b x n l) F,
      if_pos (Finset.mem_range.2 (hblt n))]
  have hval : (∑ v ∈ Finset.range (b ^ l), F v * ((b : ℝ) ^ l)⁻¹)
      = ((b : ℝ) ^ l)⁻¹ * ∑ v ∈ Finset.range (b ^ l), F v := by
    rw [← Finset.sum_mul, mul_comm]
  rw [← hval]
  refine (tendsto_finsetSum _ (fun v hv => (hlim v hv).const_mul (F v))).congr fun N => ?_
  rw [hsum N, Finset.sum_div]
  exact Finset.sum_congr rfl fun v _ => (mul_div_assoc _ _ _).symm

/-! ### The long-division automaton -/

/-- The state of the long-division automaton computing `(x + M)/B` in base `b`:
`r n = (b^n M + ⌊b^n x⌋) mod B`.  It is the only thing besides the digits of `x` that the
digits of `(x + M)/B` depend on. -/
noncomputable def divState (b B : ℕ) (x : ℝ) (M : ℤ) (n : ℕ) : ℕ :=
  ((M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋) % (B : ℤ)).toNat

theorem divState_lt (b B : ℕ) (hB : 0 < B) (x : ℝ) (M : ℤ) (n : ℕ) :
    divState b B x M n < B := by
  have hB' : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hB
  have h1 : (M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋) % (B : ℤ) < (B : ℤ) :=
    Int.emod_lt_of_pos _ hB'
  have h2 : (0 : ℤ) ≤ (M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋) % (B : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hB')
  rw [divState]
  omega

theorem divState_modEq (b B : ℕ) (hB : 0 < B) (x : ℝ) (M : ℤ) (n : ℕ) :
    ((divState b B x M n : ℤ)) ≡ M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋ [ZMOD (B : ℤ)] := by
  have hB' : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hB
  have h2 : (0 : ℤ) ≤ (M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋) % (B : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hB')
  show ((divState b B x M n : ℤ)) % (B : ℤ) = _ % (B : ℤ)
  rw [divState, Int.toNat_of_nonneg h2]
  exact Int.emod_emod_of_dvd _ dvd_rfl

/-- The fractional part of `x` seen by `blockVal` is `x` itself on `[0,1)`. -/
theorem blockVal_eq_of_mem (b : ℕ) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (n l : ℕ) :
    blockVal b x n l = blockNatVal b ((List.range l).map fun i => digitOf b x (n + i)) := by
  rw [blockVal, Int.fract_eq_self.2 hx]

/-- The block value is the integer part of the shifted orbit point:
`⌊b^l · (b^n x mod 1)⌋ = blockVal b x n l`. -/
theorem floor_orbit_mul_pow (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (n l : ℕ) : ⌊orbit b x n * (b : ℝ) ^ l⌋ = (blockVal b x n l : ℤ) := by
  have hmem : orbit b x n ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [floor_eq_digitVal b hb _ hmem l, blockVal_eq_of_mem b x hx n l, blockNatVal_eq_sum]
  push_cast
  refine Finset.sum_congr (by simp) fun i hi => ?_
  have hil : i < l := by simpa using hi
  have hget : ((List.range l).map fun i => digitOf b x (n + i)).getD i 0
      = digitOf b x (n + i) := by
    have hlen : i < ((List.range l).map fun i => digitOf b x (n + i)).length := by
      simpa using hil
    rw [List.getD_eq_getElem _ _ hlen]
    simp
  rw [hget, digitOf_orbit b hb x hx.1 n i]
  have hlen : ((List.range l).map fun i => digitOf b x (n + i)).length = l := by simp
  rw [hlen]

/-- The orbit shifts by dilation: `orbit b x (n + m) = {orbit b x n * b^m}`. -/
theorem orbit_shift (b : ℕ) (x : ℝ) (n m : ℕ) :
    orbit b x (n + m) = Int.fract (orbit b x n * (b : ℝ) ^ m) := by
  unfold orbit
  have h : x * (b : ℝ) ^ (n + m) = (((b : ℤ) ^ m : ℤ) : ℝ) * (x * (b : ℝ) ^ n) := by
    push_cast; ring
  rw [h, fract_intMul_fract ((b : ℤ) ^ m)]
  congr 1
  push_cast
  ring

/-- A shorter block is the leading digits of a longer one. -/
theorem blockVal_prefix (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (n j L : ℕ) (hjL : j ≤ L) :
    blockVal b x n j = blockVal b x n L / b ^ (L - j) := by
  have hb0 : (0 : ℝ) < b := by positivity
  have hbne : ((b : ℝ)) ≠ 0 := ne_of_gt hb0
  have h1 : ⌊orbit b x n * (b : ℝ) ^ L⌋ = (blockVal b x n L : ℤ) :=
    floor_orbit_mul_pow b hb x hx n L
  have h2 : ⌊orbit b x n * (b : ℝ) ^ j⌋ = (blockVal b x n j : ℤ) :=
    floor_orbit_mul_pow b hb x hx n j
  have hpow : (b : ℝ) ^ L = (b : ℝ) ^ j * (b : ℝ) ^ (L - j) := by
    rw [← pow_add]; congr 1; omega
  have hd : orbit b x n * (b : ℝ) ^ j
      = (orbit b x n * (b : ℝ) ^ L) / (((b ^ (L - j) : ℕ) : ℝ)) := by
    push_cast
    rw [hpow]
    field_simp
  rw [hd, Int.floor_div_natCast, h1] at h2
  have h3 : ((blockVal b x n L : ℤ)) / ((b ^ (L - j) : ℕ) : ℤ)
      = ((blockVal b x n L / b ^ (L - j) : ℕ) : ℤ) := (Int.natCast_div _ _).symm
  rw [h3] at h2
  exact_mod_cast h2.symm

/-- A length-`m+l` block splits into its first `m` digits and the next `l`. -/
theorem blockVal_split (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (n m l : ℕ) :
    blockVal b x (n + m) l + b ^ l * blockVal b x n m = blockVal b x n (m + l) := by
  have horb : orbit b x (n + m) = orbit b x n * (b : ℝ) ^ m - ((blockVal b x n m : ℤ) : ℝ) := by
    rw [orbit_shift, Int.fract, floor_orbit_mul_pow b hb x hx n m]
  have h1 : ((blockVal b x (n + m) l : ℤ)) = ⌊orbit b x (n + m) * (b : ℝ) ^ l⌋ :=
    (floor_orbit_mul_pow b hb x hx (n + m) l).symm
  have h2 : orbit b x (n + m) * (b : ℝ) ^ l
      = orbit b x n * (b : ℝ) ^ (m + l)
        - ((((b : ℤ) ^ l * (blockVal b x n m : ℤ)) : ℤ) : ℝ) := by
    rw [horb]
    push_cast
    ring
  rw [h2, Int.floor_sub_intCast, floor_orbit_mul_pow b hb x hx n (m + l)] at h1
  have hgoal : ((blockVal b x (n + m) l + b ^ l * blockVal b x n m : ℕ) : ℤ)
      = ((blockVal b x n (m + l) : ℕ) : ℤ) := by
    push_cast
    push_cast at h1
    linarith
  exact_mod_cast hgoal

/-- A window of `l` digits at offset `m` inside a length-`L` block is a digit slice. -/
theorem blockVal_window (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (n m l L : ℕ) (hml : m + l ≤ L) :
    blockVal b x (n + m) l = (blockVal b x n L / b ^ (L - m - l)) % b ^ l := by
  have hb0 : 0 < b := by omega
  set W := blockVal b x n L with hW
  have e1 : blockVal b x n (m + l) = W / b ^ (L - m - l) := by
    rw [blockVal_prefix b hb x hx n (m + l) L (by omega)]
    congr 2
    omega
  have e2 : blockVal b x n m = W / b ^ (L - m) := blockVal_prefix b hb x hx n m L (by omega)
  have e3 : W / b ^ (L - m) = (W / b ^ (L - m - l)) / b ^ l := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    omega
  have hsplit := blockVal_split b hb x hx n m l
  rw [e1, e2, e3] at hsplit
  set V := W / b ^ (L - m - l) with hV
  have hmod := Nat.mod_add_div V (b ^ l)
  omega

/-- **Automaton step.**  `r (n + j) ≡ b^j · r n + (value of the digit block `x[n, n+j)`)`. -/
theorem divState_shift (b B : ℕ) (hb : 2 ≤ b) (hB : 0 < B) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (M : ℤ) (n j : ℕ) :
    ((divState b B x M (n + j) : ℤ))
      ≡ (b : ℤ) ^ j * (divState b B x M n : ℤ) + (blockVal b x n j : ℤ) [ZMOD (B : ℤ)] := by
  have horb : orbit b x n = x * (b : ℝ) ^ n - (⌊x * (b : ℝ) ^ n⌋ : ℝ) := by
    rw [orbit, Int.fract]
  have hfl : ⌊x * (b : ℝ) ^ (n + j)⌋
      = (b : ℤ) ^ j * ⌊x * (b : ℝ) ^ n⌋ + (blockVal b x n j : ℤ) := by
    have h1 : x * (b : ℝ) ^ (n + j)
        = orbit b x n * (b : ℝ) ^ j + ((((b : ℤ) ^ j * ⌊x * (b : ℝ) ^ n⌋ : ℤ)) : ℝ) := by
      rw [horb]
      push_cast
      ring
    rw [h1, Int.floor_add_intCast, floor_orbit_mul_pow b hb x hx n j]
    ring
  have hA : M * (b : ℤ) ^ (n + j) + ⌊x * (b : ℝ) ^ (n + j)⌋
      = (b : ℤ) ^ j * (M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋) + (blockVal b x n j : ℤ) := by
    rw [hfl]; ring
  calc ((divState b B x M (n + j) : ℤ))
      ≡ M * (b : ℤ) ^ (n + j) + ⌊x * (b : ℝ) ^ (n + j)⌋ [ZMOD (B : ℤ)] :=
        divState_modEq b B hB x M (n + j)
    _ = (b : ℤ) ^ j * (M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋) + (blockVal b x n j : ℤ) := hA
    _ ≡ (b : ℤ) ^ j * (divState b B x M n : ℤ) + (blockVal b x n j : ℤ) [ZMOD (B : ℤ)] :=
        Int.ModEq.add_right _ (Int.ModEq.mul_left _ (divState_modEq b B hB x M n).symm)

/-- **State decomposition of the orbit.**  The orbit of `(x + M)/B` is the state plus the
orbit of `x`, rescaled by `B`. -/
theorem orbit_add_div (b B : ℕ) (hB : 0 < B) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (M : ℤ)
    (n : ℕ) :
    orbit b ((x + (M : ℝ)) / B) n = ((divState b B x M n : ℝ) + orbit b x n) / B := by
  have hB' : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hBne : ((B : ℝ)) ≠ 0 := ne_of_gt hB'
  set A : ℤ := M * (b : ℤ) ^ n + ⌊x * (b : ℝ) ^ n⌋ with hAdef
  have hB'' : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hB
  have hnn : (0 : ℤ) ≤ A % (B : ℤ) := Int.emod_nonneg _ (ne_of_gt hB'')
  have hdiv : A = (B : ℤ) * (A / (B : ℤ)) + (divState b B x M n : ℤ) := by
    rw [divState, ← hAdef, Int.toNat_of_nonneg hnn, Int.emod_def]
    ring
  have hAR : ((A : ℤ) : ℝ)
      = (B : ℝ) * (((A / (B : ℤ) : ℤ)) : ℝ) + (divState b B x M n : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => ((z : ℝ))) hdiv
  have horb : orbit b x n = x * (b : ℝ) ^ n - (⌊x * (b : ℝ) ^ n⌋ : ℝ) := by
    rw [orbit, Int.fract]
  have hAR2 : ((A : ℤ) : ℝ) = (M : ℝ) * (b : ℝ) ^ n + (⌊x * (b : ℝ) ^ n⌋ : ℝ) := by
    rw [hAdef]; push_cast; ring
  have hkey : (x + (M : ℝ)) / (B : ℝ) * (b : ℝ) ^ n
      = ((divState b B x M n : ℝ) + orbit b x n) / (B : ℝ)
        + (((A / (B : ℤ) : ℤ)) : ℝ) := by
    have key0 : (x + (M : ℝ)) * (b : ℝ) ^ n
        = ((divState b B x M n : ℝ) + orbit b x n)
          + (B : ℝ) * (((A / (B : ℤ) : ℤ)) : ℝ) := by
      have hexp : (x + (M : ℝ)) * (b : ℝ) ^ n = x * (b : ℝ) ^ n + (M : ℝ) * (b : ℝ) ^ n := by
        ring
      rw [hexp]
      linarith [hAR, hAR2, horb]
    rw [div_mul_eq_mul_div, key0, add_div, mul_comm ((B : ℝ)) _, mul_div_assoc,
      div_self hBne, mul_one]
  have hlt : divState b B x M n < B := divState_lt b B hB x M n
  have hltR : ((divState b B x M n : ℕ) : ℝ) + 1 ≤ (B : ℝ) := by
    have : (divState b B x M n : ℕ) + 1 ≤ B := hlt
    exact_mod_cast this
  have hmem : ((divState b B x M n : ℝ) + orbit b x n) / (B : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    have h0 : (0 : ℝ) ≤ orbit b x n := Int.fract_nonneg _
    have h1 : orbit b x n < 1 := Int.fract_lt_one _
    constructor
    · positivity
    · rw [div_lt_one hB']
      linarith
  show Int.fract ((x + (M : ℝ)) / (B : ℝ) * (b : ℝ) ^ n) = _
  rw [hkey, Int.fract_add_intCast, Int.fract_eq_self.2 hmem]

/-- The count of length-`T` chunks with a prescribed leading `l`-digit block. -/
theorem card_leadFilter (d v a : ℕ) (hd : 0 < d) (hv : v < a) :
    (((Finset.range (a * d)).filter fun t => t / d = v).card) = d := by
  classical
  have hset : ((Finset.range (a * d)).filter fun t => t / d = v)
      = Finset.Ico (v * d) ((v + 1) * d) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(Nat.le_div_iff_mul_le hd).1 (by omega), ?_⟩
      exact (Nat.div_lt_iff_lt_mul hd).1 (by omega)
    · rintro ⟨h1, h2⟩
      have hl : v ≤ t / d := (Nat.le_div_iff_mul_le hd).2 h1
      have hr : t / d < v + 1 := (Nat.div_lt_iff_lt_mul hd).2 h2
      refine ⟨?_, by omega⟩
      calc t < (v + 1) * d := h2
        _ ≤ a * d := Nat.mul_le_mul_right d (by omega)
  rw [hset, Nat.card_Ico]
  have : (v + 1) * d = v * d + d := by ring
  omega

/-- A period for `b` modulo `B`, as long as we like: Euler's theorem, iterated. -/
theorem exists_period (b B : ℕ) (hB : 0 < B) (hcop : Nat.Coprime B b) (l : ℕ) :
    ∃ T, l < T ∧ b ^ T % B = 1 % B := by
  refine ⟨Nat.totient B * (l + 1), ?_, ?_⟩
  · have := Nat.totient_pos.2 hB
    calc l < l + 1 := by omega
      _ ≤ Nat.totient B * (l + 1) := Nat.le_mul_of_pos_left _ this
  · have h1 : b ^ Nat.totient B ≡ 1 [MOD B] := Nat.ModEq.pow_totient hcop.symm
    have h2 : (b ^ Nat.totient B) ^ (l + 1) ≡ 1 ^ (l + 1) [MOD B] := h1.pow _
    rw [one_pow, ← pow_mul] at h2
    exact h2

/-- The tag set: length-`T` chunks whose leading `l` digits spell `v`. -/
noncomputable def tagSet (b T l v : ℕ) : Finset ℕ :=
  (Finset.range (b ^ T)).filter fun t => t / b ^ (T - l) = v

theorem tagSet_subset (b T l v : ℕ) : tagSet b T l v ⊆ Finset.range (b ^ T) :=
  Finset.filter_subset _ _

theorem card_tagSet (b T l v : ℕ) (hb : 2 ≤ b) (hlT : l ≤ T) (hv : v < b ^ l) :
    (tagSet b T l v).card = b ^ (T - l) := by
  have hb0 : 0 < b := by omega
  have hsplit : b ^ T = b ^ l * b ^ (T - l) := by rw [← pow_add]; congr 1; omega
  rw [tagSet, hsplit]
  exact card_leadFilter (b ^ (T - l)) v (b ^ l) (Nat.pow_pos hb0) hv

/-- **The identification.**  Along the arithmetic progression `n, n+T, n+2T, …` the joint
event `(state = j, next l digits = v)` is exactly the `WallCrux` walk indicator read off the
single depth-`T*K` digit block at `n`, with the (unbounded-prefix) state `divState … n` as
the walk's starting point. -/
theorem chi_eq_jointIndicator (b B : ℕ) (hb : 2 ≤ b) (hB : 0 < B) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (M : ℤ) (T l : ℕ) (hlT : 0 < l) (hlT' : l ≤ T)
    (hbT : b ^ T % B = 1 % B) (j : ℕ) (hj : j < B) (v K n k : ℕ) (hk : k < K) :
    WallCrux.chi (b ^ T) B (tagSet b T l v) (divState b B x M n) j K k
        (blockVal b x n (T * K))
      = (if divState b B x M (n + T * k) = j ∧ blockVal b x (n + T * k) l = v
          then (1 : ℝ) else 0) := by
  classical
  have hb0 : 0 < b := by omega
  have hT0 : 0 < T := by omega
  have hqpow : ∀ i : ℕ, (b ^ T) ^ i = b ^ (T * i) := fun i => (pow_mul b T i).symm
  set W := blockVal b x n (T * K) with hW
  -- (i) the leading chunks give the length-`T*k` prefix
  have hi : W / (b ^ T) ^ (K - k) = blockVal b x n (T * k) := by
    rw [hqpow, blockVal_prefix b hb x hx n (T * k) (T * K) (Nat.mul_le_mul_left T (by omega))]
    congr 2
    rw [← Nat.mul_sub]
  -- (ii) the state after `T*k` steps
  have hstate : divState b B x M (n + T * k)
      = (divState b B x M n + blockVal b x n (T * k)) % B := by
    have h0 : ((b : ℤ) ^ T) ≡ 1 [ZMOD (B : ℤ)] := by
      show ((b : ℤ) ^ T) % (B : ℤ) = (1 : ℤ) % (B : ℤ)
      have e1 : ((b : ℤ) ^ T) = ((b ^ T : ℕ) : ℤ) := by push_cast; ring
      have e2 : (1 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
      rw [e1, e2, ← Int.natCast_mod, ← Int.natCast_mod, hbT]
    have hpow1 : ((b : ℤ) ^ (T * k)) ≡ 1 [ZMOD (B : ℤ)] := by
      have := h0.pow k
      rw [one_pow, ← pow_mul] at this
      exact this
    have hsh := divState_shift b B hb hB x hx M n (T * k)
    have hcong : ((divState b B x M (n + T * k) : ℤ))
        ≡ ((divState b B x M n + blockVal b x n (T * k) : ℕ) : ℤ) [ZMOD (B : ℤ)] := by
      refine hsh.trans ?_
      push_cast
      exact Int.ModEq.add_right _ (by simpa using (hpow1.mul_right (divState b B x M n : ℤ)))
    have hlt : divState b B x M (n + T * k) < B := divState_lt b B hB x M (n + T * k)
    have hBz : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hB
    have h1 : (divState b B x M (n + T * k) : ℤ) % (B : ℤ)
        = ((divState b B x M n + blockVal b x n (T * k) : ℕ) : ℤ) % (B : ℤ) := hcong
    have h2 : (divState b B x M (n + T * k) : ℤ) % (B : ℤ)
        = (divState b B x M (n + T * k) : ℤ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)
    have h3 : (((divState b B x M n + blockVal b x n (T * k)) % B : ℕ) : ℤ)
        = ((divState b B x M n + blockVal b x n (T * k) : ℕ) : ℤ) % (B : ℤ) :=
      Int.natCast_mod _ _
    have h4 : (divState b B x M (n + T * k) : ℤ)
        = (((divState b B x M n + blockVal b x n (T * k)) % B : ℕ) : ℤ) := by
      rw [← h2, h1, h3]
    exact_mod_cast h4
  -- (iii) chunk `k` is the length-`T` block at `n + T*k`
  have hchunk : (W / (b ^ T) ^ (K - 1 - k)) % b ^ T = blockVal b x (n + T * k) T := by
    rw [hqpow, hW, blockVal_window b hb x hx n (T * k) T (T * K)
      (by calc T * k + T = T * (k + 1) := by ring
            _ ≤ T * K := Nat.mul_le_mul_left T (by omega))]
    congr 2
    obtain ⟨e, he⟩ : ∃ e, K = k + 1 + e := ⟨K - k - 1, by omega⟩
    subst he
    have hr : k + 1 + e - 1 - k = e := by omega
    rw [hr]
    have key : T * (k + 1 + e) - T * k - T = T * e := by
      have h1 : T * (k + 1 + e) = T * k + (T + T * e) := by ring
      rw [h1, Nat.add_sub_cancel_left, Nat.add_comm T (T * e), Nat.add_sub_cancel]
    rw [key]
  -- (iv) the tag condition
  have hlead : blockVal b x (n + T * k) T / b ^ (T - l) = blockVal b x (n + T * k) l :=
    (blockVal_prefix b hb x hx (n + T * k) l T hlT').symm
  have hmemS : ((W / (b ^ T) ^ (K - 1 - k)) % b ^ T ∈ tagSet b T l v)
      ↔ blockVal b x (n + T * k) l = v := by
    rw [tagSet, Finset.mem_filter, Finset.mem_range, hchunk, hlead]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [← hchunk]
    exact Nat.mod_lt _ (Nat.pow_pos hb0)
  have hcond : (blockVal b x n (T * k) + divState b B x M n) % B = j
      ↔ divState b B x M (n + T * k) = j := by
    rw [hstate, Nat.add_comm (divState b B x M n)]
  have hP : ((W / (b ^ T) ^ (K - k) + divState b B x M n) % B = j
        ∧ (W / (b ^ T) ^ (K - 1 - k)) % b ^ T ∈ tagSet b T l v)
      ↔ (divState b B x M (n + T * k) = j ∧ blockVal b x (n + T * k) l = v) := by
    rw [hi, hmemS, hcond]
  rw [WallCrux.chi]
  exact if_congr hP rfl rfl

/-- Shifting the summation window of a `[0,1]`-valued sequence costs at most the shift. -/
theorem shift_sum_diff (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1) (N s : ℕ) :
    |(∑ n ∈ Finset.range N, g (n + s)) - ∑ n ∈ Finset.range N, g n| ≤ (s : ℝ) := by
  have h1 : ∑ n ∈ Finset.range s, g n + ∑ n ∈ Finset.range N, g (s + n)
      = ∑ n ∈ Finset.range (s + N), g n := (Finset.sum_range_add g s N).symm
  have h2 : ∑ n ∈ Finset.range N, g n + ∑ n ∈ Finset.range s, g (N + n)
      = ∑ n ∈ Finset.range (N + s), g n := (Finset.sum_range_add g N s).symm
  have h3 : Finset.range (s + N) = Finset.range (N + s) := by rw [Nat.add_comm]
  rw [h3] at h1
  have hcomm : ∑ n ∈ Finset.range N, g (n + s) = ∑ n ∈ Finset.range N, g (s + n) :=
    Finset.sum_congr rfl fun n _ => by rw [Nat.add_comm]
  have hb1 : (0 : ℝ) ≤ ∑ n ∈ Finset.range s, g (N + n) :=
    Finset.sum_nonneg fun n _ => hg0 _
  have hb2 : ∑ n ∈ Finset.range s, g (N + n) ≤ (s : ℝ) := by
    calc ∑ n ∈ Finset.range s, g (N + n) ≤ ∑ _n ∈ Finset.range s, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => hg1 _
      _ = (s : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hb3 : (0 : ℝ) ≤ ∑ n ∈ Finset.range s, g n := Finset.sum_nonneg fun n _ => hg0 _
  have hb4 : ∑ n ∈ Finset.range s, g n ≤ (s : ℝ) := by
    calc ∑ n ∈ Finset.range s, g n ≤ ∑ _n ∈ Finset.range s, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => hg1 _
      _ = (s : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hcomm, abs_le]
  constructor <;> linarith

/-- The joint indicator of the crux, as a real-valued `[0,1]` sequence. -/
noncomputable def jointInd (b B : ℕ) (x : ℝ) (M : ℤ) (j v l n : ℕ) : ℝ :=
  if divState b B x M n = j ∧ blockVal b x n l = v then 1 else 0

theorem jointInd_nonneg (b B : ℕ) (x : ℝ) (M : ℤ) (j v l n : ℕ) :
    0 ≤ jointInd b B x M j v l n := by unfold jointInd; split <;> norm_num

theorem jointInd_le_one (b B : ℕ) (x : ℝ) (M : ℤ) (j v l n : ℕ) :
    jointInd b B x M j v l n ≤ 1 := by unfold jointInd; split <;> norm_num

/-- The shift average of the joint indicator is the `WallCrux` shift average `Psi`, started
at the current automaton state and evaluated at the depth-`T*K` digit block. -/
theorem shiftAvg_eq_Psi (b B : ℕ) (hb : 2 ≤ b) (hB : 0 < B) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (M : ℤ) (T l : ℕ) (hl : 0 < l) (hlT : l ≤ T)
    (hbT : b ^ T % B = 1 % B) (j : ℕ) (hj : j < B) (v K n : ℕ) :
    (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, jointInd b B x M j v l (n + T * k)
      = WallCrux.Psi (b ^ T) B (tagSet b T l v) (divState b B x M n) j K
          (blockVal b x n (T * K)) := by
  rw [WallCrux.Psi]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkK : k < K := Finset.mem_range.1 hk
  rw [chi_eq_jointIndicator b B hb hB x hx M T l hl hlT hbT j hj v K n k hkK, jointInd]

/-- **The analytic core.**  The joint count over `[0,N)` is within
`T*K + ∑_n (deviation of the shift average)` of `N·τ`, for any `τ`. -/
theorem jointSum_approx (b B : ℕ) (hb : 2 ≤ b) (hB : 0 < B) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (M : ℤ) (T l : ℕ) (hl : 0 < l) (hlT : l ≤ T)
    (hbT : b ^ T % B = 1 % B) (j : ℕ) (hj : j < B) (v K : ℕ) (hK : 0 < K) (τ : ℝ)
    (N : ℕ) :
    |(∑ n ∈ Finset.range N, jointInd b B x M j v l n) - (N : ℝ) * τ|
      ≤ ((T * K : ℕ) : ℝ)
        + ∑ n ∈ Finset.range N, ∑ ρ ∈ Finset.range B,
            |WallCrux.Psi (b ^ T) B (tagSet b T l v) ρ j K (blockVal b x n (T * K)) - τ| := by
  classical
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  set g : ℕ → ℝ := fun n => jointInd b B x M j v l n with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => jointInd_nonneg b B x M j v l n
  have hg1 : ∀ n, g n ≤ 1 := fun n => jointInd_le_one b B x M j v l n
  set A : ℝ := ∑ n ∈ Finset.range N, (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, g (n + T * k) with hA
  -- Step 1: the shift average is close to the plain average
  have hstep1 : |(∑ n ∈ Finset.range N, g n) - A| ≤ ((T * K : ℕ) : ℝ) := by
    have hswap : A = (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, ∑ n ∈ Finset.range N, g (n + T * k) := by
      rw [hA, ← Finset.mul_sum, Finset.sum_comm]
    have hconst : (∑ n ∈ Finset.range N, g n)
        = (K : ℝ)⁻¹ * ∑ _k ∈ Finset.range K, ∑ n ∈ Finset.range N, g n := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hKne, one_mul]
    rw [hswap, hconst, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < (K:ℝ)⁻¹)]
    have hterm : ∀ k ∈ Finset.range K,
        |(∑ n ∈ Finset.range N, g n) - ∑ n ∈ Finset.range N, g (n + T * k)|
          ≤ ((T * K : ℕ) : ℝ) := by
      intro k hk
      have hkK : k < K := Finset.mem_range.1 hk
      have h := shift_sum_diff g hg0 hg1 N (T * k)
      rw [abs_sub_comm] at h
      refine le_trans h ?_
      have : T * k ≤ T * K := Nat.mul_le_mul_left T (le_of_lt hkK)
      exact_mod_cast this
    calc (K : ℝ)⁻¹ * |∑ k ∈ Finset.range K,
            ((∑ n ∈ Finset.range N, g n) - ∑ n ∈ Finset.range N, g (n + T * k))|
        ≤ (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, ((T * K : ℕ) : ℝ) := by
          have h1 : |∑ k ∈ Finset.range K,
              ((∑ n ∈ Finset.range N, g n) - ∑ n ∈ Finset.range N, g (n + T * k))|
              ≤ ∑ k ∈ Finset.range K, ((T * K : ℕ) : ℝ) :=
            le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((T * K : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hKne, one_mul]
  -- Step 2: the shift average IS `Psi`
  have hstep2 : A = ∑ n ∈ Finset.range N,
      WallCrux.Psi (b ^ T) B (tagSet b T l v) (divState b B x M n) j K
        (blockVal b x n (T * K)) := by
    rw [hA]
    exact Finset.sum_congr rfl fun n _ =>
      shiftAvg_eq_Psi b B hb hB x hx M T l hl hlT hbT j hj v K n
  -- Step 3: each `Psi` is within the summed deviation of `τ`
  have hstep3 : |A - (N : ℝ) * τ|
      ≤ ∑ n ∈ Finset.range N, ∑ ρ ∈ Finset.range B,
          |WallCrux.Psi (b ^ T) B (tagSet b T l v) ρ j K (blockVal b x n (T * K)) - τ| := by
    rw [hstep2]
    have hNτ : (N : ℝ) * τ = ∑ _n ∈ Finset.range N, τ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hNτ, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n _ => ?_)
    have hrn : divState b B x M n ∈ Finset.range B :=
      Finset.mem_range.2 (divState_lt b B hB x M n)
    exact Finset.single_le_sum
      (f := fun ρ => |WallCrux.Psi (b ^ T) B (tagSet b T l v) ρ j K
        (blockVal b x n (T * K)) - τ|)
      (fun ρ _ => abs_nonneg _) hrn
  calc |(∑ n ∈ Finset.range N, g n) - (N : ℝ) * τ|
      ≤ |(∑ n ∈ Finset.range N, g n) - A| + |A - (N : ℝ) * τ| := by
        have := abs_add_le ((∑ n ∈ Finset.range N, g n) - A) (A - (N : ℝ) * τ)
        simpa using this
    _ ≤ _ := by linarith

/-- **CRUX LEAF (open): joint density of the automaton state and the digit block.**

Every remaining difficulty of Wall's theorem sits here.  The state `divState b B x M n`
depends on the *entire* digit prefix of `x`, so this is not a fixed-depth block count;
it says that the state is asymptotically uniform on `ℤ/B` and asymptotically independent
of the digits ahead of `n`.  See the module docstring for the shift-average +
Cauchy–Schwarz attack that `tendsto_blockAverage` and `divState_shift` are meant to
power (the shift is by multiples of `T = orderOf b` in `(ZMod B)ˣ`, which is what makes
`b^T ≡ 1` collapse `divState_shift` to `r (n+Tk) ≡ r n + W`). -/
theorem tendsto_jointDensity (b B : ℕ) (hb : 2 ≤ b) (hB : 0 < B) (hcop : Nat.Coprime B b)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (hxn : IsNormal b x) (M : ℤ)
    (l : ℕ) (hl : 0 < l) (j : ℕ) (hj : j < B) (v : ℕ) (hv : v < b ^ l) :
    Tendsto (fun N => (((Finset.range N).filter fun n =>
        divState b B x M n = j ∧ blockVal b x n l = v).card : ℝ) / N)
      atTop (𝓝 ((B : ℝ)⁻¹ * ((b : ℝ) ^ l)⁻¹)) := by
  sorry

/-- **CRUX (open).** Normality survives `x ↦ (x + M)/B` when `gcd(B, b) = 1`.

This is the one irreducible step of Wall's theorem: `orbit b ((x+M)/B) n` is
`(r n + orbit b x n)/B` with `r n = (⌊b^n x⌋ + b^n M) mod B` the long-division state,
and the statement is the joint equidistribution of that state with the future digits.
The state depends on the unbounded digit prefix, so no fixed-depth block count reaches
it and Weyl's criterion only reproduces the same problem at a rational frequency; see
the module docstring for the shift-average + Cauchy–Schwarz attack that
`tendsto_blockAverage` is meant to power. -/
theorem isNormal_add_int_div_coprime (b B : ℕ) (hb : 2 ≤ b) (hB : 0 < B)
    (hcop : Nat.Coprime B b) (x : ℝ) (M : ℤ) (hx : IsNormal b x) :
    IsNormal b ((x + (M : ℝ)) / B) := by

  classical
  have hbk : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hB' : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  -- reduce to `x ∈ [0,1)`
  have hx'mem : Int.fract x ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hx'n : IsNormal b (Int.fract x) := by
    show IsNormalSequence b (digitOf b (Int.fract (Int.fract x)))
    rw [Int.fract_fract]
    exact hx
  have hsplit : (x + (M : ℝ)) / B = (Int.fract x + (((M + ⌊x⌋ : ℤ)) : ℝ)) / B := by
    rw [Int.fract]
    push_cast
    ring
  rw [hsplit, isNormal_iff_equidistributed_orbit b hb]
  set x' : ℝ := Int.fract x with hx'def
  set M' : ℤ := M + ⌊x⌋ with hM'def
  refine equidistributed_of_badic b hb _ ?_
  intro k hk1 m hm
  have hbkp : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have hbkN : 0 < b ^ k := Nat.pow_pos (by omega)
  -- the (state, block) index
  set idx : ℕ → ℕ := fun n => divState b B x' M' n * b ^ k + blockVal b x' n k with hidx
  have hstate : ∀ n, divState b B x' M' n < B := fun n => divState_lt b B hB x' M' n
  have hblock : ∀ n, blockVal b x' n k < b ^ k := by
    intro n
    have hd : ∀ d ∈ ((List.range k).map fun i => digitOf b (Int.fract x') (n + i)), d < b := by
      intro d hd
      simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨i, _, rfl⟩ := hd
      exact digitOf_lt b hb _ _
    have h := blockNatVal_lt b ((List.range k).map fun i => digitOf b (Int.fract x') (n + i)) hd
    simpa [blockVal] using h
  have hdm : ∀ i : ℕ, i / b ^ k * b ^ k + i % b ^ k = i := by
    intro i
    rw [Nat.mul_comm]
    exact Nat.div_add_mod i (b ^ k)
  have hidxcomm : ∀ n, idx n = b ^ k * divState b B x' M' n + blockVal b x' n k := by
    intro n
    rw [hidx]
    simp only
    ring
  have hidxdiv : ∀ n, idx n / b ^ k = divState b B x' M' n := by
    intro n
    rw [hidxcomm n, Nat.mul_add_div hbkN, Nat.div_eq_of_lt (hblock n), Nat.add_zero]
  have hidxmod : ∀ n, idx n % b ^ k = blockVal b x' n k := by
    intro n
    rw [hidxcomm n, Nat.mul_add_mod, Nat.mod_eq_of_lt (hblock n)]
  -- pointwise: the cell condition is an interval condition on the index
  have hchar : ∀ n : ℕ,
      (orbit b ((x' + (M' : ℝ)) / B) n ∈
          Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k))
        ↔ (m * B ≤ idx n ∧ idx n < (m + 1) * B) := by
    intro n
    rw [orbit_add_div b B hB x' hx'mem M' n]
    have hV : ((blockVal b x' n k : ℕ) : ℤ) = ⌊orbit b x' n * (b : ℝ) ^ k⌋ :=
      (floor_orbit_mul_pow b hb x' hx'mem n k).symm
    have hstep1 : ((m : ℝ) / (b : ℝ) ^ k
          ≤ ((divState b B x' M' n : ℝ) + orbit b x' n) / B)
        ↔ ((m : ℝ) * B ≤ (divState b B x' M' n : ℝ) * (b : ℝ) ^ k
            + orbit b x' n * (b : ℝ) ^ k) := by
      rw [div_le_div_iff₀ hbkp hB', add_mul]
    have hstep2 : (((divState b B x' M' n : ℝ) + orbit b x' n) / B
          < ((m : ℝ) + 1) / (b : ℝ) ^ k)
        ↔ ((divState b B x' M' n : ℝ) * (b : ℝ) ^ k + orbit b x' n * (b : ℝ) ^ k
            < ((m : ℝ) + 1) * B) := by
      rw [div_lt_div_iff₀ hB' hbkp, add_mul]
    rw [Set.mem_Ico, hstep1, hstep2]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · have hz : ((m : ℤ) * B - (divState b B x' M' n : ℤ) * (b : ℤ) ^ k)
            ≤ ((blockVal b x' n k : ℕ) : ℤ) := by
          rw [hV, Int.le_floor]
          push_cast
          linarith [h1]
        zify
        rw [hidx]
        push_cast
        linarith [hz]
      · have hz : ⌊orbit b x' n * (b : ℝ) ^ k⌋
            < ((m : ℤ) + 1) * B - (divState b B x' M' n : ℤ) * (b : ℤ) ^ k := by
          rw [Int.floor_lt]
          push_cast
          linarith [h2]
        rw [← hV] at hz
        zify
        rw [hidx]
        push_cast
        linarith [hz]
    · intro h
      obtain ⟨h1, h2⟩ := h
      have h1' : ((m : ℤ) * B - (divState b B x' M' n : ℤ) * (b : ℤ) ^ k)
          ≤ ((blockVal b x' n k : ℕ) : ℤ) := by
        zify at h1
        rw [hidx] at h1
        push_cast at h1
        linarith
      have h2' : ((blockVal b x' n k : ℕ) : ℤ)
          < ((m : ℤ) + 1) * B - (divState b B x' M' n : ℤ) * (b : ℤ) ^ k := by
        zify at h2
        rw [hidx] at h2
        push_cast at h2
        linarith
      rw [hV, Int.le_floor] at h1'
      rw [hV, Int.floor_lt] at h2'
      push_cast at h1' h2'
      constructor
      · linarith [h1']
      · linarith [h2']
  have hcells : ∀ N : ℕ,
      (visitCount (orbit b ((x' + (M' : ℝ)) / B)) ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k) N : ℝ)
      = ∑ i ∈ Finset.Ico (m * B) ((m + 1) * B),
          ((((Finset.range N).filter fun n =>
            divState b B x' M' n = i / b ^ k ∧ blockVal b x' n k = i % b ^ k).card : ℕ) : ℝ) := by
    intro N
    have hL : (visitCount (orbit b ((x' + (M' : ℝ)) / B)) ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k) N : ℝ)
        = ∑ n ∈ Finset.range N, (if orbit b ((x' + (M' : ℝ)) / B) n ∈
            Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)
          then (1 : ℝ) else 0) := by
      rw [visitCount, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : orbit b ((x' + (M' : ℝ)) / B) n ∈
          Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k) <;> simp [h]
    have hR : ∀ i : ℕ, ((((Finset.range N).filter fun n =>
          divState b B x' M' n = i / b ^ k ∧ blockVal b x' n k = i % b ^ k).card : ℕ) : ℝ)
        = ∑ n ∈ Finset.range N,
            (if divState b B x' M' n = i / b ^ k ∧ blockVal b x' n k = i % b ^ k
              then (1 : ℝ) else 0) := by
      intro i
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : divState b B x' M' n = i / b ^ k ∧ blockVal b x' n k = i % b ^ k <;>
        simp [h]
    rw [hL, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.Ico (m * B) ((m + 1) * B)) => hR i),
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hin : m * B ≤ idx n ∧ idx n < (m + 1) * B
    · rw [if_pos ((hchar n).2 hin)]
      rw [Finset.sum_eq_single_of_mem (idx n) (Finset.mem_Ico.2 hin) ?_]
      · rw [if_pos ⟨(hidxdiv n).symm, (hidxmod n).symm⟩]
      · intro i _ hne
        refine if_neg ?_
        intro hc
        exact hne (by rw [hidx]; simp only; rw [hc.1, hc.2, hdm i])
    · rw [if_neg (fun hcon => hin ((hchar n).1 hcon))]
      refine (Finset.sum_eq_zero fun i hi => ?_).symm
      refine if_neg ?_
      intro hc
      have : i = idx n := by
        rw [hidx]; simp only; rw [hc.1, hc.2, hdm i]
      rw [this] at hi
      exact hin (Finset.mem_Ico.1 hi)
  -- each grid cell has density 1/(B b^k)
  have hlim : ∀ i ∈ Finset.Ico (m * B) ((m + 1) * B),
      Tendsto (fun N => ((((Finset.range N).filter fun n =>
          divState b B x' M' n = i / b ^ k ∧ blockVal b x' n k = i % b ^ k).card : ℕ) : ℝ) / N)
        atTop (𝓝 ((B : ℝ)⁻¹ * ((b : ℝ) ^ k)⁻¹)) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    have hik : i < B * b ^ k := by
      have hmb : m + 1 ≤ b ^ k := hm
      calc i < (m + 1) * B := hi2
      _ ≤ b ^ k * B := Nat.mul_le_mul_right B hmb
      _ = B * b ^ k := by ring
    have hjB : i / b ^ k < B := Nat.div_lt_of_lt_mul (by rw [mul_comm] at hik; exact hik)
    exact tendsto_jointDensity b B hb hB hcop x' hx'mem hx'n M' k hk1 (i / b ^ k) hjB
      (i % b ^ k) (Nat.mod_lt _ hbkN)
  have hsum := tendsto_finsetSum _ hlim
  have hval : (∑ _i ∈ Finset.Ico (m * B) ((m + 1) * B), (B : ℝ)⁻¹ * ((b : ℝ) ^ k)⁻¹)
      = 1 / (b : ℝ) ^ k := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((m + 1) * B - m * B : ℕ) = B := by
      have : (m + 1) * B = m * B + B := by ring
      omega
    rw [hcard]
    field_simp
  rw [hval] at hsum
  refine hsum.congr fun N => ?_
  rw [hcells N, Finset.sum_div]

end WallRational

/-- **Wall (1949)**: rational affine maps preserve base-`b` normality. -/
theorem isNormal_rat_mul_add (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (q r : ℚ) (hq : q ≠ 0)
    (hx : IsNormal b x) : IsNormal b ((q : ℝ) * x + r) := by

  have hVpos : 0 < q.den * r.den := Nat.mul_pos q.pos r.pos
  obtain ⟨A, B, κ, hA, hB, hVAB, hAdvd, hBcop⟩ :=
    WallRational.exists_smooth_coprime_split b hb (q.den * r.den) hVpos
  obtain ⟨cc, hcc⟩ := hAdvd
  have hbk0 : 0 < b ^ κ := Nat.pow_pos (by omega)
  have hcc0 : 0 < cc := by
    rcases Nat.eq_zero_or_pos cc with h | h
    · rw [h, Nat.mul_zero] at hcc; omega
    · exact h
  set m : ℤ := (cc : ℤ) * q.num * (r.den : ℤ) with hmdef
  set N : ℤ := (cc : ℤ) * (q.den : ℤ) * r.num with hNdef
  have hqnum : q.num ≠ 0 := Rat.num_ne_zero.2 hq
  have hm0 : m ≠ 0 := by
    rw [hmdef]
    have h1 : (cc : ℤ) ≠ 0 := by omega
    have h2 : ((r.den : ℤ)) ≠ 0 := by
      have := r.pos
      omega
    exact mul_ne_zero (mul_ne_zero h1 hqnum) h2
  have h1 : IsNormal b ((m : ℝ) * x) := WallRational.isNormal_intMul b hb x m hm0 hx
  have h2 : IsNormal b (((m : ℝ) * x + (N : ℝ)) / B) :=
    WallRational.isNormal_add_int_div_coprime b B hb hB hBcop _ N h1
  have h3 : IsNormal b ((((m : ℝ) * x + (N : ℝ)) / B) / (b : ℝ) ^ κ) :=
    WallRational.isNormal_div_pow b hb _ κ h2
  have hbR : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hccR : (0 : ℝ) < (cc : ℝ) := by exact_mod_cast hcc0
  have hqdR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  have hrdR : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hbkR : ((b : ℝ)) ^ κ = (A : ℝ) * (cc : ℝ) := by
    have hnat : ((b ^ κ : ℕ) : ℝ) = ((A * cc : ℕ) : ℝ) := by rw [hcc]
    push_cast at hnat
    exact hnat
  have hVR : (q.den : ℝ) * (r.den : ℝ) = (A : ℝ) * (B : ℝ) := by
    have hnat : ((q.den * r.den : ℕ) : ℝ) = ((A * B : ℕ) : ℝ) := by rw [hVAB]
    push_cast at hnat
    exact hnat
  have hval : (q : ℝ) * x + (r : ℝ)
      = (((m : ℝ) * x + (N : ℝ)) / B) / (b : ℝ) ^ κ := by
    rw [div_div, hbkR,
      eq_div_iff (mul_ne_zero (ne_of_gt hBR) (mul_ne_zero (ne_of_gt hAR) (ne_of_gt hccR)))]
    rw [show (B : ℝ) * ((A : ℝ) * (cc : ℝ)) = ((A : ℝ) * (B : ℝ)) * (cc : ℝ) from by ring,
      ← hVR, Rat.cast_def, Rat.cast_def, hmdef, hNdef]
    push_cast
    field_simp
    try ring
  rw [hval]
  exact h3

end NormalNumbers
