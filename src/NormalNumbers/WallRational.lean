/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Wall
import NormalNumbers.WeylCriterion

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
  sorry

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
