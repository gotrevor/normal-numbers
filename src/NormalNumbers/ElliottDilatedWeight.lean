import NormalNumbers.ElliottDilatedCorrelation

/-!
# A lower bound for the dilated correlation weight

`NormalNumbers.ElliottDilatedCorrelation.dilatedCorrelationWeight H a c₁ h s` is the coefficient
multiplying the affine correlation after averaging all actual `a`-dilated graph edges: the prime
`p` contributes

```
#{ j < H : a·j + (p c₁ mod a) + p·h < H } / p.
```

It is the dilated analogue of `Erdos67b.primeGraphCorrelationWeight`, whose prime `p` contributes
`(H - p h)/p`.  The count is about `H/(a p)` rather than `H/p`, because only every `a`-th block
position lies in the progression the dilated edge samples.  Since `a` is a constant fixed before
every parameter of the argument, that is a constant loss — exactly the pattern of this whole
campaign.

This file is **function-free counting**: nothing here mentions `f₁`, `f₂` or the graph.

* `card_dilatedProgression_lower` — the count is at least `H/(4a)`, provided
  `4a ≤ H` and `2(a + p h) ≤ H`.  The `4` rather than `2` is the cost of the floor in
  `H/(2a)`.
* `quarter_mul_reciprocal_le_dilatedCorrelationWeight` — hence the weight is at least
  `H/(4a) · ∑_{p ∈ s} 1/p`.
* `exists_dyadic_dilatedCorrelationWeight_lower` — the dilated analogue of
  `Erdos67b.exists_dyadic_primeGraphCorrelationWeight_lower`: at a dyadic prime block `(P, 2P]` the
  weight is at least `H / (16 a log P)`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators
open Finset Filter

namespace NormalNumbers.ElliottDilatedWeight

open Erdos67b
open NormalNumbers.ElliottDilatedCorrelation

noncomputable section

/-! ## The counting lemma -/

/-- **The dilated progression is long.**  Among the `H` block positions `j`, at least `H/(4a)`
satisfy `a j + r + b < H`, whenever `r < a`, `4a ≤ H` and `2(a + b) ≤ H`.

The active positions are `j = 0, 1, …`, so the count is `⌈(H - r - b)/a⌉`; the hypotheses make
`r + b ≤ H/2 - 1`, leaving at least `H/(2a)` positions, and the floor costs another factor `2`. -/
theorem card_dilatedProgression_lower {H a r b : ℕ} (ha : 0 < a) (hr : r < a)
    (h4a : 4 * a ≤ H) (hb : 2 * (a + b) ≤ H) :
    (H : ℝ) / (4 * a) ≤
      ((Finset.univ.filter (fun j : Fin H ↦ a * j.1 + r + b < H)).card : ℝ) := by
  classical
  have hHpos : 0 < H := by omega
  set N : ℕ := H / (2 * a) with hNdef
  have h2a : 0 < 2 * a := by omega
  have hNle : N * (2 * a) ≤ H := Nat.div_mul_le_self H (2 * a)
  have hNlt : H < 2 * a * N + 2 * a := by
    have hmod : 2 * a * N + H % (2 * a) = H := Nat.div_add_mod H (2 * a)
    have hmodlt : H % (2 * a) < 2 * a := Nat.mod_lt _ h2a
    omega
  have hNa : 2 * (a * N) ≤ H := by
    have he : 2 * (a * N) = N * (2 * a) := by ring
    rw [he]; exact hNle
  -- every `j < N` is an active position
  have hactive : ∀ j : ℕ, j < N → a * j + r + b < H := by
    intro j hj
    have h1 : a * j + a ≤ a * N := by
      have he : a * j + a = a * (j + 1) := by ring
      rw [he]; exact Nat.mul_le_mul_left a (by omega)
    omega
  have hNH : N ≤ H := le_trans (Nat.le_mul_of_pos_right N h2a) hNle
  -- hence the count is at least `N`
  have hcard : N ≤ (Finset.univ.filter (fun j : Fin H ↦ a * j.1 + r + b < H)).card := by
    have := Finset.card_le_card_of_injOn
      (f := fun j : ℕ ↦ (⟨j % H, Nat.mod_lt _ hHpos⟩ : Fin H))
      (s := Finset.range N)
      (t := Finset.univ.filter (fun j : Fin H ↦ a * j.1 + r + b < H))
      (by
        intro j hj
        have hjN : j < N := Finset.mem_range.mp hj
        have hjH : j % H = j := Nat.mod_eq_of_lt (by omega)
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [hjH] using hactive j hjN)
      (by
        intro x hx y hy hxy
        have hxN : x < N := Finset.mem_range.mp hx
        have hyN : y < N := Finset.mem_range.mp hy
        have hx' : x % H = x := Nat.mod_eq_of_lt (by omega)
        have hy' : y % H = y := Nat.mod_eq_of_lt (by omega)
        have := congrArg Fin.val hxy
        simp only [hx', hy'] at this
        exact this)
    simpa using this
  -- and `N ≥ H/(4a)`
  have hNreal : (H : ℝ) / (4 * a) ≤ (N : ℝ) := by
    have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
    have h1 : (H : ℝ) < 2 * a * N + 2 * a := by exact_mod_cast hNlt
    have h2 : (4 : ℝ) * a ≤ H := by exact_mod_cast h4a
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine hNreal.trans ?_
  exact_mod_cast hcard

/-! ## The weight bound -/

theorem dilatedCorrelationWeight_nonneg (H a c₁ h : ℕ) (s : Finset ℕ) :
    0 ≤ dilatedCorrelationWeight H a c₁ h s := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> positivity

theorem dilatedCorrelationWeight_eq_sum {H : ℕ} (a c₁ h : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Nat.primesLE H) :
    dilatedCorrelationWeight H a c₁ h s =
      ∑ p ∈ s, ((Finset.univ.filter
        (fun j : Fin H ↦ a * j.1 + (p * c₁) % a + p * h < H)).card : ℝ) / p := by
  classical
  calc
    _ = ∑ p ∈ Nat.primesLE H, if p ∈ s then ((Finset.univ.filter
          (fun j : Fin H ↦ a * j.1 + (p * c₁) % a + p * h < H)).card : ℝ) / p else 0 :=
      Finset.sum_coe_sort (Nat.primesLE H) _
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun hp ↦ hp.2, fun hp ↦ ⟨hs hp, hp⟩⟩

/-- **The dilated analogue of `Erdos67b.half_mul_reciprocal_le_primeGraphCorrelationWeight`.**
The dilation costs a factor `2a` relative to the undilated `H/2`. -/
theorem quarter_mul_reciprocal_le_dilatedCorrelationWeight
    {H a : ℕ} (ha : 0 < a) (c₁ h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H)
    (h4a : 4 * a ≤ H) (hstep : ∀ p ∈ s, 2 * (a + p * h) ≤ H) :
    (H : ℝ) / (4 * a) * (∑ p ∈ s, (p : ℝ)⁻¹) ≤ dilatedCorrelationWeight H a c₁ h s := by
  rw [dilatedCorrelationWeight_eq_sum a c₁ h s hs, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hppos : 0 < p := (Nat.prime_of_mem_primesLE (hs hp)).pos
  have hcount := card_dilatedProgression_lower (H := H) (a := a) (r := (p * c₁) % a)
    (b := p * h) ha (Nat.mod_lt _ ha) h4a (hstep p hp)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcount (by positivity)

/-! ## The dyadic block -/

/-- **The dilated analogue of `Erdos67b.exists_dyadic_primeGraphCorrelationWeight_lower`.**
A dyadic prime block `(P, 2P]` retains a graph coefficient `≫ H / (a log P)`, uniformly in the
block length, the base shift `c₁` and the edge multiplier `h`. -/
theorem exists_dyadic_dilatedCorrelationWeight_lower :
    ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀, ∀ H a c₁ h : ℕ, 0 < a →
      2 * P ≤ H → 4 * a + 4 * P * h ≤ H →
      (H : ℝ) / (16 * a * Real.log P) ≤
        dilatedCorrelationWeight H a c₁ h (PrimeEstimates.dyadicPrimes P) := by
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp
    PrimeEstimates.eventually_dyadicPrimeMass_lower
  refine ⟨max P₀ 2, le_max_right _ _, ?_⟩
  intro P hP H a c₁ h ha hPH hstep
  have hmass := hP₀ P ((le_max_left _ _).trans hP)
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hsubset : PrimeEstimates.dyadicPrimes P ⊆ Nat.primesLE H := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1.trans hPH, hp'.2.2⟩
  have hquarter := quarter_mul_reciprocal_le_dilatedCorrelationWeight ha c₁ h
    (PrimeEstimates.dyadicPrimes P) hsubset (by omega) (by
      intro p hp
      have hp' := (PrimeEstimates.mem_primesInInterval.mp hp).2.1
      nlinarith)
  calc
    (H : ℝ) / (16 * a * Real.log P) = (H : ℝ) / (4 * a) * ((1 / 4 : ℝ) / Real.log P) := by
      rw [div_mul_div_comm]
      ring_nf
    _ ≤ (H : ℝ) / (4 * a) * PrimeEstimates.dyadicPrimeMass P :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ dilatedCorrelationWeight H a c₁ h (PrimeEstimates.dyadicPrimes P) := hquarter

end

end NormalNumbers.ElliottDilatedWeight

#print axioms NormalNumbers.ElliottDilatedWeight.exists_dyadic_dilatedCorrelationWeight_lower
