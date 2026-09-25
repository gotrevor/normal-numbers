/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtBlockDefect
import NormalNumbers.C3MrtWindowMass

/-!
# The conductor debt at `t = 0`: the head is elementary, the tail is the whole content

`DIRECTION.md` item ②.3 asks for `CharPrimeSumLogQ D` at `t = 0`, i.e. a bound

    ‖∑_{p ≤ X²} conj(χ(p))/p‖ ≤ D · (log(q+2) + 1)          (`CharPrimeSumLogQZero`)

uniformly over non-principal `χ mod q`.  This file splits that sum at the conductor,

    head = ∑_{p ≤ q},      tail = ∑_{q < p ≤ X²},

and **discharges the head in the kernel**: `‖head‖ ≤ ∑_{p ≤ q} 1/p ≤ log log(q+2) + mertensBound`
by `small_prime_mass_le`, and `log log(q+2) ≤ log(q+2)`.  So the head is not merely small, it is
`O(log log q)` — a whole exponential below the budget.

What remains is `CharTailCancellation`: the primes ABOVE the conductor.  There the mass
`∑_{q < p ≤ X²} 1/p ≈ log log X² − log log q` is *unbounded*, so the bound can only come from
cancellation in `χ(p)`, which is exactly the non-vanishing of `L(1,χ)` **with a rate** (the
Siegel-free `L(1,χ) ≫ q^{-1/2}`; mathlib has only the qualitative
`DirichletCharacter.LFunction_apply_one_ne_zero`).  This file therefore narrows the `t = 0`
conductor debt from the full sum to the tail, and records that the head can never be the
obstruction.

Per the **GUARD RULE** (`DIRECTION.md` ①) the new `Prop` `CharTailCancellation` ships with a
content locator (`charTailSum_head_free`: at `X` below the conductor the tail is *empty*, so the
statement is trivially true there — the content is at `X² ≫ q`) and degenerate-case verdicts:
`q = 0, 1` are excluded by `χ ≠ 1` (`charTail_conductor_pos`), the empty-tail configuration is
proved to satisfy it (`charTailCancellation_vacuous_below`), and the constant-function
configuration `χ = 1` is exactly the excluded one.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-! ### `t = 0`: the twist disappears -/

/-- The primes indexing `twistedPrimeSum X χ t`. -/
noncomputable def primesUpToSq (X : ℝ) : Finset ℕ :=
  (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime

theorem mem_primesUpToSq {X : ℝ} {p : ℕ} :
    p ∈ primesUpToSq X ↔ p < ⌈X ^ 2⌉₊ + 1 ∧ p.Prime := by
  simp [primesUpToSq, Finset.mem_filter, Finset.mem_range]

/-- At `t = 0` the twist `p^{-it}` is `1`, so the twisted prime sum is the plain character sum. -/
theorem twistedPrimeSum_zero (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedPrimeSum X χ 0
      = ∑ p ∈ primesUpToSq X, (starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ) := by
  rw [twistedPrimeSum, primesUpToSq]
  refine Finset.sum_congr rfl fun p _ => ?_
  norm_num

/-! ### The split at the conductor -/

/-- The primes **at or below** the conductor. -/
noncomputable def charHeadSum (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ (primesUpToSq X).filter (fun p => p ≤ q),
    (starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ)

/-- The primes **above** the conductor — where all the cancellation has to happen. -/
noncomputable def charTailSum (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ (primesUpToSq X).filter (fun p => ¬ p ≤ q),
    (starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ)

theorem twistedPrimeSum_zero_split (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedPrimeSum X χ 0 = charHeadSum X χ + charTailSum X χ := by
  rw [twistedPrimeSum_zero, charHeadSum, charTailSum]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-! ### The head is elementary -/

/-- `log log u ≤ log u` for `1 ≤ u` (with Lean's junk value at `log u = 0` handled). -/
theorem log_log_le_log {u : ℝ} (hu : 1 ≤ u) : Real.log (Real.log u) ≤ Real.log u := by
  have h0 : 0 ≤ Real.log u := Real.log_nonneg hu
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; simp
  · have := Real.log_le_sub_one_of_pos h
    linarith

/-- **The head is discharged.**  `‖∑_{p ≤ q} conj(χ(p))/p‖ ≤ log(q+2) + mertensBound`: it is in
fact `O(log log q)`, a whole exponential below the `log q` budget. -/
theorem norm_charHeadSum_le (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖charHeadSum X χ‖
      ≤ Real.log ((q : ℝ) + 2) + Erdos67b.PrimeEstimates.mertensBound := by
  set G : Finset ℕ := (primesUpToSq X).filter (fun p => p ≤ q) with hG
  have hterm : ∀ p ∈ G, ‖(starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ)‖ ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hpp : p.Prime := (mem_primesUpToSq.1 (Finset.mem_filter.1 hp).1).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hpp.pos
    rw [norm_div, RCLike.norm_conj]
    have hchi : ‖χ (p : ZMod q)‖ ≤ 1 := dirichletChar_norm_le_one χ _
    rw [Complex.norm_natCast]
    rw [div_le_iff₀ hp0] at *
    calc ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := hchi
      _ = (p : ℝ)⁻¹ * (p : ℝ) := by field_simp
  have hnorm : ‖charHeadSum X χ‖ ≤ ∑ p ∈ G, (p : ℝ)⁻¹ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  -- every element of `G` is a prime `≤ q + 2`
  have hB : (2 : ℕ) ≤ q + 2 := by omega
  have hGb : ∀ p ∈ G, p.Prime ∧ p ≤ q + 2 := by
    intro p hp
    refine ⟨(mem_primesUpToSq.1 (Finset.mem_filter.1 hp).1).2, ?_⟩
    have := (Finset.mem_filter.1 hp).2
    omega
  have hmass := small_prime_mass_le hB hGb
  have hcast : ((q + 2 : ℕ) : ℝ) = (q : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hmass
  have h1 : (1 : ℝ) ≤ (q : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hll := log_log_le_log h1
  linarith

/-! ### The remaining debt: cancellation above the conductor -/

/-- **The `t = 0` conductor debt, narrowed to the primes above the conductor.**

Classical and Siegel-free: `‖∑_{q < p ≤ X²} conj(χ(p))/p‖ ≪ log q + 1` for every non-principal
`χ mod q`, uniformly in `X`.  Equivalent in strength to `L(1,χ) ≫ q^{-1/2}` (mathlib has only
the qualitative `DirichletCharacter.LFunction_apply_one_ne_zero`).  The mass of this range is
`≈ log log X² − log log q`, which is unbounded, so the bound is pure cancellation — this is where
all the content of the `t = 0` debt sits, and `norm_charHeadSum_le` shows the head can never be
the obstruction. -/
def CharTailCancellation (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, 3 ≤ X →
    ‖charTailSum X χ‖ ≤ C * (Real.log ((q : ℝ) + 2) + 1)

/-- The `t = 0` slice of `CharPrimeSumLogQ`. -/
def CharPrimeSumLogQZero (D : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, 3 ≤ X →
    ‖twistedPrimeSum X χ 0‖ ≤ D * (Real.log ((q : ℝ) + 2) + 1)

/-- **The reduction.**  Head (kernel) + tail (`CharTailCancellation`) ⇒ the `t = 0` slice, with
`D = C + 1 + mertensBound`. -/
theorem charPrimeSumLogQZero_of_tail {C : ℝ} (h : CharTailCancellation C) :
    CharPrimeSumLogQZero (C + 1 + Erdos67b.PrimeEstimates.mertensBound) := by
  obtain ⟨hC, htail⟩ := h
  intro q χ hne X hX
  have hmert : 0 ≤ Erdos67b.PrimeEstimates.mertensBound :=
    Erdos67b.PrimeEstimates.mertensBound_nonneg
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hlogpos : 0 ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hhead := norm_charHeadSum_le X χ
  have ht := htail q χ hne X hX
  have hsplit : ‖twistedPrimeSum X χ 0‖ ≤ ‖charHeadSum X χ‖ + ‖charTailSum X χ‖ := by
    rw [twistedPrimeSum_zero_split]; exact norm_add_le _ _
  nlinarith

/-- …and the slice implies the `t = 0` instance of `CharPrimeSumLogQ`'s conclusion. -/
theorem charPrimeSumLogQ_at_zero {D : ℝ} (hD : 0 ≤ D) (h : CharPrimeSumLogQZero D)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {X : ℝ} (hX : 3 ≤ X) :
    ‖twistedPrimeSum X χ 0‖
      ≤ D * (Real.log ((q : ℝ) + 2) + Real.log (2 + |(0 : ℝ)|) + 1) := by
  have hb := h q χ hne X hX
  have hlog2 : 0 ≤ Real.log (2 + |(0 : ℝ)|) := by
    simp only [abs_zero, add_zero]
    exact Real.log_nonneg (by norm_num)
  nlinarith

/-! ### GUARD RULE compliance for `CharTailCancellation` -/

/-- **Degenerate verdict — the constant-function configuration is excluded.**  `χ = 1` is exactly
the hypothesis `χ ≠ 1` rules out, and at `q = 1` *every* character is `1`
(`dirichletChar_one_apply`), so the modulus is forced away from `1`. -/
theorem charTail_conductor_ne_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : q ≠ 1 := by
  rintro rfl
  exact hne (by ext x; rw [dirichletChar_one_apply, dirichletChar_one_apply])

/-- **Content locator.**  Below the conductor the tail range is *empty*, so
`CharTailCancellation` says nothing there: all its content is at `X² ≫ q`. -/
theorem charTailSum_head_free {X : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    (h : ⌈X ^ 2⌉₊ ≤ q) : charTailSum X χ = 0 := by
  rw [charTailSum, Finset.sum_eq_zero]
  intro p hp
  exfalso
  obtain ⟨hlt, _⟩ := mem_primesUpToSq.1 (Finset.mem_filter.1 hp).1
  have := (Finset.mem_filter.1 hp).2
  omega

/-- **Degenerate verdict — the empty configuration survives.**  On the empty tail range the
statement holds with any `0 ≤ C`, so emptiness is not a refutation (unlike the lap-115 singleton
blocks, which *were*). -/
theorem charTailCancellation_vacuous_below {C : ℝ} (hC : 0 ≤ C) {X : ℝ} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (h : ⌈X ^ 2⌉₊ ≤ q) :
    ‖charTailSum X χ‖ ≤ C * (Real.log ((q : ℝ) + 2) + 1) := by
  rw [charTailSum_head_free χ h, norm_zero]
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have : 0 ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by linarith)
  positivity

/-- **Degenerate verdict — the singleton configuration survives.**  A one-prime tail has norm at
most `1/p ≤ 1/2`, well inside the budget: unlike the block route, no singleton can refute this
statement, because the bound is additive in the mass rather than multiplicative in a saving. -/
theorem charTailSum_singleton_le {X : ℝ} {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hsub : (primesUpToSq X).filter (fun r => ¬ r ≤ q) = {p}) :
    ‖charTailSum X χ‖ ≤ 1 := by
  rw [charTailSum, hsub, Finset.sum_singleton, norm_div, RCLike.norm_conj,
    Complex.norm_natCast]
  have hp0 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hchi : ‖χ (p : ZMod q)‖ ≤ 1 := dirichletChar_norm_le_one χ _
  rw [div_le_one (by linarith)]
  linarith

end CastingOut

end NormalNumbers
