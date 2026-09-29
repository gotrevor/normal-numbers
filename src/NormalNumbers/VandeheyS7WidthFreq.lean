/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-WF: the width floor in FREQUENCY form is a PIGEONHOLE on the clock

The directive (lap 74) kills the *uniform* width floor and asks for the frequency form,
`freq{n : width(sₙ) < η} → 0 as η → 0`.  Nine laps treated that as needing new ergodic input.
It does not.  Here is the argument, and it is unconditional:

* lap 74's `MobState.fib_sq_mul_width_le_of_forced` is the implication *long forced block ⟹ narrow
  state*.  Its converse — *narrow state ⟹ long block* — is the geometric content of directive
  fact (β): a state that cannot emit has its image `J` straddling a digit boundary `1/k`, and if
  `|J| = width` is tiny then the emitter has fallen a distance `log(1/width)` behind, which the
  very next input digit pays back as one long emitted block.  It is the hypothesis
  `NarrowForcesBlock` below.
* Blocks of length `≥ L` cannot be frequent, **for free**: the block lengths telescope to the clock,
  `Σ_{n<p} Lₙ = N p`, so `L · #{n < p : Lₙ ≥ L} ≤ N p`.  That is Markov's inequality with no
  measure in sight — `card_longBlock_le`.
* So with a clock rate `N p ≤ Λ p` (the output expansion is at most `Λ` digits per input digit —
  a Lévy-type bound on the image, which the counting side already supplies freely),
  `freq{n < p : Lₙ ≥ L} ≤ Λ / L`, hence `freq{n : width(sₙ) < η} ≤ Λ / L(η) → 0`.

**This is why the two halves are one hypothesis, in the useful direction.**  Lap 74 showed a width
floor CAPS the block length; this module shows the block lengths' own budget FORCES the width floor
in frequency.  The residual of the §7 crux is therefore `BlockAverageBound` alone
(`VandeheyS7Decomp`) — directive fact (α) — plus the two geometric inputs named here.

Degenerate cases: `L = 0` makes the long-block count trivially `p` and the bound vacuous (hence
`1 ≤ L`); `p = 0` makes the frequency `0/0` (hence `0 < p`).
-/
import NormalNumbers.VandeheyS7Decomp

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-! ## The block lengths telescope to the clock -/

/-- The block length: the number of output digits emitted while reading input digit `n`. -/
def blockLength (N : ℕ → ℕ) (n : ℕ) : ℕ := N (n + 1) - N n

/-- **The budget.**  The block lengths sum to the clock. -/
theorem sum_blockLength (N : ℕ → ℕ) (hN0 : N 0 = 0) (hmono : Monotone N) (p : ℕ) :
    ∑ n ∈ Finset.range p, blockLength N n = N p := by
  induction p with
  | zero => simp [hN0]
  | succ p ih =>
    rw [Finset.sum_range_succ, ih, blockLength]
    have : N p ≤ N (p + 1) := hmono (Nat.le_succ p)
    omega

/-! ## Markov's inequality for the clock: long blocks are rare, for free -/

/-- The set of input times before `p` whose emitted block has length at least `L`. -/
def longBlocks (N : ℕ → ℕ) (L p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun n => L ≤ blockLength N n

/-- **Markov, with no measure.**  `L · #{n < p : Lₙ ≥ L} ≤ N p`. -/
theorem card_longBlock_le (N : ℕ → ℕ) (hN0 : N 0 = 0) (hmono : Monotone N) (L p : ℕ) :
    L * (longBlocks N L p).card ≤ N p := by
  rw [← sum_blockLength N hN0 hmono p]
  calc L * (longBlocks N L p).card
      = ∑ _n ∈ longBlocks N L p, L := by rw [Finset.sum_const, mul_comm, smul_eq_mul]
    _ ≤ ∑ n ∈ longBlocks N L p, blockLength N n := by
        refine Finset.sum_le_sum fun n hn => ?_
        exact (Finset.mem_filter.1 hn).2
    _ ≤ ∑ n ∈ Finset.range p, blockLength N n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro i _ _; exact Nat.zero_le _

/-- **The frequency form.**  With a clock rate `N p ≤ Λ p`, long blocks have frequency `≤ Λ / L`. -/
theorem freq_longBlock_le (N : ℕ → ℕ) (hN0 : N 0 = 0) (hmono : Monotone N)
    {Λ : ℝ} {L p : ℕ} (hL : 1 ≤ L) (hp : 0 < p) (hrate : (N p : ℝ) ≤ Λ * p) :
    ((longBlocks N L p).card : ℝ) / p ≤ Λ / L := by
  have hLR : (0:ℝ) < L := by exact_mod_cast hL
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have h1 : (L : ℝ) * ((longBlocks N L p).card : ℝ) ≤ (N p : ℝ) := by
    exact_mod_cast card_longBlock_le N hN0 hmono L p
  rw [div_le_div_iff₀ hpR hLR]
  calc ((longBlocks N L p).card : ℝ) * L = (L : ℝ) * (longBlocks N L p).card := by ring
    _ ≤ (N p : ℝ) := h1
    _ ≤ Λ * p := hrate

/-! ## Narrow states are rare

`NarrowForcesBlock` is the converse of lap 74's `fib_sq_mul_width_le_of_forced`: a state too narrow
to emit has fallen behind by `log(1/width)`, and the next input digit pays that back as one long
block.  Given it, narrowness inherits the long-block frequency bound *verbatim*. -/

/-- **The geometric input.**  A state of width `< η` emits, at that input time, a block of length
at least `L`. -/
def NarrowForcesBlock (s : ℕ → MobState) (N : ℕ → ℕ) (η : ℝ) (L : ℕ) : Prop :=
  ∀ n, (s n).width < η → L ≤ blockLength N n

/-- **S7-WF.**  The width floor holds in frequency: narrow states have frequency at most `Λ / L`,
with `L` the block length that narrowness forces. -/
theorem freq_narrow_le {s : ℕ → MobState} {N : ℕ → ℕ} (hN0 : N 0 = 0) (hmono : Monotone N)
    {η Λ : ℝ} {L p : ℕ} (hnar : NarrowForcesBlock s N η L) (hL : 1 ≤ L) (hp : 0 < p)
    (hrate : (N p : ℝ) ≤ Λ * p) :
    ((((Finset.range p).filter fun n => (s n).width < η).card : ℝ)) / p ≤ Λ / L := by
  refine le_trans ?_ (freq_longBlock_le N hN0 hmono hL hp hrate)
  have hsub : ((Finset.range p).filter fun n => (s n).width < η) ⊆ longBlocks N L p := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
    exact Finset.mem_filter.2 ⟨hn1, hnar n hn2⟩
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hcard : ((((Finset.range p).filter fun n => (s n).width < η).card : ℝ))
      ≤ ((longBlocks N L p).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  gcongr

/-- **The limit.**  If the forced block length grows as the width floor shrinks, the narrow-state
frequency tends to `0` — uniformly in `p`.  This is the statement the directive asked for. -/
theorem narrow_freq_tendsto_zero {s : ℕ → MobState} {N : ℕ → ℕ}
    (hN0 : N 0 = 0) (hmono : Monotone N) {Λ : ℝ} (_hΛ : 0 ≤ Λ)
    (hrate : ∀ p, 0 < p → (N p : ℝ) ≤ Λ * p)
    {η : ℕ → ℝ} {L : ℕ → ℕ} (hL : ∀ i, 1 ≤ L i) (hLtop : Tendsto L atTop atTop)
    (hnar : ∀ i, NarrowForcesBlock s N (η i) (L i)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ p, 0 < p →
      ((((Finset.range p).filter fun n => (s n).width < η i).card : ℝ)) / p ≤ ε := by
  intro ε hε
  have hev : ∀ᶠ i in atTop, Λ / ε ≤ (L i : ℝ) := by
    obtain ⟨M, hM⟩ := exists_nat_ge (Λ / ε)
    filter_upwards [hLtop.eventually_ge_atTop M] with i hi
    exact le_trans hM (by exact_mod_cast hi)
  filter_upwards [hev] with i hi p hp
  have hLR : (0:ℝ) < L i := by exact_mod_cast hL i
  refine le_trans (freq_narrow_le hN0 hmono (hnar i) (hL i) hp (hrate p hp)) ?_
  rw [div_le_iff₀ hLR]
  rw [div_le_iff₀ hε] at hi
  linarith

section Audit

#print axioms sum_blockLength
#print axioms card_longBlock_le
#print axioms freq_longBlock_le
#print axioms freq_narrow_le
#print axioms narrow_freq_tendsto_zero

end Audit

end NormalNumbers.VandeheyS7
