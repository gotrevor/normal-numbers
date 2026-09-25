/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtArchFaithful

/-!
# The dyadic-block archimedean route: its three statements are FALSE — and the repair

Laps 112-114 reduced the wide archimedean debt (`WideTwistSmall`) through three successively
"cleaner" per-block statements:

    BlockPhasePairing d  →  WideBlockPartial κ  →  WideBlockSaving κ  →  WideTwistSmall κ C

Every implication in that chain is a theorem.  **All three hypotheses are false**, so
`conjC3_of_geom_input_blocks`, `conjC3_of_geom_input_blockPartial` and
`conjC3_of_geom_input_pairing` are vacuous — exactly the lap-102 defect pattern, one level down.

## §1 the refutations

The defect is that a *constant-fraction* saving is demanded of blocks (and of initial segments of
blocks) that are too small to have any cancellation in them at all.

* `not_wideBlockPartial` — `WideBlockPartial κ` is false for every `κ > 0`.  Take `X = 3`,
  `q = 1`, `t = 2`, `j = 1`, `m = 3`: the initial segment is the **singleton** `{2}`, its sum has
  norm exactly `1`, and the demanded bound is `(1 − κ)·1 < 1`.
* `not_blockPhasePairing` — `BlockPhasePairing d` is false for every `d < 1`, at the same
  witness: an injective self-map of a singleton is the identity, so its partner separation is
  `Re(u₂ · conj u₂) = ‖u₂‖² = 1`, never `≤ d`.
* `not_wideBlockSaving` — `WideBlockSaving κ` is false for every `κ > 0`.  Here there is no
  segment parameter to abuse, so the witness is the **truncated top block**: at `X = 16/5`,
  `⌈X²⌉₊ = 11`, and the `j = 3` block of primes `< 12` is the singleton `{11}`; its weighted sum
  has norm exactly its mass `1/11`.

The first two are *segment* defects (fixable by asking for the saving on complete blocks only);
the third is structural — the top block of *any* truncation may be a singleton.

## §2-§3 the repair

`WideBlockSavingAbove J κ` asks for the saving only on blocks that are

* **complete**: `2^{j+1} ≤ ⌈X²⌉₊ + 1`, so the truncated top block is excluded, and
* **above a threshold**: `J X ≤ j`, with the threshold allowed to grow with `X`.

The threshold is necessary and cannot be a constant: a block at any *fixed* index `j` holds
finitely many primes, whose phases `t log p` can be driven simultaneously to within `ε` of each
other by a large twist `t` (Kronecker, the `log p` being `ℚ`-independent), and the wide range
allows `|t|` up to `X²`.  So the honest statement carries a threshold, and the cost of the
threshold is a *separate, purely arithmetic* obligation:

    BlockThresholdAffordable J ε C  :  ∑_{j < J X} mass_j ≤ ε · log log X + C.

`wideTwistSmall_of_blockSavingAbove` then recovers `WideTwistSmall (κ − ε) C'`: the excluded
blocks are bounded by the trivial bound `‖blockSum j‖ ≤ mass_j` (`norm_blockSum_le_mass`), the
one truncated block costs `≤ 1`, and the saving survives on the rest.

Guards (so the repair is not vacuous in either direction):
`wideBlockSavingAbove_zero` — at `κ = 0` it is trivially true, so all its content is in `κ > 0`;
`witness_block_truncated` / `witness_block_below_threshold` — the three refutations above do
**not** apply to it.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-! ## §0 the witness: `X ∈ [3,7]`, conductor `q = 1`, twist `t = 2` -/

/-- Mod `1` every Dirichlet character is identically `1`: `ZMod 1` is a subsingleton. -/
theorem dirichletChar_one_apply (χ : DirichletCharacter ℂ 1) (x : ZMod 1) : χ x = 1 := by
  have hs : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  rw [hs.elim x 1, map_one]

theorem dirichletChar_one_ne_zero (χ : DirichletCharacter ℂ 1) (x : ZMod 1) : χ x ≠ 0 := by
  rw [dirichletChar_one_apply]; exact one_ne_zero

/-- The summand of the block sums is unimodular wherever `χ` survives. -/
theorem norm_blockSummand {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ} {p : ℕ}
    (hne : χ (p : ZMod q) ≠ 0) :
    ‖(starRingEnd ℂ) (χ (p : ZMod q)) *
      Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))‖ = 1 :=
  norm_twistUnit hne

/-- For `3 ≤ X ≤ 7` the conductor `q = 1` and the twist `t = 2` are admissible in the wide
range: `1 ≤ (log X)^{1/125} < 2 ≤ X²`. -/
theorem wide_witness_admissible {X : ℝ} (hX3 : 3 ≤ X) (hX7 : X ≤ 7) :
    ((1 : ℕ) : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) ∧
      Real.log X ^ ((1 : ℝ) / 125) < |(2 : ℝ)| ∧ |(2 : ℝ)| ≤ X ^ 2 := by
  have h1 : 1 < Real.log X := one_lt_log_of_three_le hX3
  have h2 : Real.log X < 2 := by
    have h7 : (7 : ℝ) < Real.exp 2 := by
      have h := Real.exp_one_gt_d9
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    calc Real.log X ≤ Real.log 7 := Real.log_le_log (by linarith) hX7
      _ < 2 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr h7
  have habs : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have h0 : Real.log X ^ (0 : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num)
    rw [Real.rpow_zero] at h0
    push_cast
    exact h0
  · have hle : Real.log X ^ ((1 : ℝ) / 125) ≤ Real.log X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num)
    rw [Real.rpow_one] at hle
    rw [habs]
    linarith
  · rw [habs]; nlinarith

/-! ## §1 the three refutations -/

/-- At any `X ≥ 3` the initial segment `p < 3` of the `j = 1` dyadic block is the singleton
`{2}`. -/
theorem seg_one_eq_singleton {X : ℝ} (hX : 3 ≤ X) :
    (blockPrimes X 1).filter (fun p => p < 3) = {2} := by
  classical
  have h9 : (9 : ℝ) ≤ X ^ 2 := by nlinarith
  have hc : (9 : ℕ) ≤ ⌈X ^ 2⌉₊ := by
    have := Nat.le_ceil (X ^ 2)
    exact_mod_cast le_trans h9 this
  ext p
  simp only [blockPrimes, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨-, hp⟩, -⟩, h3⟩
    have := hp.two_le
    omega
  · rintro rfl
    refine ⟨⟨⟨by omega, Nat.prime_two⟩, ?_⟩, by norm_num⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

/-- **Defect (lap 113).**  `WideBlockPartial κ` is FALSE for every `κ > 0`: the initial segment
`p < 3` of the `j = 1` block is the singleton `{2}`, whose sum has norm exactly `1`, while the
statement demands `≤ (1 − κ)·1`. -/
theorem not_wideBlockPartial {κ : ℝ} (hκ : 0 < κ) : ¬ WideBlockPartial κ := by
  classical
  intro h
  obtain ⟨hq, ht1, ht2⟩ := wide_witness_admissible (le_refl (3 : ℝ)) (by norm_num)
  have hspec := h 3 le_rfl 1 (1 : DirichletCharacter ℂ 1) hq 2 ht1 ht2 1 3
  rw [seg_one_eq_singleton (le_refl (3 : ℝ)), Finset.sum_singleton,
    Finset.card_singleton] at hspec
  rw [norm_blockSummand (dirichletChar_one_ne_zero _ _)] at hspec
  norm_num at hspec
  linarith

/-- At `X = 16/5` the ceiling `⌈X²⌉₊` is `11`, so the `j = 3` block — the primes `p` with
`8 ≤ p < 16` and `p < 12` — is the singleton `{11}`.  This is the *truncated top block*: no
segment parameter is involved. -/
theorem block_three_eq_singleton : blockPrimes (16 / 5) 3 = {11} := by
  classical
  have hceil : ⌈((16 : ℝ) / 5) ^ 2⌉₊ = 11 := by
    have he : ((16 : ℝ) / 5) ^ 2 = 256 / 25 := by norm_num
    rw [he, Nat.ceil_eq_iff (by norm_num)]
    norm_num
  ext p
  simp only [blockPrimes, hceil, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hlt, hp⟩, hlog⟩
    have h8 : 2 ^ 3 ≤ p := by
      have := Nat.pow_log_le_self 2 hp.pos.ne'
      rwa [hlog] at this
    have h8' : 8 ≤ p := by norm_num at h8 ⊢; omega
    interval_cases p <;> revert hp <;> decide
  · rintro rfl
    exact ⟨⟨by norm_num, by norm_num⟩,
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)⟩

/-- **Defect (lap 112).**  `WideBlockSaving κ` is FALSE for every `κ > 0`.  Unlike lap 113's
statement there is no initial-segment parameter, so the witness is the truncated top block: at
`X = 16/5` the `j = 3` block is the singleton `{11}`, whose weighted sum has norm exactly its own
mass `1/11`.  **This defect is structural**: for any truncation point the top block can be a
singleton, so no per-block constant-fraction saving can hold at every `j`. -/
theorem not_wideBlockSaving {κ : ℝ} (hκ : 0 < κ) : ¬ WideBlockSaving κ := by
  classical
  intro h
  have hX3 : (3 : ℝ) ≤ 16 / 5 := by norm_num
  have hX7 : (16 : ℝ) / 5 ≤ 7 := by norm_num
  obtain ⟨hq, ht1, ht2⟩ := wide_witness_admissible hX3 hX7
  have hspec := h (16 / 5) hX3 1 (1 : DirichletCharacter ℂ 1) hq 2 ht1 ht2 3
  rw [dyadicPrimeBlockSum_eq, dyadicPrimeBlockMass_eq, block_three_eq_singleton,
    Finset.sum_singleton, Finset.sum_singleton] at hspec
  rw [norm_div, norm_blockSummand (dirichletChar_one_ne_zero _ _)] at hspec
  have h11 : ‖((11 : ℕ) : ℂ)‖ = (11 : ℝ) := by
    rw [Complex.norm_natCast]; norm_num
  rw [h11] at hspec
  have hinv : (((11 : ℕ) : ℝ))⁻¹ = 1 / 11 := by norm_num
  rw [hinv] at hspec
  nlinarith

/-- The `goodSeg` of the `j = 1` block at `q = 1` and `m = 3` is the singleton `{2}`: mod `1` no
prime is killed by the character. -/
theorem goodSeg_one_eq_singleton {X : ℝ} (hX : 3 ≤ X) (χ : DirichletCharacter ℂ 1) :
    goodSeg X 1 χ 1 3 = {2} := by
  classical
  have h : ((blockPrimes X 1).filter (fun p => p < 3)).filter
      (fun p : ℕ => χ ((p : ℕ) : ZMod 1) ≠ 0)
      = (blockPrimes X 1).filter (fun p => p < 3) :=
    Finset.filter_true_of_mem fun p _ => dirichletChar_one_ne_zero χ _
  rw [goodSeg, h, seg_one_eq_singleton hX]

/-- **Defect (lap 114).**  `BlockPhasePairing d` is FALSE for every `d < 1`.  On the singleton
segment `{2}` an injective self-map is forced to be the identity, and a unit vector is never
separated from itself: `Re(u₂ · conj u₂) = ‖u₂‖² = 1`.

So the "purely geometric" endpoint of the archimedean reduction assumes a false statement, and
`conjC3_of_geom_input_pairing` carries no content. -/
theorem not_blockPhasePairing {d : ℝ} (hd : d < 1) : ¬ BlockPhasePairing d := by
  classical
  intro h
  obtain ⟨hq, ht1, ht2⟩ := wide_witness_admissible (le_refl (3 : ℝ)) (by norm_num)
  obtain ⟨σ, hmaps, -, hsep⟩ := h 3 le_rfl 1 (1 : DirichletCharacter ℂ 1) hq 2 ht1 ht2 1 3
  have hgood := goodSeg_one_eq_singleton (le_refl (3 : ℝ)) (1 : DirichletCharacter ℂ 1)
  have h2 : (2 : ℕ) ∈ goodSeg 3 1 (1 : DirichletCharacter ℂ 1) 1 3 := by
    rw [hgood]; exact Finset.mem_singleton_self 2
  have hσ : σ 2 = 2 := by
    have hm := hmaps 2 h2
    rw [hgood, Finset.mem_singleton] at hm
    exact hm
  have hone := hsep 2 h2
  rw [hσ] at hone
  set u : ℂ := twistUnit (1 : DirichletCharacter ℂ 1) 2 2 with hu
  have hnu : ‖u‖ = 1 := norm_twistUnit (dirichletChar_one_ne_zero _ _)
  have hmc : (u * (starRingEnd ℂ) u).re = 1 := by
    rw [Complex.mul_conj]
    simp only [Complex.ofReal_re]
    rw [Complex.normSq_eq_norm_sq, hnu]
    norm_num
  rw [hmc] at hone
  linarith

#print axioms not_wideBlockPartial
#print axioms not_wideBlockSaving
#print axioms not_blockPhasePairing


/-! ## §2 the trivial bound, and the total block mass -/

/-- Every Dirichlet character is 1-bounded. -/
theorem dirichletChar_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖χ x‖ ≤ 1 := by
  by_cases hu : IsUnit x
  · have h := DirichletCharacter.unit_norm_eq_one χ hu.unit
    rw [IsUnit.unit_spec] at h
    exact h.le
  · rw [MulChar.map_nonunit _ hu]; simp

/-- **The trivial block bound**: no cancellation at all.  `‖blockSum j‖ ≤ blockMass j`.  This is
what makes `WideBlockSavingBand J Jtop 0` trivially true, so all the content of the repaired
statement lives in `κ > 0`. -/
theorem norm_blockSum_le_mass (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (j : ℕ) :
    ‖dyadicPrimeBlockSum X χ t j‖ ≤ dyadicPrimeBlockMass X j := by
  classical
  rw [dyadicPrimeBlockSum_eq, dyadicPrimeBlockMass_eq]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
  have hpp : Nat.Prime p := blockPrimes_prime hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hnum : ‖(starRingEnd ℂ) (χ (p : ZMod q)) *
      Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))‖ ≤ 1 := by
    rw [norm_mul, RCLike.norm_conj]
    have hexp : ‖Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))‖ = 1 := by
      have he : Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))
          = Complex.exp (((-t * Real.log p : ℝ) : ℂ) * Complex.I) := by push_cast; ring_nf
      rw [he, Complex.norm_exp_ofReal_mul_I]
    rw [hexp, mul_one]
    exact dirichletChar_norm_le_one χ _
  rw [norm_div, Complex.norm_natCast]
  rw [div_le_iff₀ hp0, inv_mul_cancel₀ hp0.ne']
  exact hnum

theorem dyadicPrimeBlockMass_nonneg (X : ℝ) (j : ℕ) : 0 ≤ dyadicPrimeBlockMass X j := by
  rw [dyadicPrimeBlockMass_eq]
  exact Finset.sum_nonneg fun p _ => by positivity

/-- The total dyadic block mass is the prime mass of `⌈X²⌉₊`, hence `log log X + O(1)`. -/
theorem sum_blockMass_le {X : ℝ} (hX : 3 ≤ X) :
    ∑ j ∈ Finset.range (⌈X ^ 2⌉₊ + 1), dyadicPrimeBlockMass X j
      ≤ Real.log (Real.log X) + (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound) := by
  classical
  rw [sum_blockMass_eq]
  have hB : 2 ≤ ⌈X ^ 2⌉₊ := by
    have h2 : X ^ 2 ≤ ((⌈X ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have : (2 : ℝ) ≤ ((⌈X ^ 2⌉₊ : ℕ) : ℝ) := by nlinarith
    exact_mod_cast this
  have hmass : ∑ p ∈ (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime, ((p : ℝ))⁻¹
      ≤ Real.log (Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ)) + Erdos67b.PrimeEstimates.mertensBound := by
    refine small_prime_mass_le hB (fun p hp => ?_)
    refine ⟨(Finset.mem_filter.mp hp).2, ?_⟩
    have := (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    omega
  have := logloglog_ceil_sq_le hX
  linarith

/-! ## §3 the repair: a banded saving with a named threshold cost -/

/-- **The repaired block debt.**  A constant-fraction saving on each dyadic block in a *band*
`J X ≤ j ≤ Jtop X`.

Both ends of the band are forced by §1.  The **top** end excludes the truncated block, whose
singleton witness refutes `WideBlockSaving` outright.  The **bottom** end excludes the small
blocks, and it cannot be a constant: a block at any fixed index holds finitely many primes, whose
phases `t log p` can be driven simultaneously into an arbitrarily small arc by a large twist `t`
(the `log p` are `ℚ`-independent, so Kronecker applies), and the wide range permits `|t| ≤ X²`.
So `J` is a *function of `X`*, and the mass it discards is a separate obligation,
`BlockBandCost`. -/
def WideBlockSavingBand (J Jtop : ℝ → ℕ) (κ : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
    (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) →
    ∀ t : ℝ, Real.log X ^ ((1 : ℝ) / 125) < |t| → |t| ≤ X ^ 2 → ∀ j : ℕ,
      J X ≤ j → j ≤ Jtop X →
      ‖dyadicPrimeBlockSum X χ t j‖ ≤ (1 - κ) * dyadicPrimeBlockMass X j

/-- **The cost of the band.**  The reciprocal mass discarded outside the band must be a small
fraction of the total.  This is a purely arithmetic statement: no characters, no twists, no
cancellation — only Mertens for the blocks below `J X` and a Chebyshev-free count for the blocks
above `Jtop X`. -/
def BlockBandCost (J Jtop : ℝ → ℕ) (ε C : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X →
    ∑ j ∈ (Finset.range (⌈X ^ 2⌉₊ + 1)).filter (fun j => j < J X ∨ Jtop X < j),
      dyadicPrimeBlockMass X j ≤ ε * Real.log (Real.log X) + C

/-- **The repaired reduction.**  A banded saving `κ` plus a band cost `ε` gives the wide twist
bound with saving `κ − ε`.  Outside the band the trivial bound `norm_blockSum_le_mass` is used;
inside it the hypothesis; and the two are added. -/
theorem wideTwistSmall_of_blockSavingBand {J Jtop : ℝ → ℕ} {κ ε C : ℝ}
    (hκ1 : κ ≤ 1) (hcost : BlockBandCost J Jtop ε C) (h : WideBlockSavingBand J Jtop κ) :
    WideTwistSmall (κ - ε)
      (C + (1 - κ) * (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound)) := by
  classical
  intro X hX q χ hqX t hwide ht
  have hκ0 : (0 : ℝ) ≤ 1 - κ := by linarith
  set n : ℕ := ⌈X ^ 2⌉₊ + 1 with hn
  set P : ℕ → Prop := fun j => j < J X ∨ Jtop X < j with hP
  -- the two pieces
  have hbad : ∑ j ∈ (Finset.range n).filter P, ‖dyadicPrimeBlockSum X χ t j‖
      ≤ ε * Real.log (Real.log X) + C := by
    refine le_trans (Finset.sum_le_sum fun j _ => norm_blockSum_le_mass X χ t j) ?_
    exact hcost X hX
  have hgood : ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
        ‖dyadicPrimeBlockSum X χ t j‖
      ≤ (1 - κ) * (Real.log (Real.log X)
          + (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound)) := by
    have hstep : ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
          ‖dyadicPrimeBlockSum X χ t j‖
        ≤ ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
            (1 - κ) * dyadicPrimeBlockMass X j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hnp : ¬ P j := (Finset.mem_filter.mp hj).2
      rw [hP] at hnp
      push_neg at hnp
      exact h X hX q χ hqX t hwide ht j hnp.1 hnp.2
    have hsub : ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
          (1 - κ) * dyadicPrimeBlockMass X j
        ≤ ∑ j ∈ Finset.range n, (1 - κ) * dyadicPrimeBlockMass X j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro j _ _
      exact mul_nonneg hκ0 (dyadicPrimeBlockMass_nonneg X j)
    have htot : ∑ j ∈ Finset.range n, (1 - κ) * dyadicPrimeBlockMass X j
        ≤ (1 - κ) * (Real.log (Real.log X)
            + (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_blockMass_le hX) hκ0
    linarith
  calc ‖twistedPrimeSum X χ t‖
      = ‖∑ j ∈ Finset.range n, dyadicPrimeBlockSum X χ t j‖ := by
        rw [twistedPrimeSum_eq_sum_blocks]
    _ ≤ ∑ j ∈ Finset.range n, ‖dyadicPrimeBlockSum X χ t j‖ := norm_sum_le _ _
    _ = ∑ j ∈ (Finset.range n).filter P, ‖dyadicPrimeBlockSum X χ t j‖
          + ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
              ‖dyadicPrimeBlockSum X χ t j‖ :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ (ε * Real.log (Real.log X) + C)
          + (1 - κ) * (Real.log (Real.log X)
              + (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound)) := by
        exact add_le_add hbad hgood
    _ = (1 - (κ - ε)) * Real.log (Real.log X)
          + (C + (1 - κ) * (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound)) := by ring

/-! ## §4 the guards: the repair is neither trivially true nor refuted by §1 -/

/-- Guard (not trivially true).  At `κ = 0` the banded statement is exactly the trivial bound, so
every bit of its content is the positivity of `κ`. -/
theorem wideBlockSavingBand_zero (J Jtop : ℝ → ℕ) : WideBlockSavingBand J Jtop 0 := by
  intro X _ q χ _ t _ _ j _ _
  simpa using norm_blockSum_le_mass X χ t j

/-- The intended top of the band, `Jtop X = log₂⌈X²⌉₊ − 1`, consists of **complete** blocks:
`2^{j+1} ≤ ⌈X²⌉₊`, so the truncated block that refutes `WideBlockSaving` is excluded. -/
theorem band_block_complete {X : ℝ} (hX : 3 ≤ X) {j : ℕ}
    (hj : j ≤ Nat.log 2 (⌈X ^ 2⌉₊) - 1) : 2 ^ (j + 1) ≤ ⌈X ^ 2⌉₊ := by
  have h9 : (9 : ℝ) ≤ X ^ 2 := by nlinarith
  have hc : (9 : ℕ) ≤ ⌈X ^ 2⌉₊ := by
    have := Nat.le_ceil (X ^ 2)
    exact_mod_cast le_trans h9 this
  have hne : ⌈X ^ 2⌉₊ ≠ 0 := by omega
  have hlog3 : 3 ≤ Nat.log 2 (⌈X ^ 2⌉₊) := by
    have := Nat.log_mono_right (b := 2) hc
    have h8 : Nat.log 2 9 = 3 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    omega
  have hj' : j + 1 ≤ Nat.log 2 (⌈X ^ 2⌉₊) := by omega
  calc 2 ^ (j + 1) ≤ 2 ^ Nat.log 2 (⌈X ^ 2⌉₊) := Nat.pow_le_pow_right (by norm_num) hj'
    _ ≤ ⌈X ^ 2⌉₊ := Nat.pow_log_le_self 2 hne

/-- Guard (the §1 witnesses are excluded).  The `X = 16/5` witness block `j = 3` that refutes
`WideBlockSaving` lies **above** the intended top of the band. -/
theorem witness_block_above_band : Nat.log 2 (⌈((16 : ℝ) / 5) ^ 2⌉₊) - 1 < 3 := by
  have hceil : ⌈((16 : ℝ) / 5) ^ 2⌉₊ = 11 := by
    have he : ((16 : ℝ) / 5) ^ 2 = 256 / 25 := by norm_num
    rw [he, Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [hceil]
  have h11 : Nat.log 2 11 = 3 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  omega

/-- Guard (the §1 witnesses are excluded).  The `j = 1` witness that refutes `WideBlockPartial`
and `BlockPhasePairing` lies **below** the bottom of the band for any threshold `2 ≤ J X`. -/
theorem witness_block_below_band {J : ℝ → ℕ} {X : ℝ} (hJ : 2 ≤ J X) : ¬ (J X ≤ 1) := by omega

/-! ## §5 the repaired headline -/

/-- **`ConjC3` on the banded block debt.**  The archimedean side, restated so that it is not
refuted: `UniformResonantMass` (the `q = 1` narrow corner), `CharPrimeSumLogQ` (a `log`-sized
conductor bound, classical and Siegel-free at `t = 0`), a constant-fraction saving on the dyadic
blocks of a band `[J X, Jtop X]`, and the arithmetic affordability of that band. -/
theorem conjC3_of_geom_input_band {c₀ θ D κ₁ ε C₁ : ℝ} (J Jtop : ℝ → ℕ)
    (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ A : ℝ, 0 < A → ∀ b : ℕ, 3 ≤ b → ∀ K,
      KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K)
    (hURM : UniformResonantMass)
    (hD : 0 < D) (hD125 : 2 * D < 125) (hlog : CharPrimeSumLogQ D)
    (hκ₁1 : κ₁ ≤ 1) (_hε : 0 ≤ ε) (hκε : ε < κ₁) (hC₁ : 0 ≤ C₁)
    (hcost : BlockBandCost J Jtop ε C₁) (hblk : WideBlockSavingBand J Jtop κ₁) :
    ConjC3 := by
  have hnp : NonPrincipalTwistSmall (1 - 2 * D / 125) (D * (2 * Real.log 3 + 1)) :=
    nonPrincipalTwistSmall_of_logQBound hD hD125 hlog
  have hwide := wideTwistSmall_of_blockSavingBand hκ₁1 hcost hblk
  have hsav := twistedPrimeSumSmall_of_parts hnp hwide
  have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hmert : (0 : ℝ) ≤ Erdos67b.PrimeEstimates.mertensBound :=
    Erdos67b.PrimeEstimates.mertensBound_nonneg
  have hκ0 : 0 < min (1 - 2 * D / 125) (κ₁ - ε) := lt_min (by linarith) (by linarith)
  have hC0 : (0 : ℝ) ≤ max (D * (2 * Real.log 3 + 1))
      (C₁ + (1 - κ₁) * (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound)) := by
    refine le_trans ?_ (le_max_left _ _)
    positivity
  refine conjC3_of_weylLambertTwist fun b hb => ?_
  obtain ⟨C, hC⟩ := faithfulArchLower_of_urm_of_saving (by omega : 2 ≤ b) hURM hκ0 hC0 hsav
  exact weylLambertTwist_of_geom_input_at hb hc₀ hθ0 hθ m
    (hin _ (Real.exp_pos _) b hb) (archSupply_of_faithfulArchLower hC)

#print axioms norm_blockSum_le_mass
#print axioms wideTwistSmall_of_blockSavingBand
#print axioms band_block_complete
#print axioms conjC3_of_geom_input_band

end CastingOut

end NormalNumbers
