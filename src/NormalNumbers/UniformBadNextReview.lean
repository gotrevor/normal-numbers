/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTowerReview
import NormalNumbers.UniformBadJoint

/-!
# Next-step review: correlated phases and the binary critical boundary

These are proposal nodes, not new upper or lower bounds.  The implementation owner
chooses a lane after the feasibility gates in the mailbox review.  In particular,
the failure of RationalTower does not exclude other rational approximations.
-/

namespace NormalNumbers.UniformBadThreshold.NextReview

open NormalNumbers.UniformBad (dnear)

/-- Containment pruning at a real exponent, for the two-base model. -/
def twoThreeBad (c : ℝ) (k a : ℕ) : Prop :=
  ∃ b : ℕ, (b = 2 ∨ b = 3) ∧ ∃ n A : ℕ,
    Count.cell k a ⊆ Set.Icc
      (((A : ℝ) - (b : ℝ) ^ (-c)) / (b : ℝ) ^ n)
      (((A : ℝ) + (b : ℝ) ^ (-c)) / (b : ℝ) ^ n)

open Classical in
/-- All surviving descendants from ONE concrete parent.  Multiplicities matter:
two distinct descendants can have the same abstract state. -/
noncomputable def blockRow {S : ℕ} (Bad : ℕ → ℕ → Prop) (D : ℕ)
    (classify : ℕ → ℕ → Fin S) (k a : ℕ) : List (Fin S) :=
  ((List.range (2 ^ D)).filter fun j => Count.Alive Bad (k + D) (2 ^ D * a + j)).map
    fun j => classify (k + D) (2 ^ D * a + j)

/-- A finite certificate keeps the joint outcome of all siblings under their
shared parent phase.  This avoids minimizing each sibling's future separately.
Bounded state weights and a positive root rule out artificial growth by merely
rescaling weights at each depth.  A realization proof must cover every concrete
block, not just sampled phases. -/
def CoherentBlockCertificate (Bad : ℕ → ℕ → Prop) (D : ℕ) (growth : ℚ) : Prop :=
  0 < D ∧ ∃ (S : ℕ) (classify : ℕ → ℕ → Fin S)
    (outcomes : Fin S → Finset (List (Fin S))) (w : Fin S → ℚ),
    (∀ s, 0 ≤ w s ∧ w s ≤ 1) ∧ 0 < w (classify 0 0) ∧
    (∀ k a, Count.Alive Bad k a →
      blockRow Bad D classify k a ∈ outcomes (classify k a)) ∧
    (∀ s, ∀ row ∈ outcomes s, growth ^ D * w s ≤ (row.map w).sum)

/-- First upper-route target, not an asserted theorem: an exact joint core at
4.49 with bounded finite-state weights and block growth at least 1.8.
This still needs a quantitative interface for bases ≥5 before it bounds cStar.
The 1.8 is a probe gate, not a proved sufficient all-base budget. -/
def CoherentTwoThree449 : Prop :=
  ∃ D : ℕ, D ≤ 12 ∧ CoherentBlockCertificate (twoThreeBad (449 / 100)) D (9 / 5)

/-- The elementary inequality explaining the relaxation in abs3.js: separate
lower bounds can be summed for each common phase, but separate minimizers need
not be jointly realizable.  This alone does not measure the loss in that probe. -/
theorem common_phase_sum_bound {P : Type*} {n : ℕ}
    (lower : Fin n → ℝ) (cost : P → Fin n → ℝ)
    (h : ∀ p i, lower i ≤ cost p i) (p : P) :
    ∑ i, lower i ≤ ∑ i, cost p i :=
  Finset.sum_le_sum fun i _ => h p i

/-- Width of the critical symmetric central hole in the doubling map.
Glendinning--Sidorov, arXiv:1302.2486v2, Proposition 3.3 and §4.3.
Numerically 0.175091932719785.  This is a known binary-system constant,
not a proposed value for cStar.  Source: https://arxiv.org/pdf/1302.2486 -/
noncomputable def binaryCriticalWidth : ℝ :=
  (1 / 4 : ℝ) * ∏' n : ℕ, (1 - ((2 : ℝ) ^ (2 ^ (n + 1) : ℕ))⁻¹)

/-- Approximately 2.513815481094635, matching the reported small-base
finite-horizon plateau to its stated precision. -/
noncomputable def binaryCriticalExponent : ℝ :=
  -Real.logb 2 binaryCriticalWidth

/-- Source-check target: above the binary critical hole width, every point
whose doubling orbit stays in [δ,1-δ] is rational.  The literature's central
hole formulation must be translated and its eventual-periodicity conclusion
checked; countability by itself does not imply rationality.  This node is not
an imported literature theorem or a claimed proof. -/
def BinaryCriticalClassification : Prop :=
  ∀ δ : ℝ, binaryCriticalWidth < δ → ∀ x : ℝ,
    (∀ n : ℕ, δ ≤ dnear ((2 : ℝ) ^ n * x)) →
    ∃ q : ℚ, (q : ℝ) = x

/-- New boundary question: can finitely many other-base windows strictly
exclude the entire closed binary critical survivor set?  Such a certificate,
with compactness and strict margins, would produce a gap above the binary
threshold.  It must cover every critical survivor, not one Thue--Morse point. -/
def CriticalCoreExclusion (B N : ℕ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1,
    (∀ n : ℕ, binaryCriticalWidth ≤ dnear ((2 : ℝ) ^ n * x)) →
    ∃ b : ℕ, 3 ≤ b ∧ b ≤ B ∧ ∃ n : ℕ, n ≤ N ∧
      dnear ((b : ℝ) ^ n * x) < (b : ℝ) ^ (-binaryCriticalExponent)

/-- A distinct target for adaptive rational-anchor exclusion.  Candidate
denominators are bases, so no fixed ceiling such as 30 or 3000 is imposed.
Any success must finish as an exact finite Win certificate.  No evidence in
this review establishes this target. -/
def AdaptiveLower252 : Prop := ¬ Admissible (63 / 25)

end NormalNumbers.UniformBadThreshold.NextReview
