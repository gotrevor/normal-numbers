/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadNextReview

/-!
# Operator gate 4: a shared-phase {2,3} core at exponent 4.49

**Frozen target** (Ren, operator, 2026-10-10): `coherentTwoThree449`, i.e. the review node
`NextReview.CoherentTwoThree449`.  Do not weaken or restate it.  If it is false, prove
`¬ NextReview.CoherentTwoThree449` (or the measured obstruction) in a separate declaration,
leave the frozen `sorry` in place and write `ON-LINE-REQUEST.md`; the operator retires it.

## The lever

`scripts/cstar_models/abs3.js` sums over the binary children of a cell, and each child
minimizes over its own target phase bin: `Σ_child inf_phase`.  A real parent has ONE phase,
shared by every descendant, so the true block value is `inf_phase Σ_child`.
`NextReview.common_phase_sum_bound` is the elementary inequality between the two; it says
nothing about the size of the gap.  `CoherentBlockCertificate` keeps the joint row of all
surviving descendants of one concrete parent over a block of `D` levels.

## Measure first (the number to reach)

An exact block certificate with per-level growth `≥ 9/5`, a positive root weight and
weights in `[0, 1]`, first at `c = 4.5` and then at `c = 449/100`.  Use the existing
`c = 4.5` SFT (`scripts/cstar_models/sft45.json`, binary rate ≈ 1.890252) and blocks
`D = 2, 4, 8` (cap 12).  Partition the parent cells along the actual transition and window
boundaries, not along a uniform grid.  Report the smallest positive weight and the
weight-aware tail charges, then feed those charges into the base `≥ 5` engine and require a
positive margin, including a rigorous infinite-base tail.

## Controls (each must pass before a number is believed)

* base 3 disabled recovers the binary rate 1.890252;
* a singleton phase set makes the shared and separate minimizations equal;
* below `log₂ 3` the binary tree dies;
* sampled phases are an OPTIMISTIC screen only: a sampled minimum is `≥` the true infimum.

## Kill test

If the shared-phase minimum is ≈ the separate minimum on the reachable states, the lever is
irrelevant for that finite model.  That is a screening failure, NOT a proof of
`¬ CoherentTwoThree449`, which quantifies over all classifiers, weights, outcomes and `D ≤ 12`
(Codex review, 2026-10-10).  State it in Lean as the actual finite model, the tested states and
phases, and an exact rational tolerance (or as a named conjecture `Prop`), add a Maze row, and
stop.  The `c = 4.49` run needs a binary model rebuilt at 4.49 (or proved stronger than
`sft45.json`), since the binary forbidden radius grows as `c` decreases.

## Measurement, lap 1 (2026-10-10; `scripts/cstar_models/shared3*.{js,c}`, `shared3_results.txt`)

Controls pass (`shared3_controls.txt`).  **Kill test does not fire:** on the same samples the
separate minimization dies (D = 2) or collapses (D = 4: growth 0.96, root 0), while the shared
one grows 1.58 (D=2), 1.76 (D=4), 1.83 (D=6), 1.82 (D=8, N=32, K=12x6).  Sampled growth at D=8
decreases slowly with K (1.832, 1.821, 1.818, 1.815 for K = 6..48): a thin margin over 1.8, and
the c = 4.49 numbers match (1.820 at N=32, 1.840 at N=64).
**Obstruction for uniform bins:** interval value iteration and branch-and-bound of the sampled
weights both fail, because a uniform bin can contain a closed-touching point (e.g. x = 0, u = 1
for the root state) where the whole block dies, so the bin infimum is 0.  A certificate must use
a partition refined along the touching boundaries (`CoherentTwoThree45` below is the c = 4.5
staging node).

## Lap 2-3 (2026-10-10): float certificates in the containment model

With pruning matched to `twoThreeBad` (containment; partial overlaps carry forbidden end-zones,
zone-carrying block leaves are killed, so the model's alive cells are genuinely alive) and the
binary automaton rebuilt per exponent (`gen_sft.js`), the target-driven fixed point
(`exactinf3.c`, interval branch-and-bound over each whole bin, no sampling) certifies growth
`9/5` at `D = 6`: c = 4.5 with `N = 128, M = 12/24` and `N = 256, M = 12`; **c = 4.49 with
`N = 128, M = 24`**.  Floating point, abstract bins (not yet the concrete root cell); the
realization obligation is reduced by `coherentBlockCertificate_of_weights`.

## Forbidden

Retuning local charges without the shared-phase change, and another blind base sweep.
-/

namespace NormalNumbers.UniformBadThreshold.Coherent

open NextReview

/-- **Outcome bookkeeping is free.**  A certificate only needs the weight inequality along the
realized rows: the outcome set of a state can be taken to be the (finite) set of rows of
bounded length that satisfy the inequality.  So the realization obligation of
`CoherentBlockCertificate` is exactly: for every alive cell,
`growth ^ D * w (classify k a) ≤ Σ` over its alive depth-`D` descendants. -/
theorem coherentBlockCertificate_of_weights {Bad : ℕ → ℕ → Prop} {D : ℕ} {growth : ℚ}
    (hD : 0 < D) (S : ℕ) (classify : ℕ → ℕ → Fin S) (w : Fin S → ℚ)
    (hw : ∀ s, 0 ≤ w s ∧ w s ≤ 1) (hroot : 0 < w (classify 0 0))
    (hgrow : ∀ k a, Count.Alive Bad k a →
      growth ^ D * w (classify k a) ≤ ((blockRow Bad D classify k a).map w).sum) :
    CoherentBlockCertificate Bad D growth := by
  classical
  have hfin : ∀ s : Fin S, {row : List (Fin S) | row.length ≤ 2 ^ D ∧
      growth ^ D * w s ≤ (row.map w).sum}.Finite := fun s =>
    (List.finite_length_le (α := Fin S) (n := 2 ^ D)).subset fun row h => h.1
  refine ⟨hD, S, classify, fun s => (hfin s).toFinset, w, hw, hroot, ?_, ?_⟩
  · intro k a ha
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, hgrow k a ha⟩
    unfold blockRow
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  · intro s row hrow
    rw [Set.Finite.mem_toFinset] at hrow
    exact hrow.2

theorem list_range_filter_map_sum (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℚ) :
    (((List.range n).filter (fun j => decide (p j))).map f).sum =
      ∑ j ∈ (Finset.range n).filter p, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_filter, Finset.sum_filter, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

open Classical in
/-- **Good-cell reduction.**  If a predicate `Good` implies `Alive`, the weights vanish off `Good`,
and every good cell's weight is beaten by its good depth-`D` descendants, then the certificate
holds.  (Alive non-good descendants only add nonnegative weight.) -/
theorem coherentBlockCertificate_of_good {Bad Good : ℕ → ℕ → Prop} {D : ℕ} {growth : ℚ}
    (hD : 0 < D) (hgood : ∀ k a, Good k a → Count.Alive Bad k a)
    (S : ℕ) (classify : ℕ → ℕ → Fin S) (w : Fin S → ℚ)
    (hw : ∀ s, 0 ≤ w s ∧ w s ≤ 1) (hroot : 0 < w (classify 0 0)) (hg : 0 ≤ growth)
    (hzero : ∀ k a, ¬ Good k a → w (classify k a) = 0)
    (hgrow : ∀ k a, Good k a → growth ^ D * w (classify k a) ≤
      ∑ j ∈ (Finset.range (2 ^ D)).filter (fun j => Good (k + D) (2 ^ D * a + j)),
        w (classify (k + D) (2 ^ D * a + j))) :
    CoherentBlockCertificate Bad D growth := by
  classical
  refine coherentBlockCertificate_of_weights hD S classify w hw hroot fun k a _ => ?_
  have hrow : ((blockRow Bad D classify k a).map w).sum =
      ∑ j ∈ (Finset.range (2 ^ D)).filter (fun j => Count.Alive Bad (k + D) (2 ^ D * a + j)),
        w (classify (k + D) (2 ^ D * a + j)) := by
    unfold blockRow
    rw [List.map_map]
    exact list_range_filter_map_sum _ _ (fun j => w (classify (k + D) (2 ^ D * a + j)))
  by_cases hk : Good k a
  · refine (hgrow k a hk).trans ?_
    rw [hrow]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.monotone_filter_right _ fun j _ hj => hgood _ _ hj)
      (fun j _ _ => (hw _).1)
  · rw [hzero k a hk, mul_zero, hrow]
    exact Finset.sum_nonneg fun j _ => (hw _).1

/-- Containment pruning is inherited by children, so a cell that is not `Bad` and lies in
`[0,1]` is alive (its ancestors contain it and so are not `Bad` either). -/
theorem alive_of_not_bad {Bad : ℕ → ℕ → Prop} (hB : ∀ k a, Bad k (a / 2) → Bad (k + 1) a) :
    ∀ k a, a < 2 ^ k → ¬ Bad k a → Count.Alive Bad k a
  | 0, a, ha, _ => by simp only [Count.Alive]; simpa using ha
  | k + 1, a, ha, hb => by
    refine ⟨alive_of_not_bad hB k (a / 2) ?_ fun h => hb (hB k a h), hb⟩
    rw [pow_succ] at ha; omega

theorem twoThreeBad_succ (c : ℝ) (k a : ℕ) (h : twoThreeBad c k (a / 2)) :
    twoThreeBad c (k + 1) a := by
  obtain ⟨b, hb, n, A, hs⟩ := h
  exact ⟨b, hb, n, A, (Count.cell_succ_sub k a).trans hs⟩

/-- The base-3 radius at the frozen exponent. -/
noncomputable def δ3 : ℝ := (3 : ℝ) ^ (-(449 / 100 : ℝ))

/-- The window of `twoThreeBad` for base `b`, stage `n`, centre `A`. -/
noncomputable def window (b n A : ℕ) : Set ℝ :=
  Set.Icc (((A : ℝ) - (b : ℝ) ^ (-(449 / 100 : ℝ))) / (b : ℝ) ^ n)
    (((A : ℝ) + (b : ℝ) ^ (-(449 / 100 : ℝ))) / (b : ℝ) ^ n)

/-- **Clean cells** (the certificate's live states): inside `[0,1]`, inside no base-2 window,
and disjoint from every base-3 window of an already *resolved* stage (`3ⁿ ≤ 2δ₃2ᵏ`, i.e. the
window is at least as long as the cell).  Whether a descendant is clean is a pure interval
disjointness question about its position `frac(3ⁿ a / 2ᵏ)` at the new stages. -/
def Clean449 (k a : ℕ) : Prop :=
  a < 2 ^ k ∧ (∀ n A : ℕ, ¬ Count.cell k a ⊆ window 2 n A) ∧
    ∀ n A : ℕ, (3 : ℝ) ^ n ≤ 2 * δ3 * 2 ^ k → Disjoint (Count.cell k a) (window 3 n A)

theorem clean449_not_bad {k a : ℕ} (h : Clean449 k a) : ¬ twoThreeBad (449 / 100) k a := by
  rintro ⟨b, hb, n, A, hs⟩
  rcases hb with rfl | rfl
  · exact h.2.1 n A (by simpa [window] using hs)
  · have hs' : Count.cell k a ⊆ window 3 n A := by simpa [window] using hs
    have hne : (Count.cell k a).Nonempty := ⟨(a : ℝ) / 2 ^ k, by
      refine ⟨le_rfl, ?_⟩; gcongr; linarith⟩
    by_cases hr : (3 : ℝ) ^ n ≤ 2 * δ3 * 2 ^ k
    · obtain ⟨x, hx⟩ := hne
      exact Set.disjoint_left.1 (h.2.2 n A hr) hx (hs' hx)
    · -- the window is shorter than the cell
      push_neg at hr
      have h1 : (a : ℝ) / 2 ^ k ∈ window 3 n A := hs' ⟨le_rfl, by gcongr; linarith⟩
      have h2 : ((a : ℝ) + 1) / 2 ^ k ∈ window 3 n A := hs' ⟨by gcongr; linarith, le_rfl⟩
      simp only [window, Set.mem_Icc] at h1 h2
      have h3p : (0 : ℝ) < 3 ^ n := by positivity
      have h2p : (0 : ℝ) < 2 ^ k := by positivity
      have hlen : ((a : ℝ) + 1) / 2 ^ k - a / 2 ^ k ≤ 2 * δ3 / 3 ^ n := by
        have := sub_le_sub h2.2 h1.1
        simp only [δ3]; push_cast at this ⊢
        calc _ ≤ _ := this
          _ = _ := by ring
      have e : ((a : ℝ) + 1) / 2 ^ k - a / 2 ^ k = 1 / 2 ^ k := by ring
      rw [e, div_le_div_iff₀ h2p h3p] at hlen
      linarith

theorem clean449_alive {k a : ℕ} (h : Clean449 k a) : Count.Alive (twoThreeBad (449 / 100)) k a :=
  alive_of_not_bad (twoThreeBad_succ _) k a h.1 (clean449_not_bad h)

/-- Staging node (gate step 1 asks for `c = 4.5` first): the same certificate at `c = 9/2`.
Evidence: sampled shared-phase growth ≈ 1.815 at D = 8 (optimistic screen); no rigorous
certificate yet (uniform bins fail, see module doc).  Confidence it holds with an adapted
partition: 45%. -/
def CoherentTwoThree45 : Prop :=
  ∃ D : ℕ, D ≤ 12 ∧ CoherentBlockCertificate (twoThreeBad (9 / 2)) D (9 / 5)

open Classical in
/-- **The crux, restated on clean cells.**  A weight function on finitely many states, vanishing
off clean cells, positive at the root, such that every clean cell's weight is beaten (by the
factor `(9/5)^D`) by its clean depth-`D` descendants.  The float certificate in the module doc
is a candidate witness (classify = (SFT state, x-bin, u-bin) of a clean cell, plus finitely many
early-level states); what remains is the exact check and the root entry. -/
def CleanCertificate449 : Prop :=
  ∃ D : ℕ, 0 < D ∧ D ≤ 12 ∧ ∃ (S : ℕ) (classify : ℕ → ℕ → Fin S) (w : Fin S → ℚ),
    (∀ s, 0 ≤ w s ∧ w s ≤ 1) ∧ 0 < w (classify 0 0) ∧
    (∀ k a, ¬ Clean449 k a → w (classify k a) = 0) ∧
    ∀ k a, Clean449 k a → (9 / 5 : ℚ) ^ D * w (classify k a) ≤
      ∑ j ∈ (Finset.range (2 ^ D)).filter (fun j => Clean449 (k + D) (2 ^ D * a + j)),
        w (classify (k + D) (2 ^ D * a + j))

theorem coherentTwoThree449_of_clean (h : CleanCertificate449) : CoherentTwoThree449 := by
  obtain ⟨D, hD, hD12, S, classify, w, hw, hroot, hzero, hgrow⟩ := h
  exact ⟨D, hD12, coherentBlockCertificate_of_good hD (fun k a hk => clean449_alive hk)
    S classify w hw hroot (by norm_num) hzero (by convert hgrow)⟩

/-- **Crux (open).**  Evidence: float certificates at growth 9/5 (module doc, lap 2-3).
Confidence 50%: the model-level margin is real, but the exact check, the early-level entry
states and the clean-cell semantics of the bins are not yet machine-checked. -/
theorem cleanCertificate449 : CleanCertificate449 := by
  sorry

/-- **Operator gate 4.**  A shared-phase finite-state certificate for the {2,3} core at
exponent 449/100, with block growth at least 9/5 over some block length `D ≤ 12`. -/
theorem coherentTwoThree449 : CoherentTwoThree449 :=
  coherentTwoThree449_of_clean cleanCertificate449

end NormalNumbers.UniformBadThreshold.Coherent
