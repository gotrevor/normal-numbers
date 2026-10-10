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

/-- Rational upper bound for the base-2 radius `2^(-449/100) ≈ 0.0445016`. -/
def δ2hi : ℚ := 4451 / 100000

/-- A forbidden binary word of length `L ≤ 13` with value `v`: its cylinder `[v/2ᴸ, (v+1)/2ᴸ]`
lies inside `[0, δ₂⁺)` or `(1 − δ₂⁺, 1]`, or `L = 13` and the cylinder meets one of them. -/
def Forb2 (L v : ℕ) : Prop :=
  L ≤ 13 ∧ (((v : ℚ) + 1) / 2 ^ L < δ2hi ∨ 1 - δ2hi < (v : ℚ) / 2 ^ L ∨
    (L = 13 ∧ ((v : ℚ) / 2 ^ 13 < δ2hi ∨ 1 - δ2hi < ((v : ℚ) + 1) / 2 ^ 13)))

instance (L v : ℕ) : Decidable (Forb2 L v) := by unfold Forb2; infer_instance

set_option exponentiation.threshold 1000 in
theorem two_rpow_lt : (2 : ℝ) ^ (-(449 / 100 : ℝ)) < (δ2hi : ℝ) := by
  have hx : 0 ≤ (2 : ℝ) ^ (-(449 / 100 : ℝ)) := by positivity
  have h100 : ((2 : ℝ) ^ (-(449 / 100 : ℝ))) ^ (100 : ℕ) = ((2 : ℝ) ^ (449 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (-(449 / 100 : ℝ) * ((100 : ℕ) : ℝ)) = -((449 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [← pow_lt_pow_iff_left₀ hx (by norm_num [δ2hi]) (by norm_num : (100 : ℕ) ≠ 0), h100]
  rw [show ((δ2hi : ℚ) : ℝ) = 4451 / 100000 by norm_num [δ2hi]]
  rw [inv_lt_comm₀ (by positivity) (by norm_num), ← inv_pow, inv_div]; norm_num

/-- **Base-2 containment leaves a forbidden substring.**  If the cell `[a/2ᵏ, (a+1)/2ᵏ]` lies
in a base-2 window of stage `n`, then the binary digits `n+1 … m` of `a` (as a `k`-bit word),
for some `n < m ≤ k`, form a forbidden word. -/
theorem forb2_of_window {k a n A : ℕ} (h : Count.cell k a ⊆ window 2 n A) :
    ∃ m, n < m ∧ m ≤ k ∧ Forb2 (m - n) (a / 2 ^ (k - m) % 2 ^ (m - n)) := by
  set d := (2 : ℝ) ^ (-(449 / 100 : ℝ)) with hd
  have hdlt := two_rpow_lt
  have hdpos : 0 < d := by positivity
  have hdhi : (δ2hi : ℝ) = 4451 / 100000 := by norm_num [δ2hi]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hlo : (a : ℝ) / 2 ^ k ∈ window 2 n A := h ⟨le_rfl, by gcongr; linarith⟩
  have hhi : ((a : ℝ) + 1) / 2 ^ k ∈ window 2 n A := h ⟨by gcongr; linarith, le_rfl⟩
  simp only [window, Set.mem_Icc, Nat.cast_ofNat] at hlo hhi
  rw [← hd] at hlo hhi
  -- n < k: otherwise the window is shorter than the cell
  have hnk : n < k := by
    by_contra hc
    push Not at hc
    have hpow : (2 : ℝ) ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hc
    have := sub_le_sub hhi.2 hlo.1
    have e1 : ((a : ℝ) + 1) / 2 ^ k - a / 2 ^ k = 1 / 2 ^ k := by ring
    have e2 : ((A : ℝ) + d) / 2 ^ n - (A - d) / 2 ^ n = 2 * d / 2 ^ n := by ring
    rw [e1, e2, div_le_div_iff₀ h2k h2n] at this
    nlinarith
  -- scale by 2^n: with L' = k - n, a = B 2^L' + t
  set L' := k - n with hL'
  have hk : k = n + L' := by omega
  have h2L : (0 : ℝ) < 2 ^ L' := by positivity
  set B := a / 2 ^ L' with hB
  set t := a % 2 ^ L' with ht
  have hat : (a : ℝ) = B * 2 ^ L' + t := by
    have := Nat.div_add_mod a (2 ^ L'); rw [← hB, ← ht] at this
    exact_mod_cast (by linarith [this] : (a : ℕ) = 2 ^ L' * B + t) |>.trans (by ring)
  have htlt : (t : ℝ) + 1 ≤ 2 ^ L' := by
    have : t < 2 ^ L' := Nat.mod_lt _ (by positivity)
    exact_mod_cast this
  have hscale : ∀ y : ℝ, y / 2 ^ k = (y / 2 ^ L') / 2 ^ n := by
    intro y; rw [hk, pow_add]; field_simp
  have hlo1 : (A : ℝ) - d ≤ a / 2 ^ L' := by
    have := hlo.1; rw [hscale] at this; exact (div_le_div_iff_of_pos_right h2n).1 this
  have hhi1 : ((a : ℝ) + 1) / 2 ^ L' ≤ A + d := by
    have := hhi.2; rw [hscale] at this; exact (div_le_div_iff_of_pos_right h2n).1 this
  have hlo' : (A : ℝ) - d ≤ B + t / 2 ^ L' := by
    rw [hat, show ((B : ℝ) * 2 ^ L' + t) / 2 ^ L' = B + t / 2 ^ L' by field_simp] at hlo1
    exact hlo1
  have hhi' : (B : ℝ) + (t + 1) / 2 ^ L' ≤ A + d := by
    rw [hat, show ((B : ℝ) * 2 ^ L' + t + 1) / 2 ^ L' = B + (t + 1) / 2 ^ L' by
      field_simp; ring] at hhi1
    exact hhi1
  have ht0 : (0 : ℝ) ≤ t / 2 ^ L' := by positivity
  have ht1 : (t + 1 : ℝ) / 2 ^ L' ≤ 1 := by rw [div_le_one h2L]; exact htlt
  have htpos : (0 : ℝ) < (t + 1) / 2 ^ L' := by positivity
  have hd2 : d < 1 / 4 := by linarith
  -- the two cases: inside [0,d] or inside [1-d,1]
  have hcase : (t + 1 : ℝ) / 2 ^ L' ≤ d ∨ 1 - d ≤ (t : ℝ) / 2 ^ L' := by
    rcases lt_trichotomy (A : ℤ) (B : ℤ) with hAB | hAB | hAB
    · exfalso
      have : (A : ℝ) + 1 ≤ B := by exact_mod_cast hAB
      linarith
    · left
      have : (A : ℝ) = B := by exact_mod_cast hAB
      linarith
    · right
      have h1 : (B : ℝ) + 1 ≤ A := by exact_mod_cast hAB
      by_contra hc
      push Not at hc
      have : (B : ℝ) + 2 ≤ A ∨ (A : ℝ) = B + 1 := by
        rcases Int.lt_or_eq_of_le (show (B : ℤ) + 1 ≤ A by omega) with h' | h'
        · left; exact_mod_cast (show (B : ℤ) + 2 ≤ A by omega)
        · right; exact_mod_cast h'.symm
      rcases this with h' | h' <;> linarith
  by_cases hsmall : L' ≤ 13
  · refine ⟨k, by omega, le_rfl, ?_⟩
    rw [Nat.sub_self, pow_zero, Nat.div_one, ← hL', ← ht]
    refine ⟨hsmall, ?_⟩
    rcases hcase with hc | hc
    · left
      refine (Rat.cast_lt (K := ℝ)).mp ?_; push_cast; linarith
    · right; left
      refine (Rat.cast_lt (K := ℝ)).mp ?_; push_cast; linarith
  · push Not at hsmall
    refine ⟨n + 13, by omega, by omega, ?_⟩
    rw [show n + 13 - n = 13 by omega, show k - (n + 13) = L' - 13 by omega]
    set v := a / 2 ^ (L' - 13) % 2 ^ 13 with hv
    have hv' : v = t / 2 ^ (L' - 13) := by
      rw [hv, ht, show 2 ^ L' = 2 ^ (L' - 13) * 2 ^ 13 by rw [← pow_add]; congr 1; omega,
        Nat.mod_mul_right_div_self]
    have hsplit : (2 : ℝ) ^ L' = 2 ^ (L' - 13) * 2 ^ 13 := by
      rw [← pow_add]; congr 1; omega
    have hq : (0 : ℝ) < 2 ^ (L' - 13) := by positivity
    have hvle : (v : ℝ) * 2 ^ (L' - 13) ≤ t := by
      rw [hv']; exact_mod_cast Nat.div_mul_le_self t _
    have hvge : (t : ℝ) + 1 ≤ ((v : ℝ) + 1) * 2 ^ (L' - 13) := by
      rw [hv']
      have := Nat.lt_div_mul_add (a := t) (show 0 < 2 ^ (L' - 13) by positivity)
      have : t + 1 ≤ (t / 2 ^ (L' - 13) + 1) * 2 ^ (L' - 13) := by
        rw [add_mul, one_mul]; omega
      exact_mod_cast this
    refine ⟨le_rfl, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    rcases hcase with hc | hc
    · left
      have : (v : ℝ) / 2 ^ 13 ≤ (t + 1) / 2 ^ L' := by
        rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      refine (Rat.cast_lt (K := ℝ)).mp ?_; push_cast; linarith
    · right
      have : (t : ℝ) / 2 ^ L' < ((v : ℝ) + 1) / 2 ^ 13 := by
        rw [hsplit, div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      refine (Rat.cast_lt (K := ℝ)).mp ?_; push_cast; linarith

/-- No forbidden base-2 substring among the binary digits `n+1 … m` of the `k`-bit word `a`. -/
def Acc2 (k a : ℕ) : Prop :=
  ∀ n m : ℕ, n < m → m ≤ k → ¬ Forb2 (m - n) (a / 2 ^ (k - m) % 2 ^ (m - n))

/-- **Good cells**: the finitely checkable version of `Clean449` (base 2 through forbidden
substrings). -/
def Good449 (k a : ℕ) : Prop :=
  a < 2 ^ k ∧ Acc2 k a ∧
    ∀ n A : ℕ, (3 : ℝ) ^ n ≤ 2 * δ3 * 2 ^ k → Disjoint (Count.cell k a) (window 3 n A)

theorem good449_clean {k a : ℕ} (h : Good449 k a) : Clean449 k a := by
  refine ⟨h.1, fun n A hs => ?_, h.2.2⟩
  obtain ⟨m, hnm, hmk, hf⟩ := forb2_of_window hs
  exact h.2.1 n m hnm hmk hf

/-- Staging node (gate step 1 asks for `c = 4.5` first): the same certificate at `c = 9/2`.
Evidence: sampled shared-phase growth ≈ 1.815 at D = 8 (optimistic screen); no rigorous
certificate yet (uniform bins fail, see module doc).  Confidence it holds with an adapted
partition: 45%. -/
def CoherentTwoThree45 : Prop :=
  ∃ D : ℕ, D ≤ 12 ∧ CoherentBlockCertificate (twoThreeBad (9 / 2)) D (9 / 5)

open Classical in
/-- **The crux, restated on good cells** (`Good449 → Clean449 → Alive`).  A weight function on finitely many states, vanishing
off clean cells, positive at the root, such that every clean cell's weight is beaten (by the
factor `(9/5)^D`) by its clean depth-`D` descendants.  The float certificate in the module doc
is a candidate witness (classify = (SFT state, x-bin, u-bin) of a clean cell, plus finitely many
early-level states); what remains is the exact check and the root entry. -/
def CleanCertificate449 : Prop :=
  ∃ D : ℕ, 0 < D ∧ D ≤ 12 ∧ ∃ (S : ℕ) (classify : ℕ → ℕ → Fin S) (w : Fin S → ℚ),
    (∀ s, 0 ≤ w s ∧ w s ≤ 1) ∧ 0 < w (classify 0 0) ∧
    (∀ k a, ¬ Good449 k a → w (classify k a) = 0) ∧
    ∀ k a, Good449 k a → (9 / 5 : ℚ) ^ D * w (classify k a) ≤
      ∑ j ∈ (Finset.range (2 ^ D)).filter (fun j => Good449 (k + D) (2 ^ D * a + j)),
        w (classify (k + D) (2 ^ D * a + j))

theorem coherentTwoThree449_of_clean (h : CleanCertificate449) : CoherentTwoThree449 := by
  obtain ⟨D, hD, hD12, S, classify, w, hw, hroot, hzero, hgrow⟩ := h
  exact ⟨D, hD12, coherentBlockCertificate_of_good hD (fun k a hk => clean449_alive (good449_clean hk))
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
