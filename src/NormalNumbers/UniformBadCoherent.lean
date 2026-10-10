/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadNextReview
import CertData.Gate4
import CertData.Gate4Check0
import CertData.Gate4Check1
import CertData.Gate4Check2
import CertData.Gate4Check3
import CertData.Gate4Check4
import CertData.Gate4Check5
import CertData.Gate4Check6
import CertData.Gate4Check7


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

## Lap 4 (2026-10-10): EXACT integer certificate in the Good449 semantics

`scripts/cstar_models/exact3.c` re-runs the target-driven fixed point in exact fixed-point
integer arithmetic (denominator `2^90`), with a rational enclosure of `δ₃` (checked exactly:
`dlo^100·3^449 < 2^9000 < dhi^100·3^449`), dyadic `ρ = 3ⁿ/2ᵏ` bin edges, closed windows and
strict zones (a leaf that may touch a window dies), and min-over-both-interpretations where
the resolution `ρ/2 ≤ 2δ₃` is ambiguous.  The binary SFT equals the minimal forbidden words of
`Forb2` exactly (`forb2_check.js`).  Result: **exact certificate at growth 9/5, c = 449/100,
D = 6, N = 128, M = 24** (74431/76800 positive bins, 73 s); control growth 37/20 decays.  Root
entry weight 1 (`entry_exact.py`).

## Lap 5 (2026-10-10): PROVED in Lean

The checker is re-implemented in `CertData.Gate4` (precompiled, pure `Int`), proved sound
here (`go_sound`, `bb_sound`, `grow_good`, `rootSum_le`, `cleanCertificate449_of_data`), and run
by `native_decide` over all 76800 bins (`CertData.Gate4Check0..7`, about 3 minutes in parallel).
`cleanCertificate449`, hence `coherentTwoThree449`, is a theorem; its axioms are the standard
three plus the `native_decide` certificates.

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

/-- **Acc2 is a suffix automaton condition**: appending a bit only adds the new suffixes. -/
theorem acc2_succ (k a d : ℕ) (hd : d < 2) :
    Acc2 (k + 1) (2 * a + d) ↔
      Acc2 k a ∧ ∀ L, 0 < L → L ≤ k + 1 → ¬ Forb2 L ((2 * a + d) % 2 ^ L) := by
  have hdiv : ∀ j, (2 * a + d) / 2 ^ (j + 1) = a / 2 ^ j := by
    intro j; rw [pow_succ', ← Nat.div_div_eq_div_mul]; congr 1; omega
  constructor
  · intro h
    refine ⟨fun n m hnm hmk => ?_, fun L hL hLk => ?_⟩
    · have := h n m hnm (by omega)
      rwa [show k + 1 - m = (k - m) + 1 by omega, hdiv] at this
    · have := h (k + 1 - L) (k + 1) (by omega) le_rfl
      rwa [Nat.sub_self, pow_zero, Nat.div_one, show k + 1 - (k + 1 - L) = L by omega] at this
  · rintro ⟨h1, h2⟩ n m hnm hmk
    rcases Nat.lt_or_ge m (k + 1) with hm | hm
    · rw [show k + 1 - m = (k - m) + 1 by omega, hdiv]
      exact h1 n m hnm (by omega)
    · obtain rfl : m = k + 1 := by omega
      rw [Nat.sub_self, pow_zero, Nat.div_one]
      exact h2 _ (by omega) (by omega)

/-- The 25-state binary automaton `sft449` (`scripts/cstar_models/sft449.h`); `99` = dead. -/
def sftT : List (ℕ × ℕ) :=
  [(1,13),(2,13),(3,13),(4,13),(99,5),(6,14),(99,7),(99,8),(9,15),(99,10),(99,11),(12,15),(99,13),
   (1,14),(1,15),(1,16),(17,99),(2,18),(19,99),(20,99),(3,21),(22,99),(23,99),(3,24),(1,99)]

def sftStep (s d : ℕ) : ℕ :=
  match sftT[s]? with
  | some p => if d = 0 then p.1 else p.2
  | none => 99

/-- The automaton state after reading the `k`-bit word `a` (most significant bit first). -/
def sftRun : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a => let s := sftRun k (a / 2); if s = 99 then 99 else sftStep s (a % 2)

/-- Reachable (state, suffix length ≤ 12, suffix) triples, by iterated closure from the start. -/
def reachStep (l : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  (l ++ l.flatMap fun (p : ℕ × ℕ × ℕ) => [0, 1].filterMap fun d =>
    let t := sftStep p.1 d
    if t = 99 then none else some (t, min (p.2.1 + 1) 12, (2 * p.2.2 + d) % 2 ^ min (p.2.1 + 1) 12)).dedup

def sftReach : List (ℕ × ℕ × ℕ) := (reachStep)^[20] [(0, 0, 0)]

/-- Closure and safety of `sftReach`, checked by evaluation. -/
def sftReachOK : Bool :=
  sftReach.all fun (p : ℕ × ℕ × ℕ) => [0, 1].all fun d =>
    let t := sftStep p.1 d
    t = 99 || (sftReach.contains (t, min (p.2.1 + 1) 12, (2 * p.2.2 + d) % 2 ^ min (p.2.1 + 1) 12) &&
      (List.range (min (p.2.1 + 1) 13 + 1)).all fun L =>
        L = 0 || !decide (Forb2 L ((2 * p.2.2 + d) % 2 ^ L)))

theorem sftReachOK_true : sftReachOK = true := by native_decide


theorem sftReach_closed {p : ℕ × ℕ × ℕ} (hp : p ∈ sftReach) {d : ℕ} (hd : d < 2)
    (ht : sftStep p.1 d ≠ 99) :
    (sftStep p.1 d, min (p.2.1 + 1) 12, (2 * p.2.2 + d) % 2 ^ min (p.2.1 + 1) 12) ∈ sftReach ∧
      ∀ L, 0 < L → L ≤ min (p.2.1 + 1) 13 → ¬ Forb2 L ((2 * p.2.2 + d) % 2 ^ L) := by
  have h := sftReachOK_true
  simp only [sftReachOK, List.all_eq_true] at h
  have h2 := h p hp d (by interval_cases d <;> simp)
  simp only [Bool.or_eq_true, decide_eq_true_eq, ht, false_or, Bool.and_eq_true,
    List.contains_iff_mem, List.all_eq_true, List.mem_range] at h2
  refine ⟨h2.1, fun L hL hLe => ?_⟩
  have := h2.2 L (by omega)
  simpa [show L ≠ 0 by omega] using this

theorem two_mul_mod_add_mod (x m d j : ℕ) (hj : j ≤ m + 1) :
    (2 * (x % 2 ^ m) + d) % 2 ^ j = (2 * x + d) % 2 ^ j := by
  have hdvd : 2 ^ j ∣ 2 ^ (m + 1) := pow_dvd_pow 2 hj
  obtain ⟨c, hc⟩ := hdvd
  have e : 2 * x + d = 2 * (x % 2 ^ m) + d + 2 ^ j * (c * (x / 2 ^ m)) := by
    have := Nat.mod_add_div x (2 ^ m)
    rw [← mul_assoc, ← hc, pow_succ]; nlinarith
  rw [e, Nat.add_mul_mod_self_left]

/-- **SFT soundness**: a word the automaton `sft449` accepts has no forbidden `Forb2` substring. -/
theorem acc2_of_sftRun : ∀ k a, sftRun k a ≠ 99 →
    (sftRun k a, min k 12, a % 2 ^ min k 12) ∈ sftReach ∧ Acc2 k a
  | 0, a, _ => by
    refine ⟨by rw [show (sftRun 0 a, min 0 12, a % 2 ^ min 0 12) = (0, 0, 0) by simp [sftRun, Nat.mod_one]]; native_decide, fun n m hnm hmk => by omega⟩
  | k + 1, a, h => by
    have hs : sftRun k (a / 2) ≠ 99 := fun h' => h (by simp [sftRun, h'])
    obtain ⟨hr, hacc⟩ := acc2_of_sftRun k (a / 2) hs
    have hrun : sftRun (k + 1) a = sftStep (sftRun k (a / 2)) (a % 2) := by simp [sftRun, hs]
    rw [hrun] at h ⊢
    obtain ⟨h1, h2⟩ := sftReach_closed hr (Nat.mod_lt _ (by norm_num)) h
    dsimp only at h1 h2
    have ha : a = 2 * (a / 2) + a % 2 := by omega
    have hm : min (min k 12 + 1) 12 = min (k + 1) 12 := by omega
    refine ⟨?_, ?_⟩
    · rw [hm, two_mul_mod_add_mod _ _ _ _ (by omega), ← ha] at h1; exact h1
    · rw [ha, acc2_succ _ _ _ (Nat.mod_lt _ (by norm_num))]
      refine ⟨hacc, fun L hL hLk hf => ?_⟩
      have hL13 : L ≤ 13 := hf.1
      have := h2 L hL (by omega)
      rw [two_mul_mod_add_mod _ _ _ _ (by omega)] at this
      exact this hf

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

/-! ## The exact certificate, checked in Lean

`CertData.Gate4` holds the frozen weights `W` (from `scripts/cstar_models/exact3.c`) and a
computable re-implementation of the exact checker (`go`, `bb`, `checkBin`).  Below: `go_sound`
(the checker's value lower-bounds the weighted count of good descendants: window pass,
zone transfer, stage resolution, ambiguous resolution by `min`), `bb_sound` (branch and bound),
`grow_good` (a bin check gives growth for every good cell in the bin), the root entry
(`rootSum_le`) and the assembly `cleanCertificate449_of_data`. -/

section Certificate
open Data

/-- Zone property of one window `[Ac - δ, Ac + δ]` for zone bounds `z` (all in `2^-90` units). -/
def ZoneOK (cxlo cxhi crlo crhi Ac : ℤ) (z : ℤ × ℤ) : Prop :=
  ∀ c h δ y : ℝ, (cxlo : ℝ) ≤ c → c ≤ cxhi → (crlo : ℝ) ≤ h → h ≤ crhi → δ ≤ dhi →
    h ≤ 2 * δ → c ≤ y → y ≤ c + h → (Ac : ℝ) - δ ≤ y → y ≤ Ac + δ →
    ((0 : ℝ) ≤ z.1 ∧ y - c ≤ z.1) ∨ ((0 : ℝ) ≤ z.2 ∧ c + h - y ≤ z.2)

theorem wstep_mono {cxlo cxhi crlo crhi Ac : ℤ} {z z' : ℤ × ℤ}
    (h : wstep cxlo cxhi crlo crhi Ac z = some z') : z.1 ≤ z'.1 ∧ z.2 ≤ z'.2 := by
  unfold wstep at h
  split_ifs at h with h1 h2 h3 h4 h4 h3 h4 h4 <;> (try cases h) <;> simp_all

theorem wstep_sound {cxlo cxhi crlo crhi Ac : ℤ} {z z' : ℤ × ℤ}
    (h : wstep cxlo cxhi crlo crhi Ac z = some z') : ZoneOK cxlo cxhi crlo crhi Ac z' := by
  intro c hh δ y hc1 hc2 hh1 hh2 hδ h2δ hy1 hy2 hy3 hy4
  have hdhi : (δ : ℝ) ≤ (dhi : ℝ) := hδ
  unfold wstep at h
  by_cases h1 : cxhi + crhi < Ac - dhi ∨ Ac + dhi < cxlo
  · exfalso
    rcases h1 with h1 | h1
    · have : ((cxhi : ℝ) + crhi) < Ac - dhi := by exact_mod_cast h1
      linarith
    · have : ((Ac : ℝ) + dhi) < cxlo := by exact_mod_cast h1
      linarith
  rw [if_neg h1] at h
  by_cases h2 : max cxlo (Ac - dhi) ≤ min cxhi (Ac + dhi - crlo)
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  simp only [Option.some.injEq] at h
  subst h
  push Not at h1 h2
  -- not contained: c < Ac - δ or c > Ac + δ - h
  rcases lt_or_ge c ((Ac : ℝ) - δ) with hc | hc
  · right
    have e1 : (cxlo : ℝ) + crlo ≤ Ac + dhi := by linarith
    have e2 : (Ac : ℝ) - dhi ≤ cxhi + crhi := by linarith
    have e1' : cxlo + crlo ≤ Ac + dhi := by exact_mod_cast e1
    have e2' : Ac - dhi ≤ cxhi + crhi := by exact_mod_cast e2
    dsimp only; simp only [if_pos (And.intro e1' e2')]
    have hb : c + hh - y ≤ ((cxhi + crhi - (Ac - dhi) : ℤ) : ℝ) := by push_cast; linarith
    have hm : ((cxhi + crhi - (Ac - dhi) : ℤ) : ℝ) ≤ ((max z.2 (cxhi + crhi - (Ac - dhi)) : ℤ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    exact ⟨by linarith, hb.trans hm⟩
  · left
    have e1 : (cxlo : ℝ) ≤ Ac + dhi := by linarith
    have e2 : (Ac : ℝ) - dhi ≤ cxhi := by linarith
    have e1' : cxlo ≤ Ac + dhi := by exact_mod_cast e1
    have e2' : Ac - dhi ≤ cxhi := by exact_mod_cast e2
    dsimp only; simp only [if_pos (And.intro e1' e2')]
    have hb : y - c ≤ ((Ac + dhi - cxlo : ℤ) : ℝ) := by push_cast; linarith
    have hm : ((Ac + dhi - cxlo : ℤ) : ℝ) ≤ ((max z.1 (Ac + dhi - cxlo) : ℤ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    exact ⟨by linarith, hb.trans hm⟩

theorem foldl_bind_some {α : Type*} (g : ℕ → α → Option α) (le : α → α → Prop)
    (hrefl : ∀ z, le z z) (htrans : ∀ a b c, le a b → le b c → le a c)
    (hmono : ∀ t z z', g t z = some z' → le z z') :
    ∀ (l : List ℕ) (z z' : α), l.foldl (fun acc t => acc.bind (g t)) (some z) = some z' →
      le z z' ∧ ∀ t ∈ l, ∃ z1 z2, g t z1 = some z2 ∧ le z2 z'
  | [], z, z', h => by
    simp only [List.foldl_nil, Option.some.injEq] at h; subst h; simp [hrefl]
  | t :: l, z, z', h => by
    simp only [List.foldl_cons, Option.bind_some] at h
    cases hg : g t z with
    | none =>
      exfalso; rw [hg] at h
      have : ∀ l' : List ℕ, l'.foldl (fun acc t => acc.bind (g t)) none = none := by
        intro l'; induction l' with
        | nil => rfl
        | cons _ _ ih => simpa using ih
      rw [this] at h; cases h
    | some z2 =>
      rw [hg] at h
      obtain ⟨h1, h2⟩ := foldl_bind_some g le hrefl htrans hmono l z2 z' h
      refine ⟨htrans _ _ _ (hmono t z z2 hg) h1, fun t' ht' => ?_⟩
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact ⟨z, z2, hg, h1⟩
      · exact h2 t' ht'

theorem zoneOK_mono {cxlo cxhi crlo crhi Ac : ℤ} {z z' : ℤ × ℤ} (h1 : z.1 ≤ z'.1) (h2 : z.2 ≤ z'.2)
    (h : ZoneOK cxlo cxhi crlo crhi Ac z) : ZoneOK cxlo cxhi crlo crhi Ac z' := by
  intro c hh δ y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have h1' : (z.1 : ℝ) ≤ z'.1 := by exact_mod_cast h1
  have h2' : (z.2 : ℝ) ≤ z'.2 := by exact_mod_cast h2
  rcases h c hh δ y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem oneZ_pos : (0 : ℤ) < one := by unfold one; positivity

theorem fl_spec (v : ℤ) : fl v * one ≤ v ∧ v < (fl v + 1) * one := by
  unfold fl
  have := oneZ_pos
  constructor
  · rw [mul_comm]; exact Int.mul_ediv_self_le (ne_of_gt this)
  · rw [add_mul, one_mul, mul_comm]; have := Int.lt_mul_ediv_self_add (x := v) this; linarith

theorem windows_sound {cxlo cxhi crlo crhi zl zr : ℤ} {z' : ℤ × ℤ} (hcr : 0 ≤ crlo)
    (h : windows cxlo cxhi crlo crhi zl zr = some z') :
    zl ≤ z'.1 ∧ zr ≤ z'.2 ∧ ∀ A : ℤ, ZoneOK cxlo cxhi crlo crhi (A * one) z' := by
  unfold windows at h
  obtain ⟨hle, hall⟩ := foldl_bind_some (fun t => wstep cxlo cxhi crlo crhi ((fl cxlo - 1 + Int.ofNat t) * one))
    (fun (a b : ℤ × ℤ) => a.1 ≤ b.1 ∧ a.2 ≤ b.2) (fun _ => ⟨le_rfl, le_rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩) (fun _ _ _ h => wstep_mono h) _ _ _ h
  refine ⟨hle.1, hle.2, fun A => ?_⟩
  by_cases hA : fl cxlo - 1 ≤ A ∧ A ≤ fl (cxhi + crhi) + 2
  · obtain ⟨z1, z2, hz, hz2⟩ := hall (A - (fl cxlo - 1)).toNat (by
      rw [List.mem_range]; omega)
    rw [show fl cxlo - 1 + Int.ofNat (A - (fl cxlo - 1)).toNat = A by
      rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]; ring] at hz
    exact zoneOK_mono hz2.1 hz2.2 (wstep_sound hz)
  · intro c hh δ y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    exfalso
    push_cast at a9 a10
    have hd : (dhi : ℝ) < one := by unfold dhi one F; norm_num
    have hδ : δ < one := by linarith
    have hδ0 : 0 ≤ δ := by
      have : (0:ℝ) ≤ crlo := by exact_mod_cast hcr
      linarith
    obtain ⟨f1, f2⟩ := fl_spec cxlo
    obtain ⟨g1, g2⟩ := fl_spec (cxhi + crhi)
    have f1' : ((fl cxlo : ℤ) : ℝ) * one ≤ cxlo := by exact_mod_cast f1
    have g2' : ((cxhi + crhi : ℤ) : ℝ) < ((fl (cxhi + crhi) : ℤ) + 1) * one := by exact_mod_cast g2
    push_cast at g2'
    have hone : (0 : ℝ) < one := by exact_mod_cast oneZ_pos
    rcases not_and_or.1 hA with hA | hA
    · push Not at hA
      have : A + 1 ≤ fl cxlo - 1 := by omega
      have : ((A : ℝ) + 1) * one ≤ ((fl cxlo : ℝ) - 1) * one := by
        apply mul_le_mul_of_nonneg_right _ hone.le; exact_mod_cast this
      nlinarith
    · push Not at hA
      have : fl (cxhi + crhi) + 3 ≤ A := by omega
      have : ((fl (cxhi + crhi) : ℝ) + 3) * one ≤ (A : ℝ) * one := by
        apply mul_le_mul_of_nonneg_right _ hone.le; exact_mod_cast this
      nlinarith

theorem step_eq (s d : ℕ) : Data.step s d = sftStep s d := by
  unfold Data.step sftStep
  rcases lt_or_ge s 25 with h | h
  · interval_cases s <;> rfl
  · rw [show (Data.sftT[s]? : Option (ℕ × ℕ)) = none from
      Array.getElem?_eq_none (by simp [Data.sftT]; omega),
      show (sftT[s]? : Option (ℕ × ℕ)) = none from List.getElem?_eq_none (by simp [sftT]; omega)]

theorem one_eq : ((one : ℤ) : ℝ) = 2 ^ 90 := by simp [one, F]; norm_num

noncomputable def pend (k : ℕ) : ℕ :=
  Nat.find (pow_unbounded_of_one_lt (2 * δ3 * 2 ^ k) (by norm_num : (1 : ℝ) < 3))

theorem pend_spec (k : ℕ) : 2 * δ3 * 2 ^ k < 3 ^ pend k :=
  Nat.find_spec (pow_unbounded_of_one_lt (2 * δ3 * 2 ^ k) (by norm_num : (1 : ℝ) < 3))

theorem pend_min {k n : ℕ} (h : n < pend k) : (3 : ℝ) ^ n ≤ 2 * δ3 * 2 ^ k :=
  not_lt.1 (Nat.find_min (pow_unbounded_of_one_lt (2 * δ3 * 2 ^ k) (by norm_num : (1 : ℝ) < 3)) h)

/-- The `x`-bin of a cell: `⌊N · frac(3ⁿ a / 2ᵏ)⌋` at the pending stage. -/
noncomputable def ibin (k a : ℕ) : ℕ := ⌊(N : ℚ) * Int.fract ((3 : ℚ) ^ pend k * a / 2 ^ k)⌋₊

/-- The `ρ`-bin of level `k`: interior edges below `ρ = 3ⁿ / 2ᵏ` (in `2^-90` units). -/
noncomputable def jbin (k : ℕ) : ℕ :=
  (edges.toList.filter (fun (e : ℤ) => decide ((e : ℚ) < (3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90))).length

/-- The certificate weight of a cell. -/
noncomputable def Wc (k a : ℕ) : ℤ := wt (sftRun k a) (ibin k a) (jbin k)

open Classical in
/-- Weighted count of the good depth-`r` descendants. -/
noncomputable def Sum (r k a : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ r), if Good449 (k + r) (2 ^ r * a + j) then (Wc (k + r) (2 ^ r * a + j) : ℝ) else 0

/-- The invariant of a box of the checker realized by the cell `(k, a)`. -/
structure Inv (k a s : ℕ) (xlo xhi rlo rhi zl zr : ℤ) : Prop where
  hk : 5 ≤ k
  hrlo : 0 ≤ rlo
  ha : a < 2 ^ k
  hs : sftRun k a = s
  hs99 : s ≠ 99
  hx : ∃ m : ℤ, (xlo : ℝ) ≤ ((3 : ℝ) ^ pend k * a / 2 ^ k - m) * 2 ^ 90 ∧
    ((3 : ℝ) ^ pend k * a / 2 ^ k - m) * 2 ^ 90 ≤ xhi
  hr1 : (rlo : ℝ) ≤ (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90
  hr2 : (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 ≤ rhi
  hz : ∀ n' < pend k, ∀ A : ℕ, ∀ t ∈ Count.cell k a, t ∈ window 3 n' A →
    ((0 : ℝ) ≤ zl ∧ ((3 : ℝ) ^ pend k * t - 3 ^ pend k * a / 2 ^ k) * 2 ^ 90 ≤ zl) ∨
    ((0 : ℝ) ≤ zr ∧ ((3 : ℝ) ^ pend k * (a + 1) / 2 ^ k - 3 ^ pend k * t) * 2 ^ 90 ≤ zr)

theorem good_of_inv {k a s : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (h : Inv k a s xlo xhi rlo rhi zl zr)
    (hl : zl < 0) (hr : zr < 0) : Good449 k a := by
  refine ⟨h.ha, (acc2_of_sftRun k a (h.hs ▸ h.hs99)).2, fun n' A hn' => ?_⟩
  have hlt : n' < pend k := by
    by_contra hc
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (not_lt.1 hc)
    linarith [pend_spec k]
  refine Set.disjoint_left.2 fun t ht hw => ?_
  have hl' : (zl : ℝ) < 0 := by exact_mod_cast hl
  have hr' : (zr : ℝ) < 0 := by exact_mod_cast hr
  rcases h.hz n' hlt A t ht hw with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

theorem fold_min_le_init (g : ℕ → ℤ) : ∀ (n : ℕ) (acc : ℤ),
    Nat.fold n (fun u _ acc => min acc (g u)) acc ≤ acc ∧
      ∀ u < n, Nat.fold n (fun u _ acc => min acc (g u)) acc ≤ g u
  | 0, acc => ⟨le_rfl, fun u hu => absurd hu (Nat.not_lt_zero _)⟩
  | n + 1, acc => by
    rw [Nat.fold_succ]
    obtain ⟨h1, h2⟩ := fold_min_le_init g n acc
    refine ⟨(min_le_left _ _).trans h1, fun u hu => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · exact (min_le_left _ _).trans (h2 u hu)
    · exact min_le_right _ _

theorem fold2_min_le (f : ℕ → ℕ → ℤ) (nj : ℕ) : ∀ (nx : ℕ) (init : ℤ),
    Nat.fold nx (fun t _ acc => Nat.fold nj (fun u _ acc => min acc (f t u)) acc) init ≤ init ∧
      ∀ t < nx, ∀ u < nj,
        Nat.fold nx (fun t _ acc => Nat.fold nj (fun u _ acc => min acc (f t u)) acc) init ≤ f t u
  | 0, init => ⟨le_rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | n + 1, init => by
    rw [Nat.fold_succ]
    obtain ⟨h1, h2⟩ := fold2_min_le f nj n init
    obtain ⟨g1, g2⟩ := fold_min_le_init (f n) nj
      (Nat.fold n (fun t _ acc => Nat.fold nj (fun u _ acc => min acc (f t u)) acc) init)
    refine ⟨g1.trans h1, fun t ht u hu => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact g1.trans (h2 t ht u hu)
    · exact g2 u hu

theorem rbin_le_jbin {r : ℤ} {k : ℕ} (h : (r : ℝ) ≤ (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90) :
    rbin r ≤ jbin k := by
  unfold rbin jbin
  rw [← Array.foldl_toList]
  generalize edges.toList = l
  suffices ∀ c, l.foldl (fun c e => if e < r then c + 1 else c) c ≤ c +
      (l.filter (fun (e : ℤ) => decide ((e : ℚ) < (3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90))).length by
    simpa using this 0
  induction l with
  | nil => simp
  | cons e l ih =>
    intro c
    simp only [List.foldl_cons, List.filter_cons]
    by_cases he : e < r
    · have : (e : ℚ) < (3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90 := by
        have h' : ((e : ℚ) : ℝ) < (((3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90 : ℚ) : ℝ) := by
          push_cast; have : (e : ℝ) < r := by exact_mod_cast he
          linarith
        exact_mod_cast h'
      rw [if_pos he, if_pos (by simpa using this)]
      simp only [List.length_cons]; have := ih (c + 1); omega
    · rw [if_neg he]
      split_ifs <;> (try simp only [List.length_cons]) <;> have := ih c <;> omega

theorem jbin_le_rbin {r : ℤ} {k : ℕ} (h : (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 ≤ r) :
    jbin k ≤ rbin r := by
  unfold rbin jbin
  rw [← Array.foldl_toList]
  generalize edges.toList = l
  suffices ∀ c, c + (l.filter (fun (e : ℤ) => decide ((e : ℚ) < (3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90))).length
      ≤ l.foldl (fun c e => if e < r then c + 1 else c) c by
    simpa using this 0
  induction l with
  | nil => simp
  | cons e l ih =>
    intro c
    simp only [List.foldl_cons, List.filter_cons]
    by_cases he : (e : ℚ) < (3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90
    · have : e < r := by
        have h' : (e : ℝ) < r := by
          have : ((e : ℚ) : ℝ) < (((3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90 : ℚ) : ℝ) := by exact_mod_cast he
          push_cast at this; linarith
        exact_mod_cast h'
      rw [if_pos this, if_pos (by simpa using he)]
      simp only [List.length_cons]; have := ih (c + 1); omega
    · rw [if_neg (by simpa using he)]
      split_ifs <;> have := ih c <;> have := ih (c + 1) <;> omega

theorem ibin_eq (k a : ℕ) (I : ℤ) (m : ℤ)
    (hI : I = ⌊(N : ℝ) * ((3 : ℝ) ^ pend k * a / 2 ^ k - m)⌋) :
    (I % (N : ℤ)).toNat = ibin k a := by
  set P : ℚ := (3 : ℚ) ^ pend k * a / 2 ^ k with hP
  have hPr : ((P : ℚ) : ℝ) = (3 : ℝ) ^ pend k * a / 2 ^ k := by rw [hP]; push_cast; ring
  have hN : (N : ℤ) = 128 := rfl
  have key : I = ⌊(N : ℚ) * Int.fract P⌋ + (N : ℤ) * (⌊P⌋ - m) := by
    rw [hI, ← hPr]
    have : (N : ℝ) * ((P : ℝ) - m) = (((N : ℚ) * Int.fract P : ℚ) : ℝ) + (((N : ℤ) * (⌊P⌋ - m) : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [this, Int.floor_add_intCast, Rat.floor_cast]
  have h0 : 0 ≤ ⌊(N : ℚ) * Int.fract P⌋ := Int.floor_nonneg.2 (mul_nonneg (by norm_num) (Int.fract_nonneg _))
  have h1 : ⌊(N : ℚ) * Int.fract P⌋ < (N : ℤ) := by
    rw [Int.floor_lt]; push_cast
    have := Int.fract_lt_one P
    have hn : (0 : ℚ) < N := by norm_num [N]
    nlinarith
  rw [key, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]
  unfold ibin; rw [← hP]
  exact (Int.floor_toNat _).symm

theorem leafmin_le {k a s : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (h : Inv k a s xlo xhi rlo rhi zl zr) :
    leafmin s xlo xhi rlo rhi ≤ Wc k a := by
  obtain ⟨m, hm1, hm2⟩ := h.hx
  set P : ℝ := (3 : ℝ) ^ pend k * a / 2 ^ k with hP
  have hone : ((one : ℤ) : ℝ) = 2 ^ 90 := one_eq
  have honep : (0 : ℤ) < one := by unfold one; positivity
  set f0 := fl xlo with hf0
  set I : ℤ := ⌊(N : ℝ) * (P - (m + f0 : ℤ))⌋ with hIdef
  set ia := ((xlo - f0 * one) * Int.ofNat N) / one with hia
  set ib := ((xhi - f0 * one) * Int.ofNat N) / one with hib
  have hNr : ((Int.ofNat N : ℤ) : ℝ) = 128 := by simp [N]
  have hNr' : ((N : ℕ) : ℝ) = 128 := by simp [N]
  -- ia ≤ I
  have hiaI : ia ≤ I := by
    rw [hIdef, Int.le_floor]
    have e1 : ia * one ≤ (xlo - f0 * one) * Int.ofNat N := by
      rw [hia, mul_comm]; exact Int.mul_ediv_self_le (ne_of_gt honep)
    have e1' : (ia : ℝ) * 2 ^ 90 ≤ ((xlo : ℝ) - f0 * 2 ^ 90) * 128 := by
      have : ((ia * one : ℤ) : ℝ) ≤ (((xlo - f0 * one) * Int.ofNat N : ℤ) : ℝ) := by exact_mod_cast e1
      push_cast at this; rwa [hone, hNr] at this
    rw [hNr']; push_cast
    nlinarith
  have hIib : I ≤ ib := by
    have e2 : (xhi - f0 * one) * Int.ofNat N < (ib + 1) * one := by
      rw [hib, add_mul, one_mul, mul_comm (_ / one)]
      have := Int.lt_mul_ediv_self_add (x := (xhi - f0 * one) * Int.ofNat N) honep; linarith
    have e2' : ((xhi : ℝ) - f0 * 2 ^ 90) * 128 < ((ib : ℝ) + 1) * 2 ^ 90 := by
      have : (((xhi - f0 * one) * Int.ofNat N : ℤ) : ℝ) < (((ib + 1) * one : ℤ) : ℝ) := by exact_mod_cast e2
      push_cast at this; rwa [hone, hNr] at this
    have : (I : ℝ) < ib + 1 := by
      have := Int.floor_le ((N : ℝ) * (P - (m + f0 : ℤ)))
      rw [← hIdef, hNr'] at this; push_cast at this
      nlinarith
    have h3 : I < ib + 1 := by exact_mod_cast this
    omega
  have hj1 := rbin_le_jbin h.hr1
  have hj2 := jbin_le_rbin h.hr2
  unfold leafmin
  have hfold := (fold2_min_le (fun t u => wt s ((ia + Int.ofNat t) % Int.ofNat N).toNat (rbin rlo + u))
    (rbin rhi + 1 - rbin rlo) (ib - ia + 1).toNat (wt s ((ia % Int.ofNat N).toNat) (rbin rlo))).2
    (I - ia).toNat (by omega) (jbin k - rbin rlo) (by omega)
  refine hfold.trans (le_of_eq ?_)
  rw [show ia + Int.ofNat (I - ia).toNat = I by rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]; ring,
    show rbin rlo + (jbin k - rbin rlo) = jbin k by omega]
  unfold Wc
  rw [h.hs, show (Int.ofNat N) = (N : ℤ) from rfl, ibin_eq k a I (m + f0) (by rw [hIdef])]

theorem cell_child {k a d : ℕ} {t : ℝ} (ht : t ∈ Count.cell (k + 1) (2 * a + d)) (hd : d < 2) :
    t ∈ Count.cell k a ∧ (2 * a + d : ℝ) / 2 ^ (k + 1) ≤ t ∧ t ≤ (2 * a + d + 1 : ℝ) / 2 ^ (k + 1) := by
  obtain ⟨h1, h2⟩ := ht
  push_cast at h1 h2
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hd' : (d : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  rw [pow_succ] at h1 h2
  have hk2 : (0 : ℝ) < 2 ^ k * 2 := by positivity
  refine ⟨⟨?_, ?_⟩, by rw [pow_succ]; exact h1, by rw [pow_succ]; exact h2⟩
  · refine le_trans ?_ h1
    rw [le_div_iff₀ hk2, div_mul_eq_mul_div, div_le_iff₀ hk]; nlinarith
  · refine h2.trans ?_
    rw [div_le_iff₀ hk2, div_mul_eq_mul_div, le_div_iff₀ hk]; nlinarith

/-- Halving bounds: `rlo / 2 ≤ r / 2 ≤ (rhi + 1) / 2`. -/
theorem half_bounds {rlo rhi : ℤ} {r : ℝ} (h1 : (rlo : ℝ) ≤ r) (h2 : r ≤ rhi) :
    ((rlo / 2 : ℤ) : ℝ) ≤ r / 2 ∧ r / 2 ≤ (((rhi + 1) / 2 : ℤ) : ℝ) := by
  constructor
  · have : rlo / 2 * 2 ≤ rlo := Int.ediv_mul_le rlo (by norm_num)
    have : ((rlo / 2 : ℤ) : ℝ) * 2 ≤ rlo := by exact_mod_cast this
    linarith
  · have : rhi ≤ (rhi + 1) / 2 * 2 := by omega
    have : (rhi : ℝ) ≤ (((rhi + 1) / 2 : ℤ) : ℝ) * 2 := by exact_mod_cast this
    linarith

/-- **Zone transfer to the left child** (same stage coordinates). -/
theorem child_zone0 {k a s : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (h : Inv k a s xlo xhi rlo rhi zl zr)
    {n' : ℕ} (hn' : n' < pend k) {A : ℕ} {t : ℝ}
    (ht : t ∈ Count.cell (k + 1) (2 * a + 0)) (hw : t ∈ window 3 n' A) :
    ((0 : ℝ) ≤ zl ∧ ((3 : ℝ) ^ pend k * t - 3 ^ pend k * (2 * a + 0) / 2 ^ (k + 1)) * 2 ^ 90 ≤ zl) ∨
    ((0 : ℝ) ≤ ((if rlo / 2 ≤ zr then zr - rlo / 2 else -1 : ℤ) : ℝ) ∧
      ((3 : ℝ) ^ pend k * (2 * a + 0 + 1) / 2 ^ (k + 1) - 3 ^ pend k * t) * 2 ^ 90 ≤
        ((if rlo / 2 ≤ zr then zr - rlo / 2 else -1 : ℤ) : ℝ)) := by
  obtain ⟨htp, hl, hr⟩ := cell_child ht (by norm_num)
  have hz := h.hz n' hn' A t htp hw
  set n := pend k
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  set L : ℝ := (3 : ℝ) ^ n / 2 ^ k * 2 ^ 90 with hL
  have hlo_le : ((rlo / 2 : ℤ) : ℝ) ≤ L / 2 := (half_bounds h.hr1 h.hr2).1
  have hl' : (3 : ℝ) ^ n * (2 * a + 0) / 2 ^ (k + 1) ≤ 3 ^ n * t := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl) h3.le
  have hr' : (3 : ℝ) ^ n * t ≤ 3 ^ n * (2 * a + 0 + 1) / 2 ^ (k + 1) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) h3.le
  have eP : ((3 : ℝ) ^ n * (2 * a + 0) / 2 ^ (k + 1)) * 2 ^ 90 =
      ((3 : ℝ) ^ n * a / 2 ^ k) * 2 ^ 90 + 0 * (L / 2) := by rw [hL, pow_succ]; field_simp
  have eQ : ((3 : ℝ) ^ n * (2 * a + 0 + 1) / 2 ^ (k + 1)) * 2 ^ 90 =
      ((3 : ℝ) ^ n * (a + 1) / 2 ^ k) * 2 ^ 90 - (1 - 0) * (L / 2) := by
    rw [hL, pow_succ]; field_simp; ring
  have hl'' := mul_le_mul_of_nonneg_right hl' (by positivity : (0 : ℝ) ≤ 2 ^ 90)
  have hr'' := mul_le_mul_of_nonneg_right hr' (by positivity : (0 : ℝ) ≤ 2 ^ 90)
  rcases hz with ⟨z1, z2⟩ | ⟨z1, z2⟩
  · left; refine ⟨z1, ?_⟩; nlinarith
  · right
    have : rlo / 2 ≤ zr := by
      have : ((rlo / 2 : ℤ) : ℝ) ≤ zr := by nlinarith
      exact_mod_cast this
    rw [if_pos this]; push_cast
    constructor <;> nlinarith

/-- **Zone transfer to the right child** (same stage coordinates). -/
theorem child_zone1 {k a s : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (h : Inv k a s xlo xhi rlo rhi zl zr)
    {n' : ℕ} (hn' : n' < pend k) {A : ℕ} {t : ℝ}
    (ht : t ∈ Count.cell (k + 1) (2 * a + 1)) (hw : t ∈ window 3 n' A) :
    ((0 : ℝ) ≤ ((if rlo / 2 ≤ zl then zl - rlo / 2 else -1 : ℤ) : ℝ) ∧
      ((3 : ℝ) ^ pend k * t - 3 ^ pend k * (2 * a + 1) / 2 ^ (k + 1)) * 2 ^ 90 ≤
        ((if rlo / 2 ≤ zl then zl - rlo / 2 else -1 : ℤ) : ℝ)) ∨
    ((0 : ℝ) ≤ zr ∧ ((3 : ℝ) ^ pend k * (2 * a + 1 + 1) / 2 ^ (k + 1) - 3 ^ pend k * t) * 2 ^ 90 ≤ zr) := by
  obtain ⟨htp, hl, hr⟩ := cell_child ht (by norm_num)
  have hz := h.hz n' hn' A t htp hw
  set n := pend k
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  set L : ℝ := (3 : ℝ) ^ n / 2 ^ k * 2 ^ 90 with hL
  have hlo_le : ((rlo / 2 : ℤ) : ℝ) ≤ L / 2 := (half_bounds h.hr1 h.hr2).1
  have hl' : (3 : ℝ) ^ n * (2 * a + 1) / 2 ^ (k + 1) ≤ 3 ^ n * t := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl) h3.le
  have hr' : (3 : ℝ) ^ n * t ≤ 3 ^ n * (2 * a + 1 + 1) / 2 ^ (k + 1) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) h3.le
  have eP : ((3 : ℝ) ^ n * (2 * a + 1) / 2 ^ (k + 1)) * 2 ^ 90 =
      ((3 : ℝ) ^ n * a / 2 ^ k) * 2 ^ 90 + 1 * (L / 2) := by rw [hL, pow_succ]; field_simp
  have eQ : ((3 : ℝ) ^ n * (2 * a + 1 + 1) / 2 ^ (k + 1)) * 2 ^ 90 =
      ((3 : ℝ) ^ n * (a + 1) / 2 ^ k) * 2 ^ 90 - (1 - 1) * (L / 2) := by
    rw [hL, pow_succ]; field_simp; ring
  have hl'' := mul_le_mul_of_nonneg_right hl' (by positivity : (0 : ℝ) ≤ 2 ^ 90)
  have hr'' := mul_le_mul_of_nonneg_right hr' (by positivity : (0 : ℝ) ≤ 2 ^ 90)
  rcases hz with ⟨z1, z2⟩ | ⟨z1, z2⟩
  · left
    have : rlo / 2 ≤ zl := by
      have : ((rlo / 2 : ℤ) : ℝ) ≤ zl := by nlinarith
      exact_mod_cast this
    rw [if_pos this]; push_cast
    constructor <;> nlinarith
  · right; refine ⟨z1, ?_⟩; nlinarith

set_option exponentiation.threshold 10000 in
theorem δ3_bounds : (8921239036815585702838272 / 2 ^ 90 : ℝ) < δ3 ∧
    δ3 < (8921239036817784726093824 / 2 ^ 90 : ℝ) := by
  have hx : 0 ≤ δ3 := by unfold δ3; positivity
  have h100 : δ3 ^ (100 : ℕ) = ((3 : ℝ) ^ (449 : ℕ))⁻¹ := by
    unfold δ3
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (-(449 / 100 : ℝ) * ((100 : ℕ) : ℝ)) = -((449 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  constructor
  · rw [← pow_lt_pow_iff_left₀ (by positivity) hx (by norm_num : (100 : ℕ) ≠ 0), h100]
    rw [div_pow, lt_inv_comm₀ (by positivity) (by positivity), inv_div]; norm_num
  · rw [← pow_lt_pow_iff_left₀ hx (by positivity) (by norm_num : (100 : ℕ) ≠ 0), h100]
    rw [div_pow, inv_lt_comm₀ (by positivity) (by positivity), inv_div]; norm_num



theorem δ3_pos : 0 < δ3 := by unfold δ3; positivity

theorem dlo_lt : ((dlo : ℤ) : ℝ) < δ3 * 2 ^ 90 := by
  have := δ3_bounds.1; unfold dlo; push_cast
  rw [div_lt_iff₀ (by positivity)] at this; linarith
theorem lt_dhi : δ3 * 2 ^ 90 < ((dhi : ℤ) : ℝ) := by
  have := δ3_bounds.2; unfold dhi; push_cast
  rw [lt_div_iff₀ (by positivity)] at this; linarith

theorem sftRun_succ (k a d : ℕ) (hd : d < 2) :
    sftRun (k + 1) (2 * a + d) = if sftRun k a = 99 then 99 else sftStep (sftRun k a) d := by
  simp only [sftRun]
  rw [show (2 * a + d) / 2 = a by omega, show (2 * a + d) % 2 = d by omega]

theorem pend_succ_unres {k : ℕ} (h : 2 * δ3 * 2 ^ (k + 1) < 3 ^ pend k) : pend (k + 1) = pend k := by
  apply le_antisymm
  · exact Nat.find_min' _ h
  · by_contra hc
    push Not at hc
    have h1 := pend_min hc
    have h2 := pend_spec (k + 1)
    rw [pow_succ] at h2
    nlinarith [δ3_pos, (by positivity : (0 : ℝ) < 2 ^ k)]

theorem pend_succ_res {k : ℕ} (h : (3 : ℝ) ^ pend k ≤ 2 * δ3 * 2 ^ (k + 1)) :
    pend (k + 1) = pend k + 1 := by
  apply le_antisymm
  · apply Nat.find_min'
    have := pend_spec k
    rw [pow_succ, pow_succ]
    nlinarith [δ3_pos, (by positivity : (0 : ℝ) < 2 ^ k)]
  · by_contra hc
    push Not at hc
    have h2 := pend_spec (k + 1)
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.lt_succ_iff.1 hc)
    linarith

/-- Soundness of the evaluator at depth `r`. -/
def GoSound (r : ℕ) : Prop := ∀ k a s xlo xhi rlo rhi zl zr,
  Inv k a s xlo xhi rlo rhi zl zr → (go r s xlo xhi rlo rhi zl zr : ℝ) ≤ Sum r k a

theorem child_common {k a s d : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (h : Inv k a s xlo xhi rlo rhi zl zr)
    (hd : d < 2) (ht : step s d ≠ 99) :
    5 ≤ k + 1 ∧ 0 ≤ rlo / 2 ∧ 2 * a + d < 2 ^ (k + 1) ∧ sftRun (k + 1) (2 * a + d) = step s d := by
  refine ⟨by have := h.hk; omega, Int.ediv_nonneg h.hrlo (by norm_num), ?_, ?_⟩
  · have := h.ha; rw [pow_succ]; omega
  · rw [sftRun_succ k a d hd, h.hs, if_neg h.hs99, step_eq]

/-- The unresolved left/right child keeps the stage. -/
theorem kid_unres {r k a s d : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (IH : GoSound r)
    (h : Inv k a s xlo xhi rlo rhi zl zr) (hd : d < 2) (ht : step s d ≠ 99)
    (hu : 2 * δ3 * 2 ^ (k + 1) < 3 ^ pend k) :
    (kidF (go r) (step s d) (if d = 0 then xlo else xlo + rlo / 2)
      (if d = 0 then xhi else xhi + (rhi + 1) / 2) (rlo / 2) ((rhi + 1) / 2)
      (if d = 0 then zl else if rlo / 2 ≤ zl then zl - rlo / 2 else -1)
      (if d = 0 then (if rlo / 2 ≤ zr then zr - rlo / 2 else -1) else zr) false : ℝ) ≤
      Sum r (k + 1) (2 * a + d) := by
  obtain ⟨c1, c2, c3, c4⟩ := child_common h hd ht
  have hp := pend_succ_unres hu
  simp only [kidF, Bool.false_eq_true, if_false]
  apply IH
  obtain ⟨m, hm1, hm2⟩ := h.hx
  have hb := half_bounds h.hr1 h.hr2
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have eL : (3 : ℝ) ^ pend k / 2 ^ (k + 1) * 2 ^ 90 = (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 / 2 := by
    rw [pow_succ]; field_simp
  have eP : ((3 : ℝ) ^ pend k * ((2 * a + d : ℕ) : ℝ) / 2 ^ (k + 1) - m) * 2 ^ 90 =
      ((3 : ℝ) ^ pend k * a / 2 ^ k - m) * 2 ^ 90 + d * ((3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 / 2) := by
    push_cast; rw [pow_succ]; field_simp; ring
  refine ⟨c1, c2, c3, c4, ht, ⟨m, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hp, eP]; interval_cases d
    · simp; exact hm1
    · simp only [one_ne_zero, if_false, Nat.cast_one, one_mul]; push_cast; linarith [hb.1]
  · rw [hp, eP]; interval_cases d
    · simp; exact hm2
    · simp only [one_ne_zero, if_false, Nat.cast_one, one_mul]; push_cast; linarith [hb.2]
  · rw [hp, eL]; exact hb.1
  · rw [hp, eL]; exact hb.2
  · intro n' hn' A t ht' hw
    rw [hp] at hn' ⊢
    interval_cases d
    · have := child_zone0 h hn' ht' hw
      simp only [if_true]; push_cast; simpa using this
    · have := child_zone1 h hn' ht' hw
      simp only [one_ne_zero, if_false]; push_cast; simpa using this

theorem W_all_nonneg : W.all (fun x => decide (0 ≤ x)) = true := by native_decide

theorem wt_nonneg (s i j : ℕ) : 0 ≤ wt s i j := by
  unfold wt
  have h := W_all_nonneg
  rw [Array.all_eq_true] at h
  by_cases hi : s * N * M + i * M + j < W.size
  · rw [getElem!_pos W _ hi]; simpa using h _ hi
  · rw [getElem!_neg W _ hi]; rfl

theorem Sum_nonneg (r k a : ℕ) : 0 ≤ Sum r k a := by
  unfold Sum
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · unfold Wc; exact_mod_cast wt_nonneg _ _ _
  · exact le_rfl

set_option maxHeartbeats 2000000 in
/-- The resolved child: window pass at stage `pend k`, then stage `pend k + 1`. -/
theorem kid_res {r k a s d : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (IH : GoSound r)
    (h : Inv k a s xlo xhi rlo rhi zl zr) (hd : d < 2) (ht : step s d ≠ 99)
    (hres : (3 : ℝ) ^ pend k ≤ 2 * δ3 * 2 ^ (k + 1)) :
    (kidF (go r) (step s d) (if d = 0 then xlo else xlo + rlo / 2)
      (if d = 0 then xhi else xhi + (rhi + 1) / 2) (rlo / 2) ((rhi + 1) / 2)
      (if d = 0 then zl else if rlo / 2 ≤ zl then zl - rlo / 2 else -1)
      (if d = 0 then (if rlo / 2 ≤ zr then zr - rlo / 2 else -1) else zr) true : ℝ) ≤
      Sum r (k + 1) (2 * a + d) := by
  obtain ⟨c1, c2, c3, c4⟩ := child_common h hd ht
  have hp := pend_succ_res hres
  set cxlo : ℤ := if d = 0 then xlo else xlo + rlo / 2 with hcxlo
  set cxhi : ℤ := if d = 0 then xhi else xhi + (rhi + 1) / 2 with hcxhi
  set czl : ℤ := if d = 0 then zl else if rlo / 2 ≤ zl then zl - rlo / 2 else -1 with hczl
  set czr : ℤ := if d = 0 then (if rlo / 2 ≤ zr then zr - rlo / 2 else -1) else zr with hczr
  simp only [kidF, if_true]
  rcases hwin : windows cxlo cxhi (rlo / 2) ((rhi + 1) / 2) czl czr with _ | z
  · dsimp only; exact_mod_cast Sum_nonneg r (k + 1) (2 * a + d)
  obtain ⟨wl, wr, wok⟩ := windows_sound c2 hwin
  dsimp only
  apply IH
  obtain ⟨m, hm1, hm2⟩ := h.hx
  have hb := half_bounds h.hr1 h.hr2
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  set n := pend k with hn
  set L : ℝ := (3 : ℝ) ^ n / 2 ^ k * 2 ^ 90 with hL
  set P' : ℝ := (3 : ℝ) ^ n * ((2 * a + d : ℕ) : ℝ) / 2 ^ (k + 1) with hP'
  have eP : (P' - m) * 2 ^ 90 = ((3 : ℝ) ^ n * a / 2 ^ k - m) * 2 ^ 90 + d * (L / 2) := by
    rw [hP', hL]; push_cast; rw [pow_succ]; field_simp; ring
  -- the child position box (before the shift)
  have hc1 : (cxlo : ℝ) ≤ (P' - m) * 2 ^ 90 := by
    rw [eP]; interval_cases d
    · simp [hcxlo]; exact hm1
    · simp only [hcxlo, one_ne_zero, if_false, Nat.cast_one, one_mul]; push_cast; linarith [hb.1]
  have hc2 : (P' - m) * 2 ^ 90 ≤ cxhi := by
    rw [eP]; interval_cases d
    · simp [hcxhi]; exact hm2
    · simp only [hcxhi, one_ne_zero, if_false, Nat.cast_one, one_mul]; push_cast; linarith [hb.2]
  have hone := one_eq
  have e3 : (3 : ℝ) ^ (n + 1) * ((2 * a + d : ℕ) : ℝ) / 2 ^ (k + 1) = 3 * P' := by
    rw [hP', pow_succ]; ring
  have eL3 : (3 : ℝ) ^ (n + 1) / 2 ^ (k + 1) * 2 ^ 90 = 3 * (L / 2) := by
    rw [hL, pow_succ, pow_succ]; field_simp
  refine ⟨c1, by have := c2; omega, c3, c4, ht, ⟨3 * (m + fl cxlo), ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hp, e3]; push_cast; rw [hone]; nlinarith
  · rw [hp, e3]; push_cast; rw [hone]; nlinarith
  · rw [hp, eL3]; push_cast; linarith [hb.1]
  · rw [hp, eL3]; push_cast; linarith [hb.2]
  · intro n' hn' A t ht' hw
    rw [hp] at hn' ⊢
    have e4 : ∀ u : ℝ, ((3 : ℝ) ^ (n + 1) * u - 3 ^ (n + 1) * ((2 * a + d : ℕ) : ℝ) / 2 ^ (k + 1)) * 2 ^ 90
        = 3 * ((3 ^ n * u - P') * 2 ^ 90) := by intro u; rw [hP', pow_succ]; ring
    have e5 : ∀ u : ℝ, ((3 : ℝ) ^ (n + 1) * (((2 * a + d : ℕ) : ℝ) + 1) / 2 ^ (k + 1) - 3 ^ (n + 1) * u) * 2 ^ 90
        = 3 * ((P' - m) * 2 ^ 90 + L / 2 - (3 ^ n * u - m) * 2 ^ 90) := by
      intro u; rw [hP', hL, pow_succ, pow_succ]; field_simp; ring
    rw [e4, e5]
    -- the stage-n zone bound for t, in child coordinates
    have hzone : ((0 : ℝ) ≤ z.1 ∧ (3 ^ n * t - P') * 2 ^ 90 ≤ z.1) ∨
        ((0 : ℝ) ≤ z.2 ∧ (P' - m) * 2 ^ 90 + L / 2 - (3 ^ n * t - m) * 2 ^ 90 ≤ z.2) := by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn' with hlt | rfl
      · have wl' : (czl : ℝ) ≤ z.1 := by exact_mod_cast wl
        have wr' : (czr : ℝ) ≤ z.2 := by exact_mod_cast wr
        have eQ : (P' - m) * 2 ^ 90 + L / 2 - (3 ^ n * t - m) * 2 ^ 90 =
            ((3 : ℝ) ^ n * (2 * a + d + 1) / 2 ^ (k + 1) - 3 ^ n * t) * 2 ^ 90 := by
          rw [hP', hL]; push_cast; rw [pow_succ]; field_simp; ring
        have eR : (3 ^ n * t - P') * 2 ^ 90 =
            ((3 : ℝ) ^ n * t - 3 ^ n * (2 * a + d) / 2 ^ (k + 1)) * 2 ^ 90 := by rw [hP']; push_cast; ring
        rw [eQ, eR]
        interval_cases d
        · rcases child_zone0 h hlt ht' hw with ⟨z1, z2⟩ | ⟨z1, z2⟩
          · left; simp only [hczl, if_true] at wl'; push_cast; constructor <;> linarith
          · right; simp only [hczr, if_true] at wr'; push_cast; constructor <;> linarith
        · rcases child_zone1 h hlt ht' hw with ⟨z1, z2⟩ | ⟨z1, z2⟩
          · left; simp only [hczl, one_ne_zero, if_false] at wl'; push_cast; constructor <;> linarith
          · right; simp only [hczr, one_ne_zero, if_false] at wr'; push_cast; constructor <;> linarith
      · -- the newly resolved stage: the window pass
        obtain ⟨_, hl, hr⟩ := cell_child ht' hd
        obtain ⟨hw1, hw2⟩ := hw
        have h3 : (0 : ℝ) < 3 ^ n := by positivity
        have hw1' : (A : ℝ) - δ3 ≤ 3 ^ n * t := by
          have := (div_le_iff₀' h3).1 hw1; simpa [δ3, Nat.cast_ofNat] using this
        have hw2' : 3 ^ n * t ≤ (A : ℝ) + δ3 := by
          have := (le_div_iff₀' h3).1 hw2; simpa [δ3, Nat.cast_ofNat] using this
        have hl' : P' ≤ 3 ^ n * t := by
          rw [hP', mul_div_assoc]; exact mul_le_mul_of_nonneg_left (by push_cast; exact hl) h3.le
        have hr' : 3 ^ n * t ≤ P' + L / 2 / 2 ^ 90 := by
          have : P' + L / 2 / 2 ^ 90 = 3 ^ n * ((2 * a + d + 1 : ℝ) / 2 ^ (k + 1)) := by
            rw [hP', hL, pow_succ]; push_cast; field_simp
          rw [this]; exact mul_le_mul_of_nonneg_left hr h3.le
        have hLres : L / 2 ≤ 2 * (δ3 * 2 ^ 90) := by
          rw [hL]; rw [pow_succ] at hres
          rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]; nlinarith
        have := wok ((A : ℤ) - m) ((P' - m) * 2 ^ 90) (L / 2) (δ3 * 2 ^ 90) ((3 ^ n * t - m) * 2 ^ 90)
          hc1 hc2 hb.1 hb.2 lt_dhi.le hLres (by nlinarith) (by nlinarith)
          (by push_cast; rw [hone]; nlinarith) (by push_cast; rw [hone]; nlinarith)
        rcases this with ⟨z1, z2⟩ | ⟨z1, z2⟩
        · left; exact ⟨z1, by linarith⟩
        · right; exact ⟨z1, by linarith⟩
    rcases hzone with ⟨z1, z2⟩ | ⟨z1, z2⟩
    · left
      have : 0 ≤ z.1 := by exact_mod_cast z1
      rw [if_pos this]; push_cast; constructor <;> linarith
    · right
      have : 0 ≤ z.2 := by exact_mod_cast z1
      rw [if_pos this]; push_cast; constructor <;> linarith

set_option maxHeartbeats 2000000 in
theorem chF_sound {r k a s d : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (IH : GoSound r)
    (h : Inv k a s xlo xhi rlo rhi zl zr) (hd : d < 2) :
    (chF (go r) s xlo xhi rlo rhi zl zr d : ℝ) ≤ Sum r (k + 1) (2 * a + d) := by
  have h0 := Sum_nonneg r (k + 1) (2 * a + d)
  have hb := half_bounds h.hr1 h.hr2
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have eL : (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 / 2 = (3 : ℝ) ^ pend k / 2 ^ (k + 1) * 2 ^ 90 := by
    rw [show (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]; field_simp
  rw [eL] at hb
  have hres_iff : (3 : ℝ) ^ pend k ≤ 2 * δ3 * 2 ^ (k + 1) ↔
      (3 : ℝ) ^ pend k / 2 ^ (k + 1) * 2 ^ 90 ≤ 2 * (δ3 * 2 ^ 90) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    constructor <;> intro h' <;> nlinarith [(by positivity : (0 : ℝ) < 2 ^ 90)]
  unfold chF
  dsimp only
  by_cases h99 : step s d = 99
  · rw [if_pos h99]; exact_mod_cast h0
  rw [if_neg h99]
  have K1 := fun hr => kid_res (r := r) IH h hd h99 hr
  have K2 := fun hu => kid_unres (r := r) IH h hd h99 hu
  generalize (if d = 0 then xlo else xlo + rlo / 2) = cxlo at K1 K2 ⊢
  generalize (if d = 0 then xhi else xhi + (rhi + 1) / 2) = cxhi at K1 K2 ⊢
  generalize (if d = 0 then zl else if rlo / 2 ≤ zl then zl - rlo / 2 else -1) = czl at K1 K2 ⊢
  generalize (if d = 0 then (if rlo / 2 ≤ zr then zr - rlo / 2 else -1) else zr) = czr at K1 K2 ⊢
  split_ifs with hz hres hun
  · exact_mod_cast h0
  · refine K1 (hres_iff.2 ?_)
    have : (((rhi + 1) / 2 : ℤ) : ℝ) ≤ 2 * (dlo : ℝ) := by exact_mod_cast hres
    linarith [dlo_lt, hb.2]
  · refine K2 ?_
    have : 2 * (dhi : ℝ) < ((rlo / 2 : ℤ) : ℝ) := by exact_mod_cast hun
    by_contra hc
    push Not at hc
    have := (hres_iff.1 (by linarith [pend_spec k]))
    linarith [lt_dhi, hb.1]
  · push_cast
    rcases le_or_gt ((3 : ℝ) ^ pend k) (2 * δ3 * 2 ^ (k + 1)) with hr | hr
    · exact (min_le_left _ _).trans (K1 hr)
    · exact (min_le_right _ _).trans (K2 hr)

theorem Sum_succ (r k a : ℕ) : Sum (r + 1) k a = Sum r (k + 1) (2 * a + 0) + Sum r (k + 1) (2 * a + 1) := by
  unfold Sum
  rw [pow_succ, mul_two, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show k + (r + 1) = k + 1 + r by ring, show (2 ^ r + 2 ^ r) * a + j = 2 ^ r * (2 * a + 0) + j by ring]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show k + (r + 1) = k + 1 + r by ring,
      show (2 ^ r + 2 ^ r) * a + (2 ^ r + j) = 2 ^ r * (2 * a + 1) + j by ring]

theorem go_sound : ∀ r, GoSound r
  | 0 => by
    intro k a s xlo xhi rlo rhi zl zr h
    simp only [go]
    split_ifs with hz
    · exact_mod_cast Sum_nonneg 0 k a
    · push Not at hz
      have hg := good_of_inv h hz.1 hz.2
      unfold Sum
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton, one_mul, add_zero]
      rw [if_pos (by simpa using hg)]
      exact_mod_cast leafmin_le h
  | r + 1 => by
    intro k a s xlo xhi rlo rhi zl zr h
    simp only [go]
    rw [Sum_succ]
    push_cast
    exact add_le_add (chF_sound (go_sound r) h (by norm_num)) (chF_sound (go_sound r) h (by norm_num))

theorem inv_split_x {k a s : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (h : Inv k a s xlo xhi rlo rhi zl zr)
    (mid : ℤ) : Inv k a s xlo mid rlo rhi zl zr ∨ Inv k a s mid xhi rlo rhi zl zr := by
  obtain ⟨m, h1, h2⟩ := h.hx
  rcases le_total (((3 : ℝ) ^ pend k * a / 2 ^ k - m) * 2 ^ 90) (mid : ℝ) with hm | hm
  · exact Or.inl { h with hx := ⟨m, h1, hm⟩ }
  · exact Or.inr { h with hx := ⟨m, hm, h2⟩ }

theorem inv_split_r {k a s : ℕ} {xlo xhi rlo rhi zl zr : ℤ} (h : Inv k a s xlo xhi rlo rhi zl zr)
    (mid : ℤ) (hmid : 0 ≤ mid) : Inv k a s xlo xhi rlo mid zl zr ∨ Inv k a s xlo xhi mid rhi zl zr := by
  rcases le_total ((3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90) (mid : ℝ) with hm | hm
  · exact Or.inl { h with hr2 := hm }
  · exact Or.inr { h with hr1 := hm, hrlo := hmid }

/-- **Branch and bound is sound**: if `bb` reaches the target, every realized cell does. -/
theorem bb_sound : ∀ (f s : ℕ) (xlo xhi rlo rhi tgt : ℤ), tgt ≤ bb f s xlo xhi rlo rhi tgt →
    ∀ k a, Inv k a s xlo xhi rlo rhi (-1) (-1) → (tgt : ℝ) ≤ Sum D k a
  | 0, s, xlo, xhi, rlo, rhi, tgt, hb, k, a, h => by
    simp only [bb] at hb
    exact (Int.cast_le.2 hb).trans (go_sound D _ _ _ _ _ _ _ _ _ h)
  | f + 1, s, xlo, xhi, rlo, rhi, tgt, hb, k, a, h => by
    have hmid : 0 ≤ (rlo + rhi) / 2 / 2 ^ 20 * 2 ^ 20 := by
      have := h.hrlo
      have hr : rlo ≤ rhi := by
        have := h.hr1.trans h.hr2; exact_mod_cast this
      have : 0 ≤ (rlo + rhi) / 2 / 2 ^ 20 := Int.ediv_nonneg (Int.ediv_nonneg (by omega) (by norm_num))
        (by norm_num)
      positivity
    simp only [bb] at hb
    by_cases hf : f % 3 ≠ 0
    · simp only [hf, if_true, ne_eq, not_false_eq_true] at hb
      split_ifs at hb with hv ha
      · exact (Int.cast_le.2 hb).trans (go_sound D _ _ _ _ _ _ _ _ _ h)
      · exact absurd (lt_of_le_of_lt hb ha) (lt_irrefl _)
      · have hA := le_min_iff.1 hb
        rcases inv_split_x h ((xlo + xhi) / 2) with h' | h'
        · exact bb_sound f s _ _ _ _ tgt hA.1 k a h'
        · exact bb_sound f s _ _ _ _ tgt hA.2 k a h'
    · simp only [hf, if_false, ne_eq, not_true_eq_false, not_not] at hb
      split_ifs at hb with hv ha
      · exact (Int.cast_le.2 hb).trans (go_sound D _ _ _ _ _ _ _ _ _ h)
      · exact absurd (lt_of_le_of_lt hb ha) (lt_irrefl _)
      · have hA := le_min_iff.1 hb
        rcases inv_split_r h _ hmid with h' | h'
        · exact bb_sound f s _ _ _ _ tgt hA.1 k a h'
        · exact bb_sound f s _ _ _ _ tgt hA.2 k a h'

/-- In a strictly increasing list, the elements below `x` form a prefix. -/
theorem sorted_count (x : ℚ) : ∀ (l : List ℤ), l.Pairwise (· < ·) →
    let j := (l.filter (fun (e : ℤ) => decide ((e : ℚ) < x))).length
    (∀ i (hi : i < j), ((l[i]'(by have := List.length_filter_le (fun (e : ℤ) => decide ((e : ℚ) < x)) l; omega) : ℤ) : ℚ) < x) ∧
      ∀ (hj : j < l.length), x ≤ ((l[j] : ℤ) : ℚ)
  | [], _ => by simp
  | e :: l, hs => by
    intro j
    have hs' := List.pairwise_cons.1 hs
    by_cases he : (e : ℚ) < x
    · have ih := sorted_count x l hs'.2
      have hj : j = (l.filter (fun (e : ℤ) => decide ((e : ℚ) < x))).length + 1 := by
        simp [j, List.filter_cons, he]
      refine ⟨fun i hi => ?_, fun hjl => ?_⟩
      · cases i with
        | zero => simpa using he
        | succ i => simpa using ih.1 i (by omega)
      · simp only [List.length_cons] at hjl
        have := ih.2 (by omega)
        simp only [hj, List.getElem_cons_succ]; exact this
    · have h0 : j = 0 := by
        simp only [j, List.filter_cons, he, decide_false]
        simp only [Bool.false_eq_true, if_false, List.length_eq_zero_iff, List.filter_eq_nil_iff,
          decide_eq_true_eq, not_lt]
        intro b hb
        have := hs'.1 b hb
        push Not at he
        have : (e : ℚ) < b := by exact_mod_cast this
        linarith
      refine ⟨fun i hi => absurd hi (by omega), fun _ => ?_⟩
      simp only [h0, List.getElem_cons_zero]; push Not at he; exact he

theorem edges_sorted : edges.toList.Pairwise (· < ·) := by
  native_decide

theorem edges_pos : edges.all (fun e => decide (0 ≤ e)) = true := by native_decide

theorem edges_size : edges.size = M - 1 := by native_decide

theorem redge_nonneg (j : ℕ) : 0 ≤ redge j := by
  unfold redge
  split_ifs
  · unfold dlo; norm_num
  · unfold dhi; norm_num
  · by_cases hj : j - 1 < edges.size
    · rw [getElem!_pos edges _ hj]
      have := Array.all_eq_true.1 edges_pos (j - 1) hj; simpa using this
    · rw [getElem!_neg edges _ hj]; rfl

theorem len_le_six {k : ℕ} (hk : 5 ≤ k) : (3 : ℝ) ^ pend k ≤ 6 * δ3 * 2 ^ k := by
  rcases Nat.eq_zero_or_pos (pend k) with h0 | hpos
  · rw [h0, pow_zero]
    have h32 : (32 : ℝ) ≤ 2 ^ k := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk; norm_num at this; linarith
    have := δ3_bounds.1
    nlinarith
  · have := pend_min (Nat.sub_lt hpos one_pos)
    have e : (3 : ℝ) ^ pend k = 3 * 3 ^ (pend k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]; linarith

theorem jbin_lt (k : ℕ) : jbin k ≤ M - 1 := by
  unfold jbin; rw [← edges_size]; simpa using List.length_filter_le _ edges.toList

theorem jbin_box {k : ℕ} (hk : 5 ≤ k) :
    (redge (jbin k) : ℝ) ≤ (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 ∧
      (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 ≤ redge (jbin k + 1) := by
  set x : ℚ := (3 : ℚ) ^ pend k / 2 ^ k * 2 ^ 90 with hx
  have hxr : ((x : ℚ) : ℝ) = (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 := by rw [hx]; push_cast; ring
  obtain ⟨h1, h2⟩ := sorted_count x edges.toList edges_sorted
  have hj : jbin k = (edges.toList.filter (fun (e : ℤ) => decide ((e : ℚ) < x))).length := rfl
  have hk2 : (0 : ℝ) < 2 ^ k := by positivity
  have hL1 : 2 * δ3 * 2 ^ 90 < (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 := by
    have := pend_spec k
    rw [div_mul_eq_mul_div, lt_div_iff₀ hk2]; nlinarith
  have hL2 : (3 : ℝ) ^ pend k / 2 ^ k * 2 ^ 90 ≤ 6 * δ3 * 2 ^ 90 := by
    have := len_le_six hk
    rw [div_mul_eq_mul_div, div_le_iff₀ hk2]; nlinarith
  have hMs : edges.toList.length = 23 := by simp [edges_size, M]
  constructor
  · unfold redge
    by_cases h0 : jbin k = 0
    · rw [if_pos h0]; push_cast; linarith [dlo_lt]
    · have hjM : jbin k ≠ M := by have := jbin_lt k; unfold M at *; omega
      rw [if_neg h0, if_neg hjM]
      have hlt : jbin k - 1 < edges.size := by have := jbin_lt k; rw [edges_size]; omega
      rw [getElem!_pos edges _ hlt]
      have := h1 (jbin k - 1) (by rw [← hj]; omega)
      rw [← hxr]
      have : (((edges.toList[jbin k - 1]'(by rw [hMs]; rw [edges_size] at hlt; unfold M at hlt; omega)) : ℤ) : ℝ) < (x : ℝ) := by
        exact_mod_cast this
      simpa using this.le
  · unfold redge
    rw [if_neg (by omega)]
    by_cases hM : jbin k + 1 = M
    · rw [if_pos hM]; push_cast; linarith [lt_dhi]
    · rw [if_neg hM]
      have hlt : jbin k + 1 - 1 < edges.size := by have := jbin_lt k; rw [edges_size]; unfold M at *; omega
      rw [getElem!_pos edges _ hlt]
      have h2' := h2 (by rw [← hj, hMs]; have := jbin_lt k; unfold M at *; omega)
      simp only [← hj] at h2'
      rw [← hxr]
      have : (x : ℝ) ≤ (((edges.toList[jbin k]'(by rw [hMs]; have := jbin_lt k; unfold M at *; omega)) : ℤ) : ℝ) := by
        exact_mod_cast h2'
      simpa using this

theorem ibin_lt (k a : ℕ) : ibin k a < N := by
  unfold ibin
  rw [Nat.floor_lt (by positivity)]
  have := Int.fract_lt_one ((3 : ℚ) ^ pend k * a / 2 ^ k)
  have hN : (N : ℚ) = 128 := by norm_num [N]
  push_cast; rw [hN]; nlinarith

theorem inv_of_good {k a : ℕ} (hk : 5 ≤ k) (hg : Good449 k a) (hs : sftRun k a ≠ 99) :
    Inv k a (sftRun k a) (Int.ofNat (ibin k a) * one / Int.ofNat N)
      ((Int.ofNat (ibin k a) + 1) * one / Int.ofNat N) (redge (jbin k)) (redge (jbin k + 1)) (-1) (-1) := by
  obtain ⟨jb1, jb2⟩ := jbin_box hk
  set Pq : ℚ := (3 : ℚ) ^ pend k * a / 2 ^ k with hPq
  have hPr : ((Pq : ℚ) : ℝ) = (3 : ℝ) ^ pend k * a / 2 ^ k := by rw [hPq]; push_cast; ring
  have hdiv : ∀ i : ℤ, i * one / Int.ofNat N = i * 2 ^ 83 := by
    intro i; unfold one F N
    rw [show (2 : ℤ) ^ 90 = 2 ^ 83 * 128 by norm_num, ← mul_assoc]
    exact Int.mul_ediv_cancel _ (by norm_num)
  have hf0 := Int.fract_nonneg Pq
  have hfl := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℚ) ≤ (N : ℚ)) hf0)
  have hfu := Nat.lt_floor_add_one ((N : ℚ) * Int.fract Pq)
  have hN : (N : ℚ) = 128 := by norm_num [N]
  refine ⟨hk, redge_nonneg _, hg.1, rfl, hs, ⟨⌊Pq⌋, ?_, ?_⟩, jb1, jb2, ?_⟩
  · rw [hdiv, ← hPr]
    have : ((ibin k a : ℚ)) ≤ 128 * Int.fract Pq := by unfold ibin; rw [← hPq, ← hN]; exact hfl
    have h' : ((ibin k a : ℝ)) ≤ 128 * ((Int.fract Pq : ℚ) : ℝ) := by exact_mod_cast this
    rw [Int.fract] at h'
    simp only [Int.ofNat_eq_natCast, Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_one,
      Int.cast_pow, Int.cast_ofNat]
    push_cast at h'
    nlinarith
  · rw [hdiv, ← hPr]
    have : 128 * Int.fract Pq < (ibin k a : ℚ) + 1 := by unfold ibin; rw [← hPq, ← hN]; exact hfu
    have h' : 128 * ((Int.fract Pq : ℚ) : ℝ) < (ibin k a : ℝ) + 1 := by exact_mod_cast this
    rw [Int.fract] at h'
    simp only [Int.ofNat_eq_natCast, Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_one,
      Int.cast_pow, Int.cast_ofNat]
    push_cast at h'
    nlinarith
  · intro n' hn' A t ht hw
    exact absurd hw (Set.disjoint_left.1 (hg.2.2 n' A (pend_min hn')) ht)

theorem sftRun_lt {k a : ℕ} (h : sftRun k a ≠ 99) : sftRun k a < 25 := by
  have hall : ∀ s < 25, ∀ d < 2, sftStep s d = 99 ∨ sftStep s d < 25 := by decide
  induction k generalizing a with
  | zero => simp [sftRun]
  | succ k ih =>
    simp only [sftRun] at h ⊢
    split_ifs at h ⊢ with h1
    · exact absurd rfl h
    · rcases hall _ (ih h1) (a % 2) (Nat.mod_lt _ (by norm_num)) with h2 | h2
      · exact absurd h2 h
      · exact h2

/-- The bin index of a cell. -/
noncomputable def binIdx (k a : ℕ) : ℕ := sftRun k a * N * M + ibin k a * M + jbin k

theorem binIdx_lt {k a : ℕ} (h : sftRun k a ≠ 99) : binIdx k a < 76800 := by
  have h1 := sftRun_lt h; have h2 := ibin_lt k a; have h3 := jbin_lt k
  unfold binIdx; unfold N M at *; nlinarith

theorem checkRange_spec {a b : ℕ} (h : checkRange a b = true) {q : ℕ} (h1 : a ≤ q) (h2 : q < b) :
    checkBin q = true := by
  unfold checkRange at h
  rw [List.all_eq_true] at h
  have := h (q - a) (List.mem_range.2 (by omega))
  rwa [show a + (q - a) = q by omega] at this

/-- **Growth of a good cell** from the bin check. -/
theorem grow_good {k a : ℕ} (hk : 5 ≤ k) (hg : Good449 k a) (hs : sftRun k a ≠ 99)
    (hc : checkBin (binIdx k a) = true) : (9 : ℝ) ^ D * Wc k a ≤ 5 ^ D * Sum D k a := by
  have hq := binIdx_lt hs
  have e1 : binIdx k a / (N * M) = sftRun k a := by
    have := ibin_lt k a; have := jbin_lt k; unfold binIdx; unfold N M at *; omega
  have e2 : binIdx k a / M % N = ibin k a := by
    have := ibin_lt k a; have := jbin_lt k; unfold binIdx; unfold N M at *; omega
  have e3 : binIdx k a % M = jbin k := by
    have := ibin_lt k a; have := jbin_lt k; unfold binIdx; unfold N M at *; omega
  have eW : W[binIdx k a]! = Wc k a := by unfold Wc wt binIdx; rfl
  unfold checkBin at hc
  simp only [e1, e2, e3, eW, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  have hS := Sum_nonneg D k a
  rcases hc with h0 | hc
  · rw [h0]; simp; positivity
  · set w := Wc k a
    set tgt := (9 ^ D * w + 5 ^ D - 1) / 5 ^ D
    set v := bb MAXB (sftRun k a) (Int.ofNat (ibin k a) * one / Int.ofNat N)
      ((Int.ofNat (ibin k a) + 1) * one / Int.ofNat N) (redge (jbin k)) (redge (jbin k + 1)) tgt
    have hD : (5 : ℤ) ^ D = 15625 := by norm_num [D]
    have hD9 : (9 : ℤ) ^ D = 531441 := by norm_num [D]
    have ht1 : tgt ≤ v := by
      have := Int.ediv_mul_le (9 ^ D * w + 5 ^ D - 1) (show (5 : ℤ) ^ D ≠ 0 by positivity)
      rw [hD, hD9] at this hc; simp only [tgt, hD, hD9] at *
      nlinarith
    have ht2 : 9 ^ D * w ≤ 5 ^ D * tgt := by
      have := Int.lt_ediv_add_one_mul_self (9 ^ D * w + 5 ^ D - 1) (show (0 : ℤ) < 5 ^ D by positivity)
      simp only [tgt, hD, hD9] at *; nlinarith
    have hsound := bb_sound MAXB _ _ _ _ _ tgt ht1 k a (inv_of_good hk hg hs)
    have : ((9 ^ D * w : ℤ) : ℝ) ≤ ((5 ^ D * tgt : ℤ) : ℝ) := by exact_mod_cast ht2
    push_cast at this
    calc (9 : ℝ) ^ D * Wc k a ≤ 5 ^ D * tgt := this
      _ ≤ 5 ^ D * Sum D k a := mul_le_mul_of_nonneg_left hsound (by positivity)

/-- Largest certificate weight (normalization). -/
def maxW : ℤ := 1072633893121

/-- The `ρ`-bin at level 6 (`ρ = 2^-6`). -/
def J0 : ℕ := (edges.toList.filter (fun (e : ℤ) => decide ((e : ℚ) < 2 ^ 84))).length

/-- Weighted count of the SFT-alive level-6 cells (the root block). -/
def rootSum : ℤ := ∑ j ∈ (Finset.range 64).filter (fun j => sftRun 6 j ≠ 99), wt (sftRun 6 j) (2 * j) J0

theorem pend6 : pend 6 = 0 := by
  unfold pend
  rw [Nat.find_eq_zero]
  have := δ3_bounds.2
  norm_num at this ⊢; linarith

theorem good6 {j : ℕ} (hj : j < 64) (h : sftRun 6 j ≠ 99) : Good449 6 j := by
  refine ⟨by norm_num; exact hj, (acc2_of_sftRun 6 j h).2, fun n A hn => ?_⟩
  exfalso
  have h1 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have := δ3_bounds.2
  norm_num at this hn; linarith

theorem Wc6 {j : ℕ} (hj : j < 64) : Wc 6 j = wt (sftRun 6 j) (2 * j) J0 := by
  unfold Wc
  congr 1
  · unfold ibin
    rw [pend6, pow_zero, one_mul]
    have h0 : (0 : ℚ) ≤ (j : ℚ) / 2 ^ 6 := by positivity
    have h1 : (j : ℚ) / 2 ^ 6 < 1 := by
      rw [div_lt_one (by norm_num)]; exact_mod_cast (show j < 2 ^ 6 by norm_num; exact hj)
    rw [Int.fract_eq_self.2 ⟨h0, h1⟩]
    have : (N : ℚ) * ((j : ℚ) / 2 ^ 6) = ((2 * j : ℕ) : ℚ) := by norm_num [N]; ring
    rw [this, Nat.floor_natCast]
  · unfold jbin J0
    rw [pend6]; norm_num

theorem rootSum_le : (rootSum : ℝ) ≤ Sum D 0 0 := by
  unfold rootSum Sum
  rw [Finset.sum_filter]
  push_cast
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j < 64 := by simpa [D] using hj
  rw [show (0 : ℕ) + D = 6 from rfl, show 2 ^ D * 0 + j = j by simp]
  by_cases h1 : sftRun 6 j ≠ 99
  · rw [if_pos h1, if_pos (good6 hj' h1), Wc6 hj']
  · rw [if_neg h1]
    split_ifs
    · exact_mod_cast (show (0 : ℤ) ≤ Wc 6 j from wt_nonneg _ _ _)
    · exact le_rfl

open Classical in
/-- The certificate's classifier: the root, the bin of a good live regular cell, else zero. -/
noncomputable def classify (k a : ℕ) : Fin 76802 :=
  if k = 0 ∧ a = 0 then ⟨76801, by norm_num⟩
  else if h : 5 ≤ k ∧ Good449 k a ∧ sftRun k a ≠ 99 then ⟨binIdx k a, by have := binIdx_lt h.2.2; omega⟩
  else ⟨76800, by norm_num⟩

/-- The certificate's weights. -/
def wq (q : Fin 76802) : ℚ :=
  if q.val < 76800 then (W[q.val]! : ℚ) / maxW else if q.val = 76801 then 1 else 0

theorem maxW_pos : (0 : ℚ) < maxW := by norm_num [maxW]

theorem wq_nonneg (q : Fin 76802) : 0 ≤ wq q := by
  unfold wq; split_ifs
  · exact div_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ W[q.val]! from by
      have := wt_nonneg 0 0 q.val; unfold wt at this; simpa [N, M] using this)) maxW_pos.le
  · norm_num
  · norm_num

theorem w_cls (hWsize : W.size = 76800) {k a : ℕ} (hk : 5 ≤ k) (hg : Good449 k a) :
    ((wq (classify k a) : ℚ) : ℝ) = (Wc k a : ℝ) / maxW := by
  unfold classify
  rw [if_neg (by omega)]
  by_cases hs : sftRun k a ≠ 99
  · rw [dif_pos ⟨hk, hg, hs⟩]
    unfold wq
    simp only [if_pos (binIdx_lt hs)]
    push_cast
    unfold Wc wt binIdx; rfl
  · rw [dif_neg (by tauto)]
    push Not at hs
    have : Wc k a = 0 := by
      unfold Wc wt
      rw [getElem!_neg]; · rfl
      rw [hs, hWsize]; unfold N M; omega
    rw [this]; unfold wq; norm_num

open Classical in
theorem cleanCertificate449_of_data (hAll : ∀ q < 76800, checkBin q = true)
    (hWsize : W.size = 76800) (hWmax : W.all (fun x => decide (x ≤ maxW)) = true)
    (hRoot : 531441 * maxW ≤ 15625 * rootSum) : CleanCertificate449 := by
  have hmax : (0 : ℝ) < maxW := by norm_num [maxW]
  refine ⟨6, by norm_num, by norm_num, 76802, classify, wq, fun q => ⟨wq_nonneg q, ?_⟩, ?_, ?_, ?_⟩
  · unfold wq; split_ifs with h1 h2
    · rw [div_le_one maxW_pos]
      have := Array.all_eq_true.1 hWmax q.val (by rw [hWsize]; exact h1)
      rw [getElem!_pos W _ (by rw [hWsize]; exact h1)]
      exact_mod_cast (by simpa using this)
    · norm_num
    · norm_num
  · unfold classify wq; simp
  · intro k a hng
    unfold classify
    rw [if_neg (fun h => hng (by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by norm_num, fun n m h1 h2 => by omega, fun n A hn => absurd hn (by
        have := δ3_bounds.2
        have h1 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
        norm_num at this ⊢; linarith)⟩))]
    rw [dif_neg (fun h => hng h.2.1)]
    unfold wq; norm_num
  · intro k a hg
    -- the right side in ℝ
    have hR : (((∑ j ∈ (Finset.range (2 ^ 6)).filter (fun j => Good449 (k + 6) (2 ^ 6 * a + j)),
        wq (classify (k + 6) (2 ^ 6 * a + j)) : ℚ)) : ℝ) = Sum D k a / maxW := by
      push_cast
      unfold Sum
      rw [Finset.sum_filter, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show D = 6 from rfl]
      rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
      by_cases h : Good449 (k + 6) (64 * a + j)
      · rw [if_pos h, if_pos h]; exact w_cls hWsize (by omega) h
      · rw [if_neg h, if_neg h]; simp
    have hRn : (0 : ℝ) ≤ Sum D k a / maxW := div_nonneg (Sum_nonneg _ _ _) hmax.le
    rw [← Rat.cast_le (K := ℝ), hR]
    push_cast
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · -- the root
      have ha : a = 0 := by have := hg.1; simpa using this
      subst ha
      have hc : classify 0 0 = ⟨76801, by norm_num⟩ := by unfold classify; simp
      rw [hc]; unfold wq; norm_num
      have h1 := rootSum_le
      have h2 : (531441 : ℝ) * maxW ≤ 15625 * rootSum := by exact_mod_cast hRoot
      rw [le_div_iff₀ hmax]; nlinarith
    · by_cases hk5 : 5 ≤ k
      · rw [w_cls hWsize hk5 hg]
        by_cases hs : sftRun k a ≠ 99
        · have := grow_good hk5 hg hs (hAll _ (binIdx_lt hs))
          rw [show D = 6 from rfl] at this ⊢
          rw [← mul_div_assoc, div_le_div_iff_of_pos_right hmax]
          have e : (9 / 5 : ℝ) ^ 6 * Wc k a = 9 ^ 6 * Wc k a / 5 ^ 6 := by ring
          rw [e, div_le_iff₀ (by norm_num)]; linarith
        · push Not at hs
          have : Wc k a = 0 := by
            unfold Wc wt
            rw [getElem!_neg]; · rfl
            rw [hs, hWsize]; unfold N M; omega
          rw [this]; simpa using hRn
      · have hc : classify k a = ⟨76800, by norm_num⟩ := by
          unfold classify; rw [if_neg (by omega), dif_neg (by omega)]
        rw [hc]; unfold wq; simpa using hRn

end Certificate

theorem W_size : Data.W.size = 76800 := by native_decide

theorem W_le_max : Data.W.all (fun x => decide (x ≤ maxW)) = true := by native_decide

theorem root_ok : 531441 * maxW ≤ 15625 * rootSum := by native_decide

theorem all_checks : ∀ q < 76800, Data.checkBin q = true := by
  intro q hq
  rcases (show q < 9600 ∨ (9600 ≤ q ∧ q < 19200) ∨ (19200 ≤ q ∧ q < 28800) ∨ (28800 ≤ q ∧ q < 38400) ∨
      (38400 ≤ q ∧ q < 48000) ∨ (48000 ≤ q ∧ q < 57600) ∨ (57600 ≤ q ∧ q < 67200) ∨
      (67200 ≤ q ∧ q < 76800) by omega) with h | h | h | h | h | h | h | h
  · exact checkRange_spec Data.checkRange_0 (Nat.zero_le _) h
  · exact checkRange_spec Data.checkRange_1 h.1 h.2
  · exact checkRange_spec Data.checkRange_2 h.1 h.2
  · exact checkRange_spec Data.checkRange_3 h.1 h.2
  · exact checkRange_spec Data.checkRange_4 h.1 h.2
  · exact checkRange_spec Data.checkRange_5 h.1 h.2
  · exact checkRange_spec Data.checkRange_6 h.1 h.2
  · exact checkRange_spec Data.checkRange_7 h.1 h.2

/-- **The crux, proved.**  The exact integer certificate (`c = 449/100`, growth `9/5`, `D = 6`,
`N = 128`, `M = 24`), checked by `native_decide` against the verified checker. -/
theorem cleanCertificate449 : CleanCertificate449 :=
  cleanCertificate449_of_data all_checks W_size W_le_max root_ok

/-- **Operator gate 4.**  A shared-phase finite-state certificate for the {2,3} core at
exponent 449/100, with block growth at least 9/5 over some block length `D ≤ 12`. -/
theorem coherentTwoThree449 : CoherentTwoThree449 :=
  coherentTwoThree449_of_clean cleanCertificate449

end NormalNumbers.UniformBadThreshold.Coherent
