/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyLetterGrowth

/-!
# `htail` for the concrete `L/R` transducer, by finiteness of the trigger support

The output engine's last analytic-looking hypothesis is

  `htail : Tendsto (tailMass (kOut δ out v)) atTop (nhds 0)`

— the Gauss mass of the still-live trigger prefixes vanishes (Vandehey's Lemma 4.3
condition (2)).  For the Raney machine it is not analytic at all: the trigger support is
**finite in length**, so `trigPrefix` is literally EMPTY at every length past a bound
depending only on `|v|` and `D`, and `tailMass` is eventually `0`.

## Why the support is bounded

`kOut v q t ≠ 0` says the LAST digit of `q` is what completes some occurrence of `v` that
STARTS in the first emitted block.  Such an occurrence is already complete once the output
reaches `|block₀| + |v|` letters, so the digits strictly between the first and the last must
emit fewer than `|v|` letters between them.  By the lower Lemma 2.2
(`VandeheyLetterGrowth.genuine_length_le`) a genuine word emitting fewer than `|v|` letters has
length `< 2|v| + 2D + 6`.  Hence `|q|` — and so every length at which `q` can contribute a
trigger prefix — is bounded.

Note where genuineness enters: `trigPrefix k t m` only requires the length-`m` PREFIX of `q` to
be genuine, which is exactly enough, since the growth bound is applied to a prefix.
-/

namespace NormalNumbers.VandeheyLR

open Filter Mat2 VandeheyAut VandeheyOut MeasureTheory

variable {D : ℕ}

/-- The output of a prefix is a prefix of the output. -/
lemma blocksOf_take_prefix {S : Type*} [DecidableEq S] (δ : S → ℕ → S) (out : S → ℕ → List ℕ)
    (t : S) (q : List ℕ) (k : ℕ) :
    blocksOf δ out t (q.take k) <+: blocksOf δ out t q := by
  refine ⟨blocksOf δ out (runState δ t (q.take k)) (q.drop k), ?_⟩
  rw [← blocksOf_append, List.take_append_drop]

/-- **The trigger support has bounded length.**  If the last digit of `q` completes an occurrence
of `v` that starts in the first emitted block, then every genuine prefix of `q` is short. -/
theorem length_le_of_kOut_ne_zero (hD : 0 < D) (v q : List ℕ) (t : RState D) (m : ℕ)
    (hm : m ≤ q.length) (hgen : ∀ e ∈ q.take m, 1 ≤ e)
    (hk : kOut (lrDelta hD) (lrOutN hD) v q t ≠ 0) :
    m ≤ 2 * v.length + 2 * D + 6 := by
  classical
  set δ := lrDelta hD with hδ
  set out := lrOutN hD with hout
  by_cases hsmall : m ≤ 2
  · omega
  push_neg at hsmall
  have hq2 : 2 ≤ q.length := le_trans hsmall.le hm
  -- the two occurrence sets
  have hdl1 : q.dropLast.take 1 = q.take 1 := by
    have hmin : min 1 (q.length - 1) = 1 := by omega
    rw [List.dropLast_eq_take, List.take_take, hmin]
  have hmono : occIn δ out v t q.dropLast ≤ occIn δ out v t q := by
    have hq : q ≠ [] := by
      intro h; rw [h] at hq2; simp at hq2
    have := occIn_mono_concat δ out v t q.dropLast (q.getLast hq)
    rwa [List.dropLast_append_getLast hq] at this
  have hlt : occIn δ out v t q.dropLast < occIn δ out v t q := by
    rw [kOut] at hk; omega
  -- a position completed by the last digit
  rw [occIn, occIn, hdl1] at hlt
  have hnsub : ¬ ((Finset.range (blocksOf δ out t (q.take 1)).length).filter
      (fun p => p + v.length ≤ (blocksOf δ out t q).length ∧
        v = ((blocksOf δ out t q).drop p).take v.length)
      ⊆ (Finset.range (blocksOf δ out t (q.take 1)).length).filter
      (fun p => p + v.length ≤ (blocksOf δ out t q.dropLast).length ∧
        v = ((blocksOf δ out t q.dropLast).drop p).take v.length)) := by
    intro hsub
    have h1 := Finset.card_le_card hsub
    omega
  obtain ⟨p, hpA, hpB⟩ := Finset.not_subset.mp hnsub
  simp only [Finset.mem_filter, Finset.mem_range] at hpA hpB
  obtain ⟨hpL, hpfit, hpval⟩ := hpA
  -- the output of `q.dropLast` is a prefix of the output of `q`
  have hpref : blocksOf δ out t q.dropLast <+: blocksOf δ out t q := by
    have hq : q ≠ [] := by
      intro h; rw [h] at hq2; simp at hq2
    have := blocksOf_take_prefix δ out t q (q.length - 1)
    rwa [← List.dropLast_eq_take] at this
  -- so `p` fails only because the occurrence is not yet complete
  have hnotfit : (blocksOf δ out t q.dropLast).length < p + v.length := by
    by_contra hcon
    push_neg at hcon
    refine hpB ⟨hpL, hcon, ?_⟩
    have hEq : List.take v.length (List.drop p (blocksOf δ out t q))
        = List.take v.length (List.drop p (blocksOf δ out t q.dropLast)) := by
      obtain ⟨r, hr⟩ := hpref
      rw [← hr, List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
    rw [← hEq]; exact hpval
  -- split the output of `q.dropLast` after the first digit
  set t' : RState D := runState δ t (q.take 1) with ht'
  set u : List ℕ := q.dropLast.drop 1 with hu
  have hsplit : blocksOf δ out t q.dropLast
      = blocksOf δ out t (q.take 1) ++ blocksOf δ out t' u := by
    rw [← blocksOf_append, ← hdl1, List.take_append_drop]
  have hushort : (blocksOf δ out t' u).length < v.length := by
    rw [hsplit, List.length_append] at hnotfit
    omega
  -- apply the growth bound to the genuine prefix of `u`
  set k : ℕ := m - 2 with hk2
  have hulen : k ≤ u.length := by
    simp only [hu, List.length_drop, List.length_dropLast]
    omega
  have hugen : ∀ e ∈ u.take k, 1 ≤ e := by
    intro e he
    have hmin : min (1 + k) (q.length - 1) = 1 + k := by omega
    have h1 : u.take k = List.drop 1 (List.take (1 + k) q) := by
      simp only [hu, List.dropLast_eq_take, List.take_drop, List.take_take, hmin]
    rw [h1] at he
    have h2 : e ∈ List.take (1 + k) q := List.mem_of_mem_drop he
    have h3 : List.take (1 + k) q = List.take (1 + k) (List.take m q) := by
      rw [List.take_take, min_eq_left (by omega)]
    rw [h3] at h2
    exact hgen e (List.mem_of_mem_take h2)
  have hgrow := genuine_length_le hD t' (u.take k) hugen
  have hlenpref : (blocksOf δ out t' (u.take k)).length ≤ (blocksOf δ out t' u).length :=
    (blocksOf_take_prefix δ out t' u k).length_le
  rw [length_blocksOf_eq hD t' (u.take k)] at hlenpref
  have hklen : (u.take k).length = k := by
    rw [List.length_take]; omega
  rw [hklen] at hgrow
  omega

/-- **`htail` for the `L/R` transducer** — and in the strongest possible form: the tail mass is
not merely vanishing, it is eventually exactly `0`. -/
theorem tailMass_lr_eq_zero (hD : 0 < D) (v : List ℕ) {m : ℕ}
    (hm : 2 * v.length + 2 * D + 6 < m) :
    tailMass (kOut (lrDelta hD) (lrOutN hD) v) m = 0 := by
  classical
  have hempty : ∀ t : RState D, trigPrefix (kOut (lrDelta hD) (lrOutN hD) v) t m = ∅ := by
    intro t
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hlen, hpos, q, hne, hqlen, hqtake⟩
    have hgen : ∀ e ∈ q.take m, 1 ≤ e := by rw [hqtake]; exact hpos
    have := length_le_of_kOut_ne_zero hD v q t m hqlen hgen hne
    omega
  simp only [tailMass, hempty, VandeheyMix.familySetC]
  simp

/-- `htail`, in the form the output engine consumes. -/
theorem lr_htail (hD : 0 < D) (v : List ℕ) :
    Tendsto (tailMass (kOut (lrDelta hD) (lrOutN hD) v)) atTop (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (2 * v.length + 2 * D + 6)] with m hm
  exact (tailMass_lr_eq_zero hD v hm).symm

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms length_le_of_kOut_ne_zero
#print axioms tailMass_lr_eq_zero
#print axioms lr_htail
end
