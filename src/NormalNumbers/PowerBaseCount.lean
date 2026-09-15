/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyOcc
import NormalNumbers.BlockRigidity

/-!
# Counting a word at positions in a residue class

The combinatorial layer of **"normal to base `b` ⇒ normal to base `b^K`"**.  A base-`b^K` digit of
a sequence is a `K`-block of base-`b` digits at a position `≡ 0 (mod K)`, so what has to be counted
is `resCount K c s v n`, the occurrences of `v` at positions `p < n` with `p ≡ c (mod K)`.

Three exact relations drive everything (`BlockRigidity.Sys` is built from them):

* `resCount_append` — refining on the right is a **partition**: no boundary loss at all, because
  `MatchesAt` does not require the window to fit inside `[0, n)`.
* `resCount_prepend_bounds` — prepending shifts the class by one, to within `1`.
* `sum_resCount` — the `K` classes partition the unrestricted `winCount`.

`wordOf b m k` is the base-`b` word of length `m` and numeric value `k`; `wordOf_append` and
`wordOf_cons` say that the two numeric operations of `BlockRigidity.Sys` (`k ↦ k·b + d` and
`k ↦ t·b^m + k`) are exactly "append a digit" and "prepend a digit".
-/

open Filter Finset

namespace NormalNumbers.PowerBase

open NormalNumbers

/-! ### §1  Words by numeric value -/

/-- The base-`b` word of length `m` with numeric value `k`, most significant digit first. -/
def wordOf (b m k : ℕ) : List ℕ :=
  (List.range m).map (fun j => k / b ^ (m - 1 - j) % b)

@[simp] lemma length_wordOf (b m k : ℕ) : (wordOf b m k).length = m := by
  simp [wordOf]

@[simp] lemma wordOf_zero (b k : ℕ) : wordOf b 0 k = [] := by simp [wordOf]

lemma wordOf_lt (b m k : ℕ) (hb : 0 < b) : ∀ d ∈ wordOf b m k, d < b := by
  intro d hd
  rw [wordOf, List.mem_map] at hd
  obtain ⟨j, -, rfl⟩ := hd
  exact Nat.mod_lt _ hb

/-- Appending a digit is `k ↦ k·b + d`. -/
lemma wordOf_append (b m k d : ℕ) (hb : 0 < b) (hd : d < b) :
    wordOf b (m + 1) (k * b + d) = wordOf b m k ++ [d] := by
  have hkb : (k * b + d) / b = k := by
    rw [mul_comm k b, Nat.mul_add_div hb, Nat.div_eq_of_lt hd, Nat.add_zero]
  rw [wordOf, wordOf, List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    have hstep : m + 1 - 1 - j = (m - 1 - j) + 1 := by omega
    rw [hstep, pow_succ, mul_comm (b ^ (m - 1 - j)) b, ← Nat.div_div_eq_div_mul, hkb]
  · have h0 : m + 1 - 1 - m = 0 := by omega
    simp [h0, Nat.mul_add_mod, Nat.mod_eq_of_lt hd]

/-- Prepending a digit is `k ↦ t·b^m + k`. -/
lemma wordOf_cons (b m k t : ℕ) (hb : 0 < b) (hk : k < b ^ m) (ht : t < b) :
    wordOf b (m + 1) (t * b ^ m + k) = t :: wordOf b m k := by
  rw [wordOf, wordOf, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · have h0 : m + 1 - 1 - 0 = m := by omega
    rw [h0, mul_comm t (b ^ m), Nat.mul_add_div (show 0 < b ^ m by positivity),
      Nat.div_eq_of_lt hk, Nat.add_zero]
    simp [Nat.mod_eq_of_lt ht]
  · refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    have hstep : m + 1 - 1 - (j + 1) = m - 1 - j := by omega
    rw [hstep]
    have hme : t * b ^ m = b ^ (m - 1 - j) * (b * (t * b ^ j)) := by
      have hx : b ^ (m - 1 - j) * (b * (t * b ^ j)) = t * (b ^ (m - 1 - j) * b ^ j * b) := by
        ring
      rw [hx, ← pow_add, ← pow_succ]
      congr 2
      omega
    rw [hme, Nat.mul_add_div (show 0 < b ^ (m - 1 - j) by positivity), Nat.add_comm,
      Nat.add_mul_mod_self_left]

/-! ### §2  `MatchesAt` under appending and prepending -/

lemma matchesAt_append (s : ℕ → ℕ) (v : List ℕ) (d p : ℕ) :
    MatchesAt s (v ++ [d]) p ↔ MatchesAt s v p ∧ s (p + v.length) = d := by
  have hget : ∀ j, j < v.length → (v ++ [d]).getD j 0 = v.getD j 0 := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have hlast : (v ++ [d]).getD v.length 0 = d := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl v.length)]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h j (by simp; omega)
      rwa [hget j hj] at this
    · have := h v.length (by simp)
      rwa [hlast] at this
  · rintro ⟨h1, h2⟩ j hj
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j v.length with hlt | hge
    · rw [hget j hlt]; exact h1 j hlt
    · have hje : j = v.length := by omega
      subst hje
      rw [hlast]
      exact h2

lemma matchesAt_cons (s : ℕ → ℕ) (v : List ℕ) (d p : ℕ) :
    MatchesAt s (d :: v) p ↔ s p = d ∧ MatchesAt s v (p + 1) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
    have := h (j + 1) (by simp; omega)
    have harg : p + (j + 1) = p + 1 + j := by omega
    rwa [harg, List.getD_cons_succ] at this
  · rintro ⟨h0, h1⟩ j hj
    cases j with
    | zero => simpa using h0
    | succ j =>
        simp only [List.length_cons] at hj
        have := h1 j (by omega)
        have harg : p + (j + 1) = p + 1 + j := by omega
        rw [harg, List.getD_cons_succ]
        exact this

/-! ### §3  The residue-restricted count -/

open Classical in
/-- Occurrences of `v` in `s` at positions `p < n` with `p ≡ c (mod K)`. -/
noncomputable def resCount (K c : ℕ) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun p => p % K = c % K ∧ MatchesAt s v p)).card

lemma resCount_le (K c : ℕ) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) : resCount K c s v n ≤ n := by
  classical
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- **Refining on the right is a partition.**  No boundary term: `MatchesAt` never asks the
window to fit inside `[0, n)`. -/
theorem resCount_append {b : ℕ} {s : ℕ → ℕ} (hs : ∀ j, s j < b) (K c : ℕ) (v : List ℕ) (n : ℕ) :
    resCount K c s v n = ∑ d ∈ Finset.range b, resCount K c s (v ++ [d]) n := by
  classical
  rw [resCount]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p => s (p + v.length)) (t := Finset.range b)
    (fun p _ => Finset.mem_range.2 (hs _))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [resCount]
  congr 1
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun p _ => ?_
  rw [matchesAt_append]
  tauto

/-- **The `K` classes partition the unrestricted count.** -/
theorem sum_resCount (K : ℕ) (hK : 0 < K) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) :
    ∑ c ∈ Finset.range K, resCount K c s v n = winCount s v n := by
  classical
  rw [winCount]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p % K) (t := Finset.range K)
    (fun p _ => Finset.mem_range.2 (Nat.mod_lt _ hK))]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [resCount]
  congr 1
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun p _ => ?_
  rw [Finset.mem_range] at hc
  rw [Nat.mod_eq_of_lt hc]
  tauto

/-- **Prepending shifts the class by one**, to within one position. -/
theorem resCount_prepend_bounds {b : ℕ} {s : ℕ → ℕ} (hs : ∀ j, s j < b) {K : ℕ} (hK : 0 < K)
    (c : ℕ) (v : List ℕ) (n : ℕ) :
    (∑ d ∈ Finset.range b, resCount K c s (d :: v) n) ≤ resCount K (c + 1) s v (n + 1) ∧
      resCount K (c + 1) s v (n + 1)
        ≤ (∑ d ∈ Finset.range b, resCount K c s (d :: v) n) + 1 := by
  classical
  set T : Finset ℕ :=
    (Finset.range (n + 1)).filter (fun p => p % K = (c + 1) % K ∧ MatchesAt s v p) with hT
  set U : Finset ℕ :=
    (Finset.range n).filter (fun q => q % K = c % K ∧ MatchesAt s (s q :: v) q) with hU
  have hUcard : U.card = ∑ d ∈ Finset.range b, resCount K c s (d :: v) n := by
    rw [hU, Finset.card_eq_sum_card_fiberwise (f := fun q => s q) (t := Finset.range b)
      (fun q _ => Finset.mem_range.2 (hs _))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [resCount]
    congr 1
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun q _ => ?_
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, by rwa [h3] at h2⟩
    · rintro ⟨h1, h2⟩
      have hd : s q = d := (matchesAt_cons s v d q |>.1 h2).1
      exact ⟨⟨h1, by rwa [hd]⟩, hd⟩
  -- the shift `q ↦ q + 1` embeds `U` into `T`
  have hmaps : ∀ q ∈ U, q + 1 ∈ T := by
    intro q hq
    rw [hU, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    rw [hT, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · exact Nat.ModEq.add_right 1 hq2
    · exact ((matchesAt_cons s v (s q) q).1 hq3).2
  have hinj : ∀ q ∈ U, ∀ q' ∈ U, q + 1 = q' + 1 → q = q' := by
    intro q _ q' _ h; omega
  have hsub : U.card ≤ T.card := Finset.card_le_card_of_injOn (fun q => q + 1) hmaps hinj
  -- conversely every element of `T` except possibly `0` comes from `U`
  have hsurj : ∀ p ∈ T, p ≠ 0 → ∃ q ∈ U, q + 1 = p := by
    intro p hp hp0
    rw [hT, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    refine ⟨p - 1, ?_, by omega⟩
    rw [hU, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · have h' : (p - 1) + 1 ≡ c + 1 [MOD K] := by
        show ((p - 1) + 1) % K = (c + 1) % K
        rw [show p - 1 + 1 = p by omega]
        exact hp2
      exact Nat.ModEq.add_right_cancel' 1 h'
    · rw [matchesAt_cons]
      refine ⟨rfl, ?_⟩
      rw [show p - 1 + 1 = p by omega]
      exact hp3
  have hTle : T.card ≤ U.card + 1 := by
    have hsub2 : T ⊆ insert 0 (U.image (fun q => q + 1)) := by
      intro p hp
      rcases eq_or_ne p 0 with rfl | hp0
      · exact Finset.mem_insert_self _ _
      · obtain ⟨q, hq, rfl⟩ := hsurj p hp hp0
        exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨q, hq, rfl⟩)
    calc T.card ≤ (insert 0 (U.image (fun q => q + 1))).card := Finset.card_le_card hsub2
      _ ≤ (U.image (fun q => q + 1)).card + 1 := Finset.card_insert_le _ _
      _ ≤ U.card + 1 := by
          have := Finset.card_image_le (s := U) (f := fun q => q + 1)
          omega
  rw [resCount, ← hT, ← hUcard]
  exact ⟨hsub, hTle⟩

end NormalNumbers.PowerBase
