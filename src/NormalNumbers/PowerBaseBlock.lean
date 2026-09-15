/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerBaseLimit

/-!
# Blocking a normal sequence: `IsNormalSequence b s → IsNormalSequence (b^K) (blockOf b K s)`

`tendsto_resCount` is the analytic content; what remains is bookkeeping between a base-`b^K`
word and its base-`b` **flattening**.

* `valOf B w` — the numeric value of the base-`B` word `w`; inverse to `wordOf` on valid words
  (`wordOf_valOf`, `valOf_wordOf`).
* `flat b K w` — replace each base-`b^K` letter by its `K` base-`b` digits.  `flat_wordOf` says
  this is compatible with `wordOf`: `flat b K (wordOf (b^K) ℓ k) = wordOf b (K*ℓ) k`.
* `blockOf b K s j` — the `j`-th base-`b^K` digit of `s`, i.e. the value of the `K`-block of `s`
  starting at `K*j`.
* `matchesAt_blockOf` — `w` occurs in `blockOf` at `j` iff `flat w` occurs in `s` at `K*j`.
* `winCount_blockOf` — hence the window count of `w` is a residue-restricted window count of
  `flat w`, and `tendsto_resCount` finishes.
-/

open Filter Finset

namespace NormalNumbers.PowerBase

open NormalNumbers

/-! ### §1  `wordOf` is a two-sided digit expansion -/

/-- Splitting a word into its high `m₁` and low `m₂` digits. -/
lemma wordOf_split (b m₁ m₂ k : ℕ) :
    wordOf b (m₁ + m₂) k = wordOf b m₁ (k / b ^ m₂) ++ wordOf b m₂ k := by
  rw [wordOf, wordOf, wordOf, List.range_add, List.map_append]
  congr 1
  · refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 3
    omega
  · rw [List.map_map]
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    congr 3
    omega

/-- `wordOf` only sees `k` modulo `b ^ m`. -/
lemma wordOf_mod (b m k : ℕ) (hb : 0 < b) : wordOf b m (k % b ^ m) = wordOf b m k := by
  rw [wordOf, wordOf]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  have hsplit : b ^ m = b ^ (m - 1 - j) * b ^ (m - (m - 1 - j)) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self b (by omega))

/-- The numeric value of a base-`B` word. -/
def valOf (B : ℕ) (w : List ℕ) : ℕ := w.foldl (fun a d => a * B + d) 0

@[simp] lemma valOf_nil (B : ℕ) : valOf B [] = 0 := rfl

lemma valOf_append (B : ℕ) (w : List ℕ) (d : ℕ) :
    valOf B (w ++ [d]) = valOf B w * B + d := by
  simp [valOf]

lemma valOf_lt {B : ℕ} (hB : 0 < B) (w : List ℕ) (hw : ∀ d ∈ w, d < B) :
    valOf B w < B ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simpa using hB
  | append_singleton w d ih =>
      have hw' : ∀ e ∈ w, e < B := fun e he => hw e (by simp [he])
      have hd : d < B := hw d (by simp)
      have h1 := ih hw'
      rw [valOf_append, List.length_append, List.length_singleton, pow_succ]
      calc valOf B w * B + d < valOf B w * B + B := by omega
        _ = (valOf B w + 1) * B := by ring
        _ ≤ B ^ w.length * B := Nat.mul_le_mul_right B h1

lemma wordOf_valOf {B : ℕ} (hB : 0 < B) (w : List ℕ) (hw : ∀ d ∈ w, d < B) :
    wordOf B w.length (valOf B w) = w := by
  induction w using List.reverseRecOn with
  | nil => simp [valOf]
  | append_singleton w d ih =>
      have hw' : ∀ e ∈ w, e < B := fun e he => hw e (by simp [he])
      have hd : d < B := hw d (by simp)
      rw [List.length_append, List.length_singleton, valOf_append,
        wordOf_append B w.length (valOf B w) d hB hd, ih hw']

lemma valOf_wordOf {B : ℕ} (hB : 0 < B) (m k : ℕ) (hk : k < B ^ m) :
    valOf B (wordOf B m k) = k := by
  induction m generalizing k with
  | zero =>
      have : k = 0 := by simpa using hk
      subst this
      simp [valOf]
  | succ m ih =>
      have hd : k % B < B := Nat.mod_lt _ hB
      have hdec : k / B * B + k % B = k := Nat.div_add_mod' k B
      have hq : k / B < B ^ m := by
        rw [pow_succ] at hk
        exact (Nat.div_lt_iff_lt_mul hB).2 hk
      have key := wordOf_append B m (k / B) (k % B) hB hd
      rw [hdec] at key
      rw [key, valOf_append, ih (k / B) hq, hdec]

/-! ### §2  Flattening -/

/-- Replace each base-`b^K` letter by its `K` base-`b` digits. -/
def flat (b K : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: w => wordOf b K d ++ flat b K w

@[simp] lemma length_flat (b K : ℕ) (w : List ℕ) : (flat b K w).length = K * w.length := by
  induction w with
  | nil => simp [flat]
  | cons d w ih => simp [flat, ih]; ring

lemma flat_wordOf (b K : ℕ) (hb : 0 < b) (ℓ k : ℕ) :
    flat b K (wordOf (b ^ K) ℓ k) = wordOf b (K * ℓ) k := by
  induction ℓ generalizing k with
  | zero => simp [flat]
  | succ ℓ ih =>
      have h1 : ∀ x : ℕ, wordOf (b ^ K) 1 x = [x % b ^ K] := by
        intro x; simp [wordOf]
      have hstep : ℓ + 1 = 1 + ℓ := by omega
      rw [hstep, wordOf_split (b ^ K) 1 ℓ k, h1]
      simp only [List.singleton_append, flat]
      rw [ih, wordOf_mod b K _ hb]
      have hpow : (b ^ K) ^ ℓ = b ^ (K * ℓ) := by rw [← pow_mul]
      rw [hpow, show K * (1 + ℓ) = K + K * ℓ by ring, wordOf_split b K (K * ℓ) k]

/-! ### §3  Matching -/

lemma matchesAt_append_list (s : ℕ → ℕ) (u v : List ℕ) (p : ℕ) :
    MatchesAt s (u ++ v) p ↔ MatchesAt s u p ∧ MatchesAt s v (p + u.length) := by
  have hleft : ∀ j, j < u.length → (u ++ v).getD j 0 = u.getD j 0 := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have hright : ∀ j, (u ++ v).getD (u.length + j) 0 = v.getD j 0 := by
    intro j
    simp [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right u.length j)]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h j (by simp; omega)
      rwa [hleft j hj] at this
    · have := h (u.length + j) (by simp; omega)
      rw [hright j] at this
      rw [show p + u.length + j = p + (u.length + j) by ring]
      exact this
  · rintro ⟨h1, h2⟩ j hj
    simp only [List.length_append] at hj
    rcases Nat.lt_or_ge j u.length with hlt | hge
    · rw [hleft j hlt]; exact h1 j hlt
    · obtain ⟨j', rfl⟩ : ∃ j', j = u.length + j' := ⟨j - u.length, by omega⟩
      rw [hright j']
      have := h2 j' (by omega)
      rw [show p + (u.length + j') = p + u.length + j' by ring]
      exact this

/-- The `j`-th base-`b^K` digit of `s`. -/
def blockOf (b K : ℕ) (s : ℕ → ℕ) (j : ℕ) : ℕ :=
  valOf b ((List.range K).map (fun t => s (K * j + t)))

lemma matchesAt_block {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : ∀ j, s j < b) (d j : ℕ)
    (hd : d < b ^ K) :
    MatchesAt s (wordOf b K d) (K * j) ↔ blockOf b K s j = d := by
  classical
  set L : List ℕ := (List.range K).map (fun t => s (K * j + t)) with hL
  have hLlen : L.length = K := by simp [hL]
  have hLget : ∀ t, t < K → L.getD t 0 = s (K * j + t) := by
    intro t ht
    simp [hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
  have hLdig : ∀ e ∈ L, e < b := by
    intro e he
    rw [hL, List.mem_map] at he
    obtain ⟨t, -, rfl⟩ := he
    exact hs _
  have hiff : MatchesAt s (wordOf b K d) (K * j) ↔ L = wordOf b K d := by
    constructor
    · intro h
      refine List.ext_getElem (by simp [hLlen]) fun t h1 h2 => ?_
      have ht : t < K := by rw [hLlen] at h1; exact h1
      have hget := h t (by simpa using ht)
      have hL' : L[t] = L.getD t 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
        rfl
      have hR' : (wordOf b K d)[t] = (wordOf b K d).getD t 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
        rfl
      rw [hL', hR', hLget t ht, hget]
    · intro h t ht
      rw [length_wordOf] at ht
      rw [← h, hLget t ht]
  rw [hiff]
  constructor
  · intro h
    rw [blockOf, ← hL, h, valOf_wordOf hb K d hd]
  · intro h
    rw [blockOf, ← hL] at h
    have hkey := wordOf_valOf hb L hLdig
    rw [hLlen, h] at hkey
    exact hkey.symm

lemma matchesAt_blockOf {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : ∀ j, s j < b)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b ^ K) (j : ℕ) :
    MatchesAt (blockOf b K s) w j ↔ MatchesAt s (flat b K w) (K * j) := by
  induction w generalizing j with
  | nil =>
      constructor <;> intro _ t ht <;> simp [flat] at ht
  | cons d w ih =>
      have hd : d < b ^ K := hw d (by simp)
      have hw' : ∀ e ∈ w, e < b ^ K := fun e he => hw e (by simp [he])
      rw [matchesAt_cons, flat, matchesAt_append_list, length_wordOf]
      refine and_congr ?_ ?_
      · exact (matchesAt_block hb hs d j hd).symm
      · rw [ih hw' (j + 1), show K * (j + 1) = K * j + K by ring]

/-! ### §4  Counting, and the theorem -/

lemma winCount_blockOf {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b ^ K) (N : ℕ) :
    winCount (blockOf b K s) w N = resCount K 0 s (flat b K w) (K * N) := by
  classical
  rw [winCount, resCount]
  refine Finset.card_nbij' (fun j => K * j) (fun p => p / K) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨(Nat.mul_lt_mul_left hK).2 hj.1, ?_, ?_⟩
    · simp
    · exact (matchesAt_blockOf hb hs w hw j).1 hj.2
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have hdvd : K * (p / K) = p := by
      have h0 : p % K = 0 := by simpa using hp2
      rw [mul_comm]
      exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h0)
    refine ⟨?_, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hK).2 (by rw [mul_comm]; exact hp1)
    · refine (matchesAt_blockOf hb hs w hw (p / K)).2 ?_
      rw [hdvd]
      exact hp3
  · intro j _
    exact Nat.mul_div_cancel_left j hK
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    have h0 : p % K = 0 := by simpa using hp.2.1
    show K * (p / K) = p
    rw [mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h0)

/-- 🎯 **Blocking preserves normality.** -/
theorem isNormalSequence_pow {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K)
    (hs : ∀ j, s j < b) (hnorm : IsNormalSequence b s) :
    IsNormalSequence (b ^ K) (blockOf b K s) := by
  refine isNormalSequence_of_tendsto_winCount fun w hwne hwb => ?_
  have hBpos : 0 < b ^ K := pow_pos hb K
  have hkl : valOf (b ^ K) w < (b ^ K) ^ w.length := valOf_lt hBpos w hwb
  have hword : wordOf (b ^ K) w.length (valOf (b ^ K) w) = w := wordOf_valOf hBpos w hwb
  set ℓ := w.length with hℓ
  set k := valOf (b ^ K) w with hk
  have hpow : (b ^ K) ^ ℓ = b ^ (K * ℓ) := by rw [← pow_mul]
  have hklt : k < b ^ (K * ℓ) := by rw [← hpow]; exact hkl
  have hflat : flat b K w = wordOf b (K * ℓ) k := by
    conv_lhs => rw [← hword]
    rw [flat_wordOf b K hb]
  have hres := tendsto_resCount hb hK hs hnorm 0 (K * ℓ) k hklt
  have hcomp : Tendsto (fun N : ℕ =>
      (K : ℝ) / (K * N : ℕ) * (resCount K 0 s (wordOf b (K * ℓ) k) (K * N) : ℝ))
      atTop (nhds (1 / (b : ℝ) ^ (K * ℓ))) := by
    refine hres.comp ?_
    refine Filter.tendsto_atTop_atTop.2 fun c => ⟨c, fun n hn => ?_⟩
    calc c ≤ n := hn
      _ ≤ K * n := Nat.le_mul_of_pos_left n hK
  have hgoal : (((b ^ K : ℕ) : ℝ) ^ ℓ)⁻¹ = 1 / (b : ℝ) ^ (K * ℓ) := by
    push_cast
    rw [← pow_mul]
    ring
  rw [hgoal]
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hcast : ((K * N : ℕ) : ℝ) = (K : ℝ) * N := by push_cast; ring
  rw [hcast, ← hflat, ← winCount_blockOf hb hK hs w hwb N]
  field_simp

end NormalNumbers.PowerBase
