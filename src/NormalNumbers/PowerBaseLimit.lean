/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerBaseCount

/-!
# The analytic glue: residue-restricted word densities converge

`BlockRigidity.Sys.eq_uniform` is a statement about a *system of numbers* `F m k`.  This module
manufactures that system out of a normal sequence `s`, by taking the limit of

    `Gseq b K c s m k n = (K / n) · resCount K c s (wordOf b m k) n`

**along an arbitrary ultrafilter** `g ≤ atTop`.  The limit exists for free (the sequence lives in
the compact `[0, K]`), the three structural relations of `Sys` survive the limit because the
counting relations of `PowerBaseCount` are exact up to `O(1)`, and the domination `bdd` comes from
normality of `s`.  Rigidity then pins the limit at `b^{-m}` — for *every* ultrafilter, which by
`tendsto_iff_ultrafilter` is genuine convergence:

> 🎯 `tendsto_resCount` : `(K/n) · resCount K c s (wordOf b m k) n → b^{-m}`,

the residue-restricted word density of a base-`b` normal sequence.  This is the whole content of
"normal to base `b` ⇒ normal to base `b^K`"; the remaining work is bookkeeping between a
base-`b^K` word and its base-`b` flattening.
-/

open Filter Finset Topology

namespace NormalNumbers.PowerBase

open NormalNumbers

/-! ### §1  Elementary facts about `resCount` -/

lemma resCount_succ (K c : ℕ) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) :
    resCount K c s v (n + 1)
      = resCount K c s v n + (if n % K = c % K ∧ MatchesAt s v n then 1 else 0) := by
  classical
  rw [resCount, resCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : n % K = c % K ∧ MatchesAt s v n
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

lemma resCount_mono (K c : ℕ) (s : ℕ → ℕ) (v : List ℕ) {m n : ℕ} (h : m ≤ n) :
    resCount K c s v m ≤ resCount K c s v n := by
  classical
  refine Finset.card_le_card fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 h, hp.2⟩

lemma resCount_succ_le (K c : ℕ) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) :
    resCount K c s v (n + 1) ≤ resCount K c s v n + 1 := by
  rw [resCount_succ]
  split <;> omega

lemma resCount_le_winCount (K c : ℕ) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) :
    resCount K c s v n ≤ winCount s v n := by
  classical
  refine Finset.card_le_card fun p hp => ?_
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.2⟩

/-- The empty word is matched everywhere, so `resCount K c s [] n` counts one arithmetic
progression, and `K` times it is `n` to within `K`. -/
lemma resCount_nil_bounds {K : ℕ} (hK : 0 < K) (c : ℕ) (s : ℕ → ℕ) (n : ℕ) :
    K * resCount K c s [] n ≤ n + K ∧ n ≤ K * resCount K c s [] n + K := by
  sorry

/-! ### §2  Normality gives the unrestricted density -/

/-- The converse of `isNormalSequence_of_tendsto_winCount`, for the words `wordOf b m k`
(including the empty word `m = 0`). -/
theorem tendsto_winCount_wordOf {b : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : IsNormalSequence b s)
    (m k : ℕ) :
    Tendsto (fun n => (winCount s (wordOf b m k) n : ℝ) / n) atTop (nhds (((b : ℝ) ^ m)⁻¹)) := by
  sorry

/-! ### §3  The ultrafilter limit -/

/-- The residue-restricted word density at scale `n`. -/
noncomputable def Gseq (b K c : ℕ) (s : ℕ → ℕ) (m k n : ℕ) : ℝ :=
  (K : ℝ) / n * (resCount K c s (wordOf b m k) n : ℝ)

lemma Gseq_nonneg (b K c : ℕ) (s : ℕ → ℕ) (m k n : ℕ) : 0 ≤ Gseq b K c s m k n := by
  unfold Gseq
  positivity

lemma Gseq_le (b K c : ℕ) (s : ℕ → ℕ) (m k n : ℕ) : Gseq b K c s m k n ≤ K := by
  unfold Gseq
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (resCount K c s (wordOf b m k) n : ℝ) ≤ n := by
    exact_mod_cast resCount_le K c s _ n
  rw [div_mul_eq_mul_div, div_le_iff₀ hn']
  nlinarith [Nat.cast_nonneg (α := ℝ) K]

/-- The limit of `Gseq` along an ultrafilter. -/
noncomputable def G (g : Ultrafilter ℕ) (b K c : ℕ) (s : ℕ → ℕ) (m k : ℕ) : ℝ :=
  lim (Filter.map (Gseq b K c s m k) (g : Filter ℕ))

theorem tendsto_G (g : Ultrafilter ℕ) (b K c : ℕ) (s : ℕ → ℕ) (m k : ℕ) :
    Tendsto (Gseq b K c s m k) (g : Filter ℕ) (nhds (G g b K c s m k)) := by
  sorry

/-! ### §4  The three relations in the limit -/

/-- A helper: two sequences that differ by `O(1/n)` have the same ultrafilter limit. -/
lemma eq_of_tendsto_of_close {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) {u v : ℕ → ℝ}
    {x y C : ℝ} (hu : Tendsto u (g : Filter ℕ) (nhds x)) (hv : Tendsto v (g : Filter ℕ) (nhds y))
    (h : ∀ n, 1 ≤ n → |u n - v n| ≤ C / n) : x = y := by
  sorry

lemma G_nonneg (g : Ultrafilter ℕ) (b K c : ℕ) (s : ℕ → ℕ) (m k : ℕ) :
    0 ≤ G g b K c s m k := by
  sorry

lemma G_bdd {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hnorm : IsNormalSequence b s)
    {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) (c m k : ℕ) :
    G g b K c s m k ≤ (K : ℝ) / (b : ℝ) ^ m := by
  sorry

lemma G_unit {K : ℕ} (hK : 0 < K) {b : ℕ} {s : ℕ → ℕ} {g : Ultrafilter ℕ}
    (hg : (g : Filter ℕ) ≤ atTop) (c : ℕ) : G g b K c s 0 0 = 1 := by
  sorry

lemma G_right {b : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : ∀ j, s j < b) (K c : ℕ)
    (g : Ultrafilter ℕ) (m k : ℕ) :
    G g b K c s m k = ∑ d ∈ Finset.range b, G g b K c s (m + 1) (k * b + d) := by
  sorry

lemma G_prepend {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) (c m k : ℕ) (hk : k < b ^ m) :
    G g b K (c + 1) s m k = ∑ d ∈ Finset.range b, G g b K c s (m + 1) (d * b ^ m + k) := by
  sorry

end NormalNumbers.PowerBase
