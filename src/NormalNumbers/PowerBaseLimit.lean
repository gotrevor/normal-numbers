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
  classical
  have hfil : resCount K c s [] n = ((Finset.range n).filter (fun p => p % K = c % K)).card := by
    rw [resCount]
    congr 1
    refine Finset.filter_congr fun p _ => ?_
    simp [MatchesAt]
  rw [hfil]
  set A := ((Finset.range n).filter (fun p => p % K = c % K)).card with hA
  have hKn : n / K * K ≤ n := Nat.div_mul_le_self n K
  have hmod : n % K < K := Nat.mod_lt _ hK
  have hdm : n / K * K + n % K = n := Nat.div_add_mod' n K
  have hup : A ≤ n / K + 1 := by
    rw [hA, ← Finset.card_range (n / K + 1)]
    refine Finset.card_le_card_of_injOn (fun p => p / K) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_coe, Finset.mem_range]
      have h1 : p / K ≤ n / K := Nat.div_le_div_right (le_of_lt hp.1)
      show p / K < n / K + 1
      omega
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      have e1 : K * (p / K) + p % K = p := Nat.div_add_mod p K
      have e2 : K * (q / K) + q % K = q := Nat.div_add_mod q K
      simp only at hpq
      rw [hpq, hp.2] at e1
      rw [hq.2] at e2
      exact e1.symm.trans e2
  have hlow : n / K ≤ A := by
    rw [hA]
    have := Finset.card_le_card_of_injOn (s := Finset.range (n / K))
      (t := (Finset.range n).filter (fun p => p % K = c % K))
      (fun j => c % K + j * K) ?_ ?_
    · rwa [Finset.card_range] at this
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_range] at hj
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have h1 : (j + 1) * K ≤ n / K * K := Nat.mul_le_mul_right K hj
        have hck : c % K < K := Nat.mod_lt _ hK
        calc c % K + j * K = j * K + c % K := by ring
          _ < j * K + K := Nat.add_lt_add_left hck _
          _ = (j + 1) * K := by ring
          _ ≤ n / K * K := h1
          _ ≤ n := hKn
      · simp [Nat.add_mul_mod_self_right, Nat.mod_mod]
    · intro j _ j' _ hjj
      simp only at hjj
      have : j * K = j' * K := by omega
      exact Nat.eq_of_mul_eq_mul_right hK this
  constructor
  · calc K * A ≤ K * (n / K + 1) := Nat.mul_le_mul_left K hup
      _ = n / K * K + K := by ring
      _ ≤ n + K := Nat.add_le_add_right hKn K
  · calc n = n / K * K + n % K := hdm.symm
      _ ≤ K * A + K := by
          have h1 : n / K * K ≤ A * K := Nat.mul_le_mul_right K hlow
          have h2 : A * K = K * A := by ring
          omega

/-! ### §2  Normality gives the unrestricted density -/

/-- The converse of `isNormalSequence_of_tendsto_winCount`, for the words `wordOf b m k`
(including the empty word `m = 0`). -/
theorem tendsto_winCount_wordOf {b : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : IsNormalSequence b s)
    (m k : ℕ) :
    Tendsto (fun n => (winCount s (wordOf b m k) n : ℝ) / n) atTop (nhds (((b : ℝ) ^ m)⁻¹)) := by
  classical
  have hlen : (wordOf b m k).length = m := length_wordOf b m k
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hnil : wordOf b 0 k = [] := wordOf_zero b k
    have hwc : ∀ n, winCount s (wordOf b 0 k) n = n := by
      intro n
      rw [hnil, winCount]
      have : (Finset.range n).filter (MatchesAt s []) = Finset.range n := by
        refine Finset.filter_true_of_mem fun p _ => ?_
        intro j hj
        simp at hj
      rw [this, Finset.card_range]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := ((b : ℝ) ^ 0)⁻¹) (f := atTop))
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      have : 0 < n := hn
      positivity
    rw [hwc n, pow_zero, inv_one, div_self hn']
  · have hne : wordOf b m k ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    have hdig : ∀ d ∈ wordOf b m k, d < b := wordOf_lt b m k hb
    have hco := hs (wordOf b m k) hne hdig
    rw [hlen] at hco
    have hup : Tendsto (fun n : ℕ =>
        (countOccurrences (wordOf b m k) ((List.range n).map s) : ℝ) / n + (m : ℝ) / n)
        atTop (nhds (((b : ℝ) ^ m)⁻¹)) := by
      simpa using hco.add (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hco hup ?_ ?_
    · intro n
      dsimp only
      obtain ⟨h1, -⟩ := card_filter_matchesAt_le s (wordOf b m k) hne n
      have : (countOccurrences (wordOf b m k) ((List.range n).map s) : ℝ)
          ≤ (winCount s (wordOf b m k) n : ℝ) := by
        rw [winCount]; exact_mod_cast h1
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        gcongr
    · intro n
      dsimp only
      obtain ⟨-, h2⟩ := card_filter_matchesAt_le s (wordOf b m k) hne n
      rw [hlen] at h2
      have h2' : (winCount s (wordOf b m k) n : ℝ)
          ≤ (countOccurrences (wordOf b m k) ((List.range n).map s) : ℝ) + m := by
        rw [winCount]
        exact_mod_cast h2
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have hsum : (countOccurrences (wordOf b m k) ((List.range n).map s) : ℝ) / n
            + (m : ℝ) / n
            = ((countOccurrences (wordOf b m k) ((List.range n).map s) : ℝ) + m) / n := by
          ring
        rw [hsum]
        gcongr

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
  have hmem : (↑(Ultrafilter.map (Gseq b K c s m k) g) : Filter ℝ)
      ≤ Filter.principal (Set.Icc (0 : ℝ) (K : ℝ)) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff]
    exact Filter.mem_map.2 (Filter.univ_mem' fun n =>
      ⟨Gseq_nonneg b K c s m k n, Gseq_le b K c s m k n⟩)
  obtain ⟨a, -, ha⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (K : ℝ))).ultrafilter_le_nhds
    (Ultrafilter.map (Gseq b K c s m k) g) hmem
  rw [Ultrafilter.coe_map] at ha
  exact le_nhds_lim ⟨a, ha⟩

/-! ### §4  The three relations in the limit -/

/-- A helper: two sequences that differ by `O(1/n)` have the same ultrafilter limit. -/
lemma eq_of_tendsto_of_close {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) {u v : ℕ → ℝ}
    {x y C : ℝ} (hu : Tendsto u (g : Filter ℕ) (nhds x)) (hv : Tendsto v (g : Filter ℕ) (nhds y))
    (h : ∀ n, 1 ≤ n → |u n - v n| ≤ C / n) : x = y := by
  have hC : Tendsto (fun n : ℕ => C / n) (g : Filter ℕ) (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).mono_left hg
  have hev : ∀ᶠ n in (g : Filter ℕ), ‖u n - v n‖ ≤ C / n := by
    filter_upwards [hg (Filter.eventually_ge_atTop 1)] with n hn
    simpa [Real.norm_eq_abs] using h n hn
  have hzero : Tendsto (fun n => u n - v n) (g : Filter ℕ) (nhds 0) :=
    squeeze_zero_norm' hev hC
  have := tendsto_nhds_unique (hu.sub hv) hzero
  linarith [this]

lemma G_nonneg (g : Ultrafilter ℕ) (b K c : ℕ) (s : ℕ → ℕ) (m k : ℕ) :
    0 ≤ G g b K c s m k :=
  ge_of_tendsto (tendsto_G g b K c s m k)
    (Filter.univ_mem' fun n => Gseq_nonneg b K c s m k n)

lemma G_bdd {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hnorm : IsNormalSequence b s)
    {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) (c m k : ℕ) :
    G g b K c s m k ≤ (K : ℝ) / (b : ℝ) ^ m := by
  have hlim : Tendsto (fun n => (K : ℝ) * ((winCount s (wordOf b m k) n : ℝ) / n))
      (g : Filter ℕ) (nhds ((K : ℝ) * ((b : ℝ) ^ m)⁻¹)) :=
    ((tendsto_winCount_wordOf hb hnorm m k).const_mul (K : ℝ)).mono_left hg
  have hle : ∀ n, Gseq b K c s m k n ≤ (K : ℝ) * ((winCount s (wordOf b m k) n : ℝ) / n) := by
    intro n
    unfold Gseq
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hRW : (resCount K c s (wordOf b m k) n : ℝ) ≤ (winCount s (wordOf b m k) n : ℝ) := by
      exact_mod_cast resCount_le_winCount K c s (wordOf b m k) n
    have he1 : (K : ℝ) / n * (resCount K c s (wordOf b m k) n : ℝ)
        = (K : ℝ) * ((resCount K c s (wordOf b m k) n : ℝ) / n) := by ring
    rw [he1]
    have hKn : (0 : ℝ) ≤ (K : ℝ) := by positivity
    gcongr
  have := le_of_tendsto_of_tendsto' (tendsto_G g b K c s m k) hlim hle
  rwa [div_eq_mul_inv]

lemma G_unit {K : ℕ} (hK : 0 < K) {b : ℕ} {s : ℕ → ℕ} {g : Ultrafilter ℕ}
    (hg : (g : Filter ℕ) ≤ atTop) (c : ℕ) : G g b K c s 0 0 = 1 := by
  refine eq_of_tendsto_of_close hg (tendsto_G g b K c s 0 0)
    (tendsto_const_nhds (x := (1 : ℝ))) (C := (K : ℝ)) ?_
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hb1, hb2⟩ := resCount_nil_bounds hK c s n
  set R : ℕ := resCount K c s [] n with hR
  have hc1 : (K : ℝ) * R ≤ (n : ℝ) + K := by exact_mod_cast hb1
  have hc2 : (n : ℝ) ≤ (K : ℝ) * R + K := by exact_mod_cast hb2
  have hnil : wordOf b 0 0 = [] := wordOf_zero b 0
  have hkey : Gseq b K c s 0 0 n - 1 = ((K : ℝ) * R - n) / n := by
    unfold Gseq
    rw [hnil, ← hR]
    field_simp
  rw [hkey, abs_div, abs_of_pos hn']
  have habs : |(K : ℝ) * R - n| ≤ (K : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  gcongr

lemma G_right {b : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : ∀ j, s j < b) (K c : ℕ)
    (g : Ultrafilter ℕ) (m k : ℕ) :
    G g b K c s m k = ∑ d ∈ Finset.range b, G g b K c s (m + 1) (k * b + d) := by
  have hpt : ∀ n, Gseq b K c s m k n
      = ∑ d ∈ Finset.range b, Gseq b K c s (m + 1) (k * b + d) n := by
    intro n
    unfold Gseq
    rw [← Finset.mul_sum]
    congr 1
    rw [resCount_append hs K c (wordOf b m k) n]
    push_cast
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [wordOf_append b m k d hb (Finset.mem_range.1 hd)]
  have h2 : Tendsto (fun n => ∑ d ∈ Finset.range b, Gseq b K c s (m + 1) (k * b + d) n)
      (g : Filter ℕ) (nhds (∑ d ∈ Finset.range b, G g b K c s (m + 1) (k * b + d))) :=
    tendsto_finset_sum _ fun d _ => tendsto_G g b K c s (m + 1) (k * b + d)
  exact tendsto_nhds_unique ((tendsto_G g b K c s m k).congr hpt) h2

lemma G_prepend {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) (c m k : ℕ) (hk : k < b ^ m) :
    G g b K (c + 1) s m k = ∑ d ∈ Finset.range b, G g b K c s (m + 1) (d * b ^ m + k) := by
  have h2 : Tendsto (fun n => ∑ d ∈ Finset.range b, Gseq b K c s (m + 1) (d * b ^ m + k) n)
      (g : Filter ℕ) (nhds (∑ d ∈ Finset.range b, G g b K c s (m + 1) (d * b ^ m + k))) :=
    tendsto_finset_sum _ fun d _ => tendsto_G g b K c s (m + 1) (d * b ^ m + k)
  refine eq_of_tendsto_of_close hg (tendsto_G g b K (c + 1) s m k) h2 (C := (K : ℝ)) ?_
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set v : List ℕ := wordOf b m k with hv
  set R : ℕ := resCount K (c + 1) s v n with hR
  set S : ℕ := ∑ d ∈ Finset.range b, resCount K c s (d :: v) n with hS
  have hword : ∀ d ∈ Finset.range b, wordOf b (m + 1) (d * b ^ m + k) = d :: v := by
    intro d hd
    exact wordOf_cons b m k d hb hk (Finset.mem_range.1 hd)
  have hsum : ∑ d ∈ Finset.range b, Gseq b K c s (m + 1) (d * b ^ m + k) n
      = (K : ℝ) / n * (S : ℝ) := by
    rw [hS]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    unfold Gseq
    rw [hword d hd]
  obtain ⟨hp1, hp2⟩ := resCount_prepend_bounds hs hK c v n
  have hmono : R ≤ resCount K (c + 1) s v (n + 1) := resCount_mono K (c + 1) s v (Nat.le_succ n)
  have hstep : resCount K (c + 1) s v (n + 1) ≤ R + 1 := resCount_succ_le K (c + 1) s v n
  have hRS : (R : ℝ) - S ≤ 1 ∧ (S : ℝ) - R ≤ 1 := by
    constructor
    · have : R ≤ S + 1 := by omega
      have : (R : ℝ) ≤ (S : ℝ) + 1 := by exact_mod_cast this
      linarith
    · have : S ≤ R + 1 := by omega
      have : (S : ℝ) ≤ (R : ℝ) + 1 := by exact_mod_cast this
      linarith
  have hkey : Gseq b K (c + 1) s m k n
      - ∑ d ∈ Finset.range b, Gseq b K c s (m + 1) (d * b ^ m + k) n
      = (K : ℝ) / n * ((R : ℝ) - S) := by
    rw [hsum]
    unfold Gseq
    rw [← hv, ← hR]
    ring
  rw [hkey, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ) / n)]
  have habs : |(R : ℝ) - S| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hRS.1, hRS.2]
  calc (K : ℝ) / n * |(R : ℝ) - S| ≤ (K : ℝ) / n * 1 := by
        have : (0 : ℝ) ≤ (K : ℝ) / n := by positivity
        nlinarith
    _ = (K : ℝ) / n := by ring

/-! ### §5  Periodicity in the class, and the `shift` relation -/

lemma resCount_class {K c c' : ℕ} (h : c % K = c' % K) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) :
    resCount K c s v n = resCount K c' s v n := by
  classical
  rw [resCount, resCount, h]

lemma G_class {K c c' : ℕ} (h : c % K = c' % K) (g : Ultrafilter ℕ) (b : ℕ) (s : ℕ → ℕ)
    (m k : ℕ) : G g b K c s m k = G g b K c' s m k := by
  have hfun : Gseq b K c s m k = Gseq b K c' s m k := by
    funext n
    unfold Gseq
    rw [resCount_class h s _ n]
  unfold G
  rw [hfun]

/-- Iterating `G_prepend`: `r` prepends turn class `c` into class `c + r` and level `m` into
level `m + r`. -/
lemma G_iter {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) (c : ℕ) :
    ∀ r m k : ℕ, k < b ^ m →
      G g b K (c + r) s m k = ∑ t ∈ Finset.range (b ^ r), G g b K c s (m + r) (t * b ^ m + k) := by
  intro r
  induction r with
  | zero => intro m k _; simp
  | succ r ih =>
      intro m k hk
      have hstep : G g b K (c + r + 1) s m k
          = ∑ d ∈ Finset.range b, G g b K (c + r) s (m + 1) (d * b ^ m + k) :=
        G_prepend hb hK hs hg (c + r) m k hk
      have harg : c + (r + 1) = c + r + 1 := by omega
      rw [harg, hstep]
      have hbound : ∀ d ∈ Finset.range b, d * b ^ m + k < b ^ (m + 1) := by
        intro d hd
        rw [Finset.mem_range] at hd
        have h1 : (d + 1) * b ^ m ≤ b * b ^ m := Nat.mul_le_mul_right _ hd
        rw [pow_succ, mul_comm (b ^ m) b]
        calc d * b ^ m + k < d * b ^ m + b ^ m := by omega
          _ = (d + 1) * b ^ m := by ring
          _ ≤ b * b ^ m := h1
      have hinner : ∀ d ∈ Finset.range b,
          G g b K (c + r) s (m + 1) (d * b ^ m + k)
            = ∑ t ∈ Finset.range (b ^ r), G g b K c s (m + 1 + r) (t * b ^ (m + 1) + (d * b ^ m + k)) :=
        fun d hd => ih (m + 1) (d * b ^ m + k) (hbound d hd)
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      have hpow : b ^ (r + 1) = b ^ r * b := by ring
      rw [hpow, BlockRigidity.sum_range_mul'
        (fun u => G g b K c s (m + (r + 1)) (u * b ^ m + k)) (b ^ r) b]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun d _ => ?_
      have hlev : m + (r + 1) = m + 1 + r := by omega
      have hval : (t * b + d) * b ^ m + k = t * b ^ (m + 1) + (d * b ^ m + k) := by
        rw [pow_succ]; ring
      rw [hlev, hval]

lemma G_shift {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) (c m k : ℕ) (hk : k < b ^ m) :
    G g b K c s m k = ∑ t ∈ Finset.range (b ^ K), G g b K c s (m + K) (t * b ^ m + k) := by
  have hper : G g b K c s m k = G g b K (c + K) s m k :=
    G_class (Nat.add_mod_right c K).symm g b s m k
  rw [hper, G_iter hb hK hs hg c K m k hk]

/-! ### §6  The system, and the theorem -/

theorem sys_G {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    (hnorm : IsNormalSequence b s) {g : Ultrafilter ℕ} (hg : (g : Filter ℕ) ≤ atTop) (c : ℕ) :
    BlockRigidity.Sys b K (K : ℝ) (G g b K c s) where
  bpos := hb
  Kpos := hK
  nonneg := fun m k => G_nonneg g b K c s m k
  bdd := fun m k => G_bdd hb hnorm hg c m k
  unit := G_unit hK hg c
  right := fun m k => G_right hb hs K c g m k
  shift := fun m k hk => G_shift hb hK hs hg c m k hk

/-- 🎯 **The residue-restricted word density of a normal sequence.**  For a base-`b` normal
sequence `s`, every residue class `c` mod `K` sees every base-`b` word of length `m` with its
correct frequency `b^{-m}` — the fraction of the class's positions carrying the word. -/
theorem tendsto_resCount {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    (hnorm : IsNormalSequence b s) (c m k : ℕ) (hk : k < b ^ m) :
    Tendsto (fun n => (K : ℝ) / n * (resCount K c s (wordOf b m k) n : ℝ)) atTop
      (nhds (1 / (b : ℝ) ^ m)) := by
  rw [tendsto_iff_ultrafilter]
  intro g hg
  have hlim := tendsto_G g b K c s m k
  have hval : G g b K c s m k = 1 / (b : ℝ) ^ m :=
    (sys_G hb hK hs hnorm hg c).eq_uniform m k hk
  rw [hval] at hlim
  exact hlim

end NormalNumbers.PowerBase
