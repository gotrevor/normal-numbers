/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature
import NormalNumbers.Stoneham
import NormalNumbers.Counting

/-!
# Ledger edge: Bailey–Misiurewicz strong hot spot Thm 3.5 is VERIFIED here 🔌

`Literature.baileyMisiurewicz_strong_hot_spot_criterion` (B–M 2006 Thm 3.5,
the uniform-`C` sufficient form) is discharged into a machine-checked
`…_holds` edge — upgrading "we cite it" to "we independently verified it",
exactly the ledger's purpose (same move as `adamczewskiRampersad_boundary_holds`).

The proof routes the block-occurrence hypothesis to the repo's already-proven
b-adic-interval normality criterion `isNormal_of_visit_upper_bound`:

* `blockOfNat` — the big-endian base-`b` `k`-digit word of `m < bᵏ`, with
  `blockNatVal_blockOfNat` (it round-trips), `length_blockOfNat`,
  `blockOfNat_lt` (its digits are `< b`);
* `matchesAt_iff_occursAt` glues `MatchesAt (digitOf …)` to `OccursAt`, so
  `occursAt_iff_orbit_mem` identifies the occurrence count of the word with
  the visit count of its b-adic interval;
* `card_filter_matchesAt_le` (clipped vs unclipped window counts differ by
  `≤ |w|`) turns `bmHotSpotRatio ≤ C` into the eventual visit bound.
-/

namespace NormalNumbers.Literature

open NormalNumbers Filter

/-! ## The big-endian base-`b` digit word of a bounded natural -/

/-- The big-endian base-`b` word of length `k` representing `m`
(`blockOfNat b (k+1) m = (m / bᵏ) :: blockOfNat b k (m % bᵏ)`). -/
def blockOfNat (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, m => (m / b ^ k) :: blockOfNat b k (m % b ^ k)

@[simp] theorem length_blockOfNat (b k m : ℕ) : (blockOfNat b k m).length = k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => simp [blockOfNat, ih]

/-- Every digit of `blockOfNat b k m` is `< b` when `m < bᵏ` and `2 ≤ b`. -/
theorem blockOfNat_lt (b : ℕ) (hb : 2 ≤ b) :
    ∀ (k m : ℕ), m < b ^ k → ∀ d ∈ blockOfNat b k m, d < b := by
  intro k
  induction k with
  | zero => intro m hm d hd; simp [blockOfNat] at hd
  | succ k ih =>
    intro m hm d hd
    rw [blockOfNat, List.mem_cons] at hd
    have hbk : 0 < b ^ k := by positivity
    rcases hd with hd | hd
    · subst hd
      rw [Nat.div_lt_iff_lt_mul hbk]
      calc m < b ^ (k + 1) := hm
        _ = b ^ k * b := by ring
        _ = b * b ^ k := by ring
    · exact ih (m % b ^ k) (Nat.mod_lt _ hbk) d hd

/-- `blockOfNat` round-trips through `blockNatVal`: it really represents `m`. -/
theorem blockNatVal_blockOfNat (b : ℕ) (hb : 2 ≤ b) :
    ∀ (k m : ℕ), m < b ^ k → blockNatVal b (blockOfNat b k m) = m := by
  intro k
  induction k with
  | zero =>
      intro m hm; simp only [pow_zero, Nat.lt_one_iff] at hm
      simp [blockOfNat, hm, blockNatVal]
  | succ k ih =>
    intro m hm
    have hbk : 0 < b ^ k := by positivity
    rw [blockOfNat, blockNatVal_cons, length_blockOfNat,
      ih (m % b ^ k) (Nat.mod_lt _ hbk)]
    rw [Nat.div_add_mod']

/-! ## `MatchesAt` of the digit sequence is `OccursAt` -/

/-- The digit-sequence match predicate is exactly the repo's `OccursAt`. -/
theorem matchesAt_iff_occursAt (b : ℕ) (x : ℝ) (w : List ℕ) (i : ℕ) :
    MatchesAt (digitOf b (Int.fract x)) w i ↔ OccursAt b x w i := by
  unfold MatchesAt OccursAt
  constructor
  · intro h j hj
    have := h j hj
    rwa [List.getD_eq_getElem w 0 hj] at this
  · intro h j hj
    have := h j hj
    rwa [← List.getD_eq_getElem w 0 hj] at this

/-- The visit count of a word's b-adic interval equals the (unclipped) count
of window positions `< n` where the word occurs. -/
theorem visitCount_eq_card_matchesAt (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) (n : ℕ) :
    visitCount (orbit b (Int.fract x))
        ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length)
        (((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length) n
      = ((Finset.range n).filter (MatchesAt (digitOf b (Int.fract x)) w)).card := by
  unfold visitCount
  refine congrArg Finset.card (Finset.filter_congr fun j _ => ?_)
  rw [← occursAt_iff_orbit_mem b hb (Int.fract x) w hw j,
    ← matchesAt_iff_occursAt b (Int.fract x) w j, Int.fract_fract]

/-! ## The analytic step: limsup bound + bounded gap ⇒ eventual visit bound -/

/-- If the scaled clipped count `β·O n / n` has `limsup ≤ C`, and the visit
count `U n` exceeds `O n` by at most a constant `L`, then eventually the visit
frequency obeys `U n / n ≤ (|C|+1)/β`.  Pure real-analysis bookkeeping around
`eventually_lt_of_limsup_lt` and the vanishing boundary term `β·L/n → 0`. -/
theorem eventually_visit_bound_of_limsup {β C : ℝ} {O U : ℕ → ℕ} {L : ℕ}
    (hβ : 0 < β)
    (hlim : Filter.limsup (fun n => β * (O n : ℝ) / n) Filter.atTop ≤ C)
    (hObd : ∀ n, O n ≤ n + 1)
    (hUO : ∀ n, U n ≤ O n + L) :
    ∀ᶠ n in Filter.atTop, (U n : ℝ) / n ≤ (|C| + 1) / β := by
  set f : ℕ → ℝ := fun n => β * (O n : ℝ) / n with hf
  -- `f` is bounded above (by `2β`, since `O n ≤ n+1`), so `eventually_lt_of_limsup_lt` applies.
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop f := by
    refine ⟨2 * β, Filter.eventually_map.2 (Filter.Eventually.of_forall (fun n => ?_))⟩
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0; rw [hf]; simp only [Nat.cast_zero, div_zero]; linarith [hβ]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hOn : (O n : ℝ) ≤ n + 1 := by exact_mod_cast hObd n
      rw [hf, div_le_iff₀ hnR]
      nlinarith [hOn, h1, hβ]
  have hClt : C < |C| + 1 / 2 := lt_of_le_of_lt (le_abs_self C) (by linarith)
  have hf_ev : ∀ᶠ n in Filter.atTop, f n ≤ |C| + 1 / 2 := by
    have := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim hClt) hbdd
    filter_upwards [this] with n hn using hn.le
  -- the boundary term `β·L/n → 0`, hence eventually `≤ 1/2`.
  have hbdry : ∀ᶠ (n : ℕ) in Filter.atTop, β * (L : ℝ) / n ≤ 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => β * (L : ℝ) / n) Filter.atTop (nhds 0) := by
      simpa [mul_div_assoc] using
        (tendsto_const_div_atTop_nhds_zero_nat (L : ℝ)).const_mul β
    have h := htend.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    simpa using h
  filter_upwards [hf_ev, hbdry, Filter.eventually_gt_atTop 0] with n hfn hbn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- `β·U n / n ≤ β·O n/n + β·L/n ≤ |C|+1`.
  have hUle : (U n : ℝ) ≤ (O n : ℝ) + L := by exact_mod_cast hUO n
  have hg : β * (U n : ℝ) / n ≤ f n + β * (L : ℝ) / n := by
    rw [hf]
    have hcomb : β * (O n : ℝ) / n + β * (L : ℝ) / n
        = (β * (O n : ℝ) + β * (L : ℝ)) / n := by ring
    rw [hcomb]
    exact (div_le_div_iff_of_pos_right hnR).mpr (by nlinarith [hUle, hβ])
  have hgle : β * (U n : ℝ) / n ≤ |C| + 1 := by
    have : f n + β * (L : ℝ) / n ≤ (|C| + 1 / 2) + 1 / 2 := add_le_add hfn hbn
    linarith
  have hgle' : β * (U n : ℝ) ≤ (|C| + 1) * n := (div_le_iff₀ hnR).mp hgle
  rw [div_le_iff₀ hnR, div_mul_eq_mul_div, le_div_iff₀ hβ]
  linarith [hgle']

/-! ## The edge: Thm 3.5 verified from `isNormal_of_visit_upper_bound` -/

/-- **Bailey–Misiurewicz 2006, Theorem 3.5 — VERIFIED.**  The uniform-`C`
block-occurrence criterion implies normality, proven through the repo's
b-adic-interval visit criterion.  Upgrades the ledger entry
`baileyMisiurewicz_strong_hot_spot_criterion` from a cited `def` to an
independently machine-checked edge. -/
theorem baileyMisiurewicz_strong_hot_spot_criterion_holds :
    baileyMisiurewicz_strong_hot_spot_criterion := by
  rintro b hb x ⟨C, hC⟩
  have hCnn : (0 : ℝ) ≤ |C| := abs_nonneg C
  refine isNormal_of_visit_upper_bound b hb x (|C| + 1) ?_
  intro k m hm
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  set s : ℕ → ℕ := digitOf b (Int.fract x) with hsdef
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: interval is [0,1), every orbit point visits, count = n, ratio = 1.
    subst hk0
    simp only [pow_zero, Nat.lt_one_iff] at hm; subst hm
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hfull : ((Finset.range n).filter
        (fun j => orbit b (Int.fract x) j ∈ Set.Ico ((0:ℝ)/(b:ℝ)^0) (((0:ℝ)+1)/(b:ℝ)^0)))
        = Finset.range n := by
      apply Finset.filter_true_of_mem
      intro j _
      simpa using orbit_mem_Ico b (Int.fract x) j
    have : visitCount (orbit b (Int.fract x)) ((0:ℝ)/(b:ℝ)^0) (((0:ℝ)+1)/(b:ℝ)^0) n = n := by
      rw [visitCount, hfull, Finset.card_range]
    rw [Nat.cast_zero]
    rw [this, pow_zero, div_one, div_self (by positivity)]
    linarith
  -- k ≥ 1: the word of m and its digit-sequence extension.
  set w : List ℕ := blockOfNat b k m with hwdef
  have hwlen : w.length = k := length_blockOfNat b k m
  have hwlt : ∀ d ∈ w, d < b := blockOfNat_lt b hb k m hm
  have hwval : blockNatVal b w = m := blockNatVal_blockOfNat b hb k m hm
  have hwne : w ≠ [] := by
    intro h; rw [h, List.length_nil] at hwlen; omega
  set y : ℕ → ℕ := fun i => w.getD i 0 with hydef
  have hyb : ∀ i, y i < b := by
    intro i
    simp only [hydef]
    by_cases hi : i < w.length
    · rw [List.getD_eq_getElem w 0 hi]
      exact hwlt _ (List.getElem_mem hi)
    · rw [List.getD_eq_default w 0 (by omega)]; omega
  have hpref : (List.range k).map y = w := by
    apply List.ext_getElem (by simp [hwlen])
    intro l h1 h2
    simp only [List.getElem_map, List.getElem_range, hydef]
    rw [List.getD_eq_getElem w 0 (by simpa [hwlen] using h2)]
  -- the hypothesis at this word: limsup of the scaled clipped count ≤ C.
  have hlim := hC y hyb k
  rw [bmHotSpotRatio, hpref, ← hsdef] at hlim
  set O : ℕ → ℕ := fun n => countOccurrences w ((List.range n).map s) with hOdef
  have hlim' : Filter.limsup (fun n => (b : ℝ) ^ k * (O n : ℝ) / n) Filter.atTop ≤ C := hlim
  -- clipped vs unclipped window counts; the visit count is the unclipped one.
  set U : ℕ → ℕ := fun n => ((Finset.range n).filter (MatchesAt s w)).card with hUdef
  have hOU : ∀ n, O n ≤ U n ∧ U n ≤ O n + w.length := fun n =>
    card_filter_matchesAt_le s w hwne n
  have hObd : ∀ n, O n ≤ n + 1 := by
    intro n
    calc O n ≤ ((List.range n).map s).tails.length := by
            simp only [hOdef, countOccurrences]; exact List.countP_le_length
      _ = n + 1 := by rw [List.length_tails, List.length_map, List.length_range]
  have hVU : ∀ n, visitCount (orbit b (Int.fract x))
      ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k) n = U n := by
    intro n
    have h := visitCount_eq_card_matchesAt b hb x w hwlt n
    rw [hwval, hwlen] at h
    exact h
  -- Reduce to the eventual visit bound on `U`, then invoke the analytic step.
  simp only [hVU]
  exact eventually_visit_bound_of_limsup hbk hlim' hObd (fun n => (hOU n).2)

/-! ## Bailey–Misiurewicz 2006, Theorem 1.1 (the weak hot spot iff) — VERIFIED -/

/-- If a visit count `V n ≤ n` has `limsup (V n / n) ≤ γ`, then eventually
`V n / n ≤ γ'` for any `γ' > γ` (`V n / n ≤ 1` is bounded above). -/
theorem eventually_ratio_le_of_limsup_le {V : ℕ → ℕ} {γ γ' : ℝ}
    (hV : ∀ n, V n ≤ n) (hlt : γ < γ')
    (hlim : Filter.limsup (fun n => (V n : ℝ) / n) Filter.atTop ≤ γ) :
    ∀ᶠ n in Filter.atTop, (V n : ℝ) / n ≤ γ' := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => (V n : ℝ) / n) := by
    refine ⟨1, Filter.eventually_map.2 (Filter.Eventually.of_forall (fun n => ?_))⟩
    rcases Nat.eq_zero_or_pos n with h0 | h
    · subst h0; simp
    · have hnR : (0 : ℝ) < n := by exact_mod_cast h
      rw [div_le_one hnR]; exact_mod_cast hV n
  have := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim hlt) hbdd
  filter_upwards [this] with n hn using hn.le

/-- `visitCount` never exceeds the window length. -/
theorem visitCount_le (u : ℕ → ℝ) (a c : ℝ) (n : ℕ) : visitCount u a c n ≤ n := by
  rw [visitCount]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)

/-- **Bailey–Misiurewicz 2006, Theorem 1.1 — VERIFIED.**  `x` is `b`-normal iff
there is a uniform constant `B` bounding every interval's visit frequency by
`B·(length)`.  Both directions are proven: `⟸` through
`isNormal_of_visit_upper_bound` (specialising to b-adic intervals), `⟹`
through Wall's theorem `isNormal_iff_equidistributed_orbit` (a normal orbit's
visit frequency converges to the interval length, so `B = 1` works). -/
theorem baileyMisiurewicz_weak_hot_spot_holds : baileyMisiurewicz_weak_hot_spot := by
  intro b hb x
  have horb : orbit b (Int.fract x) = orbit b x := funext (orbit_fract b x)
  constructor
  · -- normal ⟹ ∃ B (take B = 1): equidistribution pins each limsup to `d − c`.
    intro hn
    have heq : Equidistributed (orbit b x) := (isNormal_iff_equidistributed_orbit b hb x).mp hn
    refine ⟨1, fun c d hc hcd hd => ?_⟩
    have htend := heq c d hc hcd.le hd
    rw [horb]
    rw [htend.limsup_eq]
    linarith [hcd]
  · -- ∃ B ⟹ normal: feed the b-adic specialisation to the visit criterion.
    rintro ⟨B, hB⟩
    refine isNormal_of_visit_upper_bound b hb x (|B| + 1) ?_
    intro k m hm
    have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hc : (0 : ℝ) ≤ (m : ℝ) / (b : ℝ) ^ k := by positivity
    have hcd : (m : ℝ) / (b : ℝ) ^ k < ((m : ℝ) + 1) / (b : ℝ) ^ k := by
      gcongr; linarith
    have hd : ((m : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 := by
      rw [div_le_one hbk]; exact_mod_cast Nat.succ_le_of_lt hm
    have hlim := hB _ _ hc hcd hd
    have hdc : ((m : ℝ) + 1) / (b : ℝ) ^ k - (m : ℝ) / (b : ℝ) ^ k = 1 / (b : ℝ) ^ k := by
      rw [div_sub_div_same]; norm_num
    rw [hdc, mul_one_div] at hlim
    have hlt : B / (b : ℝ) ^ k < (|B| + 1) / (b : ℝ) ^ k := by
      gcongr; linarith [le_abs_self B]
    exact eventually_ratio_le_of_limsup_le (fun n => visitCount_le _ _ _ n) hlt hlim

end NormalNumbers.Literature
