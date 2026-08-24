/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFSchedule
import NormalNumbers.CFConcat
import NormalNumbers.BaryConcat

/-!
# W5 — correctness of the schedule, CF side (B–Y §2.2)

`xstar`'s CF digit word is the increasing union of the scheduled words
`wSched s`; each appended block `uSched s` carries the Lemma-13 CF count
payload.  Chaining the payloads through B–Y Lemma 7 (`CFDiscLt.append`,
`cfDiscLt_short_append`, `cfDiscLt_append_take`) yields **CF normality of
`xstar`**: for every genuine pattern `v`, the fitting-window frequency of `v`
in the length-`p` digit prefix of `xstar` tends to `γ(I_v)`.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-! ## Schedule accessors -/

/-- The scheduled CF word at stage `s`. -/
noncomputable def wSched (s : ℕ) : List ℕ := (sched s).B.w

/-- The scheduled level at stage `s`. -/
noncomputable def tSched (s : ℕ) : ℕ := (sched s).t

/-- The CF block appended at step `s` (so `wSched (s+1) = wSched s ++ uSched s`). -/
noncomputable def uSched (s : ℕ) : List ℕ :=
  (wSched (s + 1)).drop (wSched s).length

theorem wSched_ne (s : ℕ) : wSched s ≠ [] := (sched s).B.hw_ne

theorem wSched_pos (s : ℕ) : ∀ a ∈ wSched s, 1 ≤ a := (sched s).B.hw_pos

theorem wSched_succ (s : ℕ) : wSched (s + 1) = wSched s ++ uSched s := by
  obtain ⟨u, -, -, -, -, hw, -⟩ := sched_step s
  rw [uSched, wSched, wSched, hw, List.drop_left]

/-- The CF-side payload of the block appended at step `s` (level, length,
genuineness, continuant bound, pattern counts). -/
theorem uSched_spec (s : ℕ) :
    (uSched s).length = nFn (tSched (s + 1)) ∧
    (∀ a ∈ uSched s, 1 ≤ a) ∧
    (cfK (uSched s) : ℝ) ≤ Real.exp (goodC * nFn (tSched (s + 1))) ∧
    (∀ v ∈ wordFamily (tSched (s + 1)), |(countOccurrences v (uSched s) : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * nFn (tSched (s + 1))|
        < schedEps (tSched (s + 1)) * nFn (tSched (s + 1)) + v.length) := by
  obtain ⟨u, m₁, j₁, r₁, ht, hw, hlen, hpos, -, -, hK, hCF, -⟩ := sched_step s
  have hu : uSched s = u := by
    rw [uSched, wSched, wSched, hw, List.drop_left]
  rw [hu]
  exact ⟨hlen, hpos, hK, hCF⟩

theorem uSched_length (s : ℕ) : (uSched s).length = nFn (tSched (s + 1)) :=
  (uSched_spec s).1

theorem uSched_ne (s : ℕ) : uSched s ≠ [] := by
  intro h
  have := uSched_length s
  rw [h] at this
  simp at this
  exact absurd this.symm (nFn_pos _).ne'

/-- **Khinchin uniform-integrability seed**: the total `log`-digit mass of
each appended schedule block is bounded by `goodC` times the block length —
i.e. the average `log`-digit per stage is uniformly bounded by the constant
`goodC`, with no digit-cap re-plumb needed (the existing `cfK`-continuant
payload already controls it via `prod_le_cfK`). -/
private theorem log_sum_eq_log_prod (l : List ℕ) (hpos : ∀ a ∈ l, 1 ≤ a) :
    (l.map (fun a : ℕ => Real.log a)).sum = Real.log (l.prod : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha1 : 1 ≤ a := hpos a List.mem_cons_self
      have hl : ∀ b ∈ l, 1 ≤ b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
      have hlpos : 0 < l.prod := by
        rcases Nat.eq_zero_or_pos l.prod with h0 | h0
        · exact absurd ((List.prod_eq_zero_iff).mp h0) (fun h0' => by
            have := hl 0 h0'; omega)
        · exact h0
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
      have hl0 : (l.prod : ℝ) ≠ 0 := by exact_mod_cast hlpos.ne'
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [ih hl, Nat.cast_mul, Real.log_mul ha0 hl0]

theorem uSched_log_sum_le (s : ℕ) :
    ((uSched s).map (fun a : ℕ => Real.log a)).sum ≤ goodC * nFn (tSched (s + 1)) := by
  obtain ⟨-, hpos, hK, -⟩ := uSched_spec s
  have hprod : (uSched s).prod ≤ cfK (uSched s) := prod_le_cfK (uSched s)
  have hprodR : ((uSched s).prod : ℝ) ≤ Real.exp (goodC * nFn (tSched (s + 1))) := by
    calc ((uSched s).prod : ℝ) ≤ (cfK (uSched s) : ℝ) := by exact_mod_cast hprod
      _ ≤ Real.exp (goodC * nFn (tSched (s + 1))) := hK
  have hpos0 : 0 ∉ uSched s := fun h0 => absurd (hpos 0 h0) (by norm_num)
  have hprodpos : 0 < (uSched s).prod := by
    rcases Nat.eq_zero_or_pos (uSched s).prod with h0 | h0
    · exact absurd ((List.prod_eq_zero_iff).mp h0) hpos0
    · exact h0
  have hpos' : (0 : ℝ) < ((uSched s).prod : ℝ) := by exact_mod_cast hprodpos
  have hlogle : Real.log ((uSched s).prod : ℝ) ≤ goodC * nFn (tSched (s + 1)) := by
    calc Real.log ((uSched s).prod : ℝ)
        ≤ Real.log (Real.exp (goodC * nFn (tSched (s + 1)))) :=
          Real.log_le_log hpos' hprodR
      _ = goodC * nFn (tSched (s + 1)) := Real.log_exp _
  rwa [log_sum_eq_log_prod (uSched s) hpos]

/-- Word length at stage `s`. -/
theorem wSched_length_succ (s : ℕ) :
    (wSched (s + 1)).length = (wSched s).length + nFn (tSched (s + 1)) := by
  rw [wSched_succ, List.length_append, uSched_length]

/-- **Telescoped Khinchin bound**: the total `log`-digit mass of the whole
scheduled word `wSched s` is bounded by `goodC` times its length — the seed
word (all `1`s, `log 1 = 0`) contributes nothing, and each stage adds at
most `goodC · (block length)` by `uSched_log_sum_le`. -/
theorem wSched_log_sum_le (s : ℕ) :
    ((wSched s).map (fun a : ℕ => Real.log a)).sum ≤ goodC * (wSched s).length := by
  induction s with
  | zero =>
      have hw : wSched 0 = seedWord := by rw [wSched, sched_zero, seedState_w]
      rw [hw]
      have hlog1 : ((seedWord).map (fun a : ℕ => Real.log a)).sum = 0 := by
        have heq : (seedWord).map (fun a : ℕ => Real.log a)
            = List.replicate (promThreshold 2) (Real.log (1 : ℕ)) := by
          rw [seedWord, List.map_replicate]
        rw [heq, List.sum_replicate]
        norm_num
      rw [hlog1]
      exact mul_nonneg goodC_pos.le (Nat.cast_nonneg _)
  | succ s ih =>
      have hu := uSched_log_sum_le s
      rw [wSched_succ, List.map_append, List.sum_append, List.length_append, uSched_length]
      push_cast
      calc ((wSched s).map (fun a : ℕ => Real.log a)).sum
            + ((uSched s).map (fun a : ℕ => Real.log a)).sum
          ≤ goodC * (wSched s).length + goodC * nFn (tSched (s + 1)) :=
            add_le_add ih hu
        _ = goodC * ((wSched s).length + nFn (tSched (s + 1)) : ℝ) := by ring

/-- The dominance condition in accessor form: the appended block has length
at most `|wSched s| / tSched (s+1)`. -/
theorem uSched_dominance (s : ℕ) :
    tSched (s + 1) * (uSched s).length ≤ (wSched s).length := by
  rw [uSched_length]
  exact sched_dominance s

/-! ## Digit identification -/

/-- The length-`p` CF digit prefix of `xstar`. -/
noncomputable def cfPrefix (p : ℕ) : List ℕ :=
  (List.range p).map (cfDigit xstar)

theorem cfPrefix_length (p : ℕ) : (cfPrefix p).length = p := by
  simp [cfPrefix]

/-- Digit identification at stage boundaries: the digit prefix of `xstar`
of length `|wSched s|` IS `wSched s`. -/
theorem cfPrefix_eq_wSched (s : ℕ) :
    cfPrefix (wSched s).length = wSched s := by
  have hx : xstar ∈ cfCylinder (([] : List ℕ) ++ wSched s) := xstar_mem s
  have h := range_map_cfDigit_eq hx
  simpa [cfPrefix] using h

/-- Prefixes restrict: `cfPrefix p = (cfPrefix q).take p` for `p ≤ q`. -/
theorem cfPrefix_take {p q : ℕ} (h : p ≤ q) :
    cfPrefix p = (cfPrefix q).take p := by
  rw [cfPrefix, cfPrefix, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-! ## Monotonicity helpers -/

/-- `CFDiscLt` is monotone in the accuracy. -/
theorem CFDiscLt.mono {w a : List ℕ} {m ε ε' : ℝ} (h : CFDiscLt w a m ε)
    (hε : ε ≤ ε') : CFDiscLt w a m ε' :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- `γ(I_v) ∈ [0, 1]`. -/
theorem gaussMeasure_toReal_mem_Icc (S : Set ℝ) :
    (gaussMeasure S).toReal ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h := prob_le_one (μ := gaussMeasure) (s := S)
  calc (gaussMeasure S).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top h
    _ = 1 := by simp

/-! ## Level margins -/

/-- Every list of naturals is bounded. -/
theorem exists_list_bound (l : List ℕ) : ∃ M : ℕ, ∀ a ∈ l, a ≤ M := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons b l ih =>
    obtain ⟨M, hMl⟩ := ih
    refine ⟨max b M, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | h
    · exact le_max_left _ _
    · exact le_trans (hMl a h) (le_max_right _ _)

/-- **The level margin**: past some level `T`, the pattern `v` is active and
the per-stage payload accuracy `schedEps t · n + |v|` fits inside `ε·n` with
room to spare (`+ 2|v|` version), and `1/t ≤ ε/2` (for the dominance use). -/
theorem exists_level_margin (v : List ℕ) (hne : v ≠ [])
    (hpos : ∀ a ∈ v, 1 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧
      (∀ t, T ≤ t → v ∈ wordFamily t) ∧
      (∀ t, T ≤ t →
        schedEps t * nFn t + 2 * v.length ≤ ε * nFn t) ∧
      (∀ t, T ≤ t → (1 : ℝ) / t ≤ ε / 2) := by
  obtain ⟨M, hM⟩ := exists_list_bound v
  obtain ⟨T₀, hT₀⟩ := exists_nat_ge ((4 * (v.length : ℝ) + 2) / ε)
  refine ⟨max (max v.length M) (max T₀ 1), le_trans (le_max_right _ _)
    (le_max_right _ _), ?_, ?_, ?_⟩
  · intro t ht
    refine mem_wordFamily.2 ⟨⟨List.length_pos_of_ne_nil hne, ?_⟩,
      fun a ha => ⟨hpos a ha, ?_⟩⟩
    · calc v.length ≤ max (max v.length M) (max T₀ 1) :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        _ ≤ t := ht
    · calc a ≤ M := hM a ha
        _ ≤ max (max v.length M) (max T₀ 1) :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        _ ≤ t := ht
  all_goals {
    intro t ht
    have ht1 : 1 ≤ t :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have ht0R : (0 : ℝ) < t := by linarith
    have hT₀t : ((4 * (v.length : ℝ) + 2) / ε) ≤ t := by
      refine le_trans hT₀ ?_
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
    have hεt : 4 * (v.length : ℝ) + 2 ≤ ε * t := by
      rw [div_le_iff₀ hε] at hT₀t
      linarith
    have hv0 : (0 : ℝ) ≤ v.length := Nat.cast_nonneg _
    have hinv : (1 : ℝ) / t ≤ ε / 2 := by
      rw [div_le_div_iff₀ ht0R two_pos]
      nlinarith
    first
    | exact hinv
    | { -- the margin bound
        have hn : (t * t + 1 : ℝ) ≤ (nFn t : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (sq_lt_nFn t)
        have hn0 : (0 : ℝ) ≤ (nFn t : ℝ) := Nat.cast_nonneg _
        have htn : (t : ℝ) ≤ nFn t := by nlinarith
        have heps : schedEps t ≤ 1 / t := by
          rw [schedEps, div_le_div_iff₀ (by positivity) ht0R]
          linarith
        have h1 : schedEps t * nFn t ≤ (ε / 2) * nFn t :=
          mul_le_mul_of_nonneg_right (le_trans heps hinv) hn0
        have h2 : 2 * (v.length : ℝ) ≤ (ε / 2) * nFn t := by
          have h3 : 4 * (v.length : ℝ) + 2 ≤ ε * nFn t := by
            calc 4 * (v.length : ℝ) + 2 ≤ ε * t := hεt
              _ ≤ ε * nFn t := mul_le_mul_of_nonneg_left htn hε.le
          linarith
        linarith }
  }

/-! ## The tail decomposition -/

/-- The digits appended after stage `s₀`. -/
noncomputable def tailSched (s₀ s : ℕ) : List ℕ :=
  (wSched s).drop (wSched s₀).length

theorem tailSched_self (s₀ : ℕ) : tailSched s₀ s₀ = [] := by
  rw [tailSched, List.drop_length]

/-- The scheduled word splits at any earlier stage. -/
theorem wSched_eq_append_tail (s₀ : ℕ) :
    ∀ k, wSched (s₀ + k) = wSched s₀ ++ tailSched s₀ (s₀ + k) := by
  intro k
  induction k with
  | zero => simp [tailSched_self]
  | succ k ih =>
    have hidx : s₀ + (k + 1) = (s₀ + k) + 1 := by omega
    have htail : tailSched s₀ ((s₀ + k) + 1)
        = tailSched s₀ (s₀ + k) ++ uSched (s₀ + k) := by
      rw [tailSched, wSched_succ (s₀ + k), ih, List.append_assoc,
        List.drop_left]
    rw [hidx, htail, wSched_succ (s₀ + k), ih, List.append_assoc]

/-- The tail extends by the appended block each step. -/
theorem tailSched_succ (s₀ k : ℕ) :
    tailSched s₀ (s₀ + k + 1) = tailSched s₀ (s₀ + k) ++ uSched (s₀ + k) := by
  rw [tailSched, wSched_succ (s₀ + k), wSched_eq_append_tail s₀ k,
    List.append_assoc, List.drop_left]

/-- Tail length grows at least linearly. -/
theorem le_tailSched_length (s₀ k : ℕ) :
    k ≤ (tailSched s₀ (s₀ + k)).length := by
  have h1 := wSched_eq_append_tail s₀ k
  have h2 : ((wSched s₀).length) + k ≤ (wSched (s₀ + k)).length :=
    sched_length_ge s₀ k
  have h3 : (wSched (s₀ + k)).length
      = (wSched s₀).length + (tailSched s₀ (s₀ + k)).length := by
    rw [h1, List.length_append]
  omega

/-! ## The chain (B–Y Lemma 7 induction) -/

/-- **The good-tail chain**: past a stage `s₀` whose level clears the margin
threshold, every tail is `ε`-good for `v` (deviation form). -/
theorem tailSched_cfDiscLt (v : List ℕ) (hne : v ≠ [])
    {ε : ℝ} (T : ℕ)
    (hmem : ∀ t, T ≤ t → v ∈ wordFamily t)
    (hmargin : ∀ t, T ≤ t →
      schedEps t * nFn t + 2 * v.length ≤ ε * nFn t)
    (s₀ : ℕ) (hs₀ : T ≤ tSched (s₀ + 1)) :
    ∀ k, CFDiscLt v (tailSched s₀ (s₀ + k + 1))
      (gaussMeasure (cfCylinder v)).toReal ε := by
  have hv1 : (1 : ℝ) ≤ v.length := by
    exact_mod_cast List.length_pos_of_ne_nil hne
  -- the payload of block `s₀ + k`, in margin form
  have hblock : ∀ k, |(countOccurrences v (uSched (s₀ + k)) : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * (uSched (s₀ + k)).length|
        < ε * (uSched (s₀ + k)).length - ((v.length : ℝ) - 1) := by
    intro k
    set t := tSched (s₀ + k + 1) with htdef
    have hTt : T ≤ t := by
      refine le_trans hs₀ ?_
      exact sched_t_mono (by omega)
    obtain ⟨hlen, -, -, hCF⟩ := uSched_spec (s₀ + k)
    have hcount := hCF v (hmem t hTt)
    have hm := hmargin t hTt
    have hlenR : ((uSched (s₀ + k)).length : ℝ) = (nFn t : ℝ) := by
      exact_mod_cast hlen
    rw [hlenR]
    calc |(countOccurrences v (uSched (s₀ + k)) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * (nFn t : ℝ)|
        < schedEps t * nFn t + v.length := hcount
      _ ≤ ε * nFn t - 2 * v.length + v.length := by linarith
      _ ≤ ε * (nFn t : ℝ) - ((v.length : ℝ) - 1) := by linarith
  intro k
  induction k with
  | zero =>
    -- the first block alone
    have h0 : tailSched s₀ (s₀ + 0 + 1) = uSched s₀ := by
      have := tailSched_succ s₀ 0
      simpa [tailSched_self] using this
    rw [h0]
    have h := hblock 0
    simp only [Nat.add_zero] at h
    rw [CFDiscLt]
    calc |(countOccurrences v (uSched s₀) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * (uSched s₀).length|
        < ε * (uSched s₀).length - ((v.length : ℝ) - 1) := h
      _ ≤ ε * (uSched s₀).length := by linarith
  | succ k ih =>
    have h1 : s₀ + (k + 1) = s₀ + k + 1 := by omega
    have hstep := tailSched_succ s₀ (k + 1)
    rw [h1] at hstep
    have h2 : s₀ + (k + 1) + 1 = s₀ + k + 1 + 1 := by omega
    rw [h2, hstep]
    exact CFDiscLt.append hne ih (by
      have := hblock (k + 1)
      rwa [h1] at this)

/-! ## Locating the stage of a position -/

theorem wSched_length_ge (s k : ℕ) :
    (wSched s).length + k ≤ (wSched (s + k)).length :=
  sched_length_ge s k

/-- Every position `p` past stage `s₁` lies in a definite stage window
`[|wSched s|, |wSched (s+1)|)` with `s ≥ s₁`. -/
theorem exists_stage (s₁ p : ℕ) (hp : (wSched s₁).length ≤ p) :
    ∃ s, s₁ ≤ s ∧ (wSched s).length ≤ p ∧ p < (wSched (s + 1)).length := by
  classical
  set Q : ℕ → Prop := fun k => (wSched (s₁ + k)).length ≤ p with hQdef
  have hQ0 : Q 0 := by simpa [hQdef] using hp
  have hQbig : ¬ Q (p + 1) := by
    have h := wSched_length_ge s₁ (p + 1)
    simp only [hQdef]
    omega
  set k := Nat.findGreatest Q (p + 1) with hkdef
  have hk : Q k := Nat.findGreatest_spec (Nat.zero_le _) hQ0
  have hkb : k ≤ p + 1 := Nat.findGreatest_le _
  have hkne : k ≠ p + 1 := fun h => hQbig (h ▸ hk)
  have hk1 : ¬ Q (k + 1) :=
    Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (by omega)
  refine ⟨s₁ + k, by omega, hk, ?_⟩
  have h2 : s₁ + k + 1 = s₁ + (k + 1) := by omega
  rw [h2]
  simp only [hQdef] at hk1
  omega

/-! ## CF normality of `xstar` -/

/-- **CF normality of `xstar`** (fitting-window frequency form, B–Y §2.2):
for every genuine CF pattern `v`, the frequency of `v` among the windows of
the length-`p` digit prefix of `xstar` tends to `γ(I_v)`. -/
theorem xstar_cf_freq_tendsto (v : List ℕ) (hne : v ≠ [])
    (hpos : ∀ a ∈ v, 1 ≤ a) :
    Filter.Tendsto
      (fun p => (countOccurrences v (cfPrefix p) : ℝ) / p)
      Filter.atTop (nhds ((gaussMeasure (cfCylinder v)).toReal)) := by
  set γv := (gaussMeasure (cfCylinder v)).toReal with hγdef
  obtain ⟨hγ0, hγ1⟩ := gaussMeasure_toReal_mem_Icc (cfCylinder v)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε5 : 0 < ε / 5 := by positivity
  have hv1 : (1 : ℝ) ≤ v.length := by
    exact_mod_cast List.length_pos_of_ne_nil hne
  obtain ⟨T, hT1, hTmem, hTmargin, hTinv⟩ := exists_level_margin v hne hpos hε5
  obtain ⟨s₀, hs₀⟩ := sched_t_eventually T
  have hchain : ∀ k, CFDiscLt v (tailSched s₀ (s₀ + k + 1)) γv (ε / 5) :=
    tailSched_cfDiscLt v hne T hTmem hTmargin s₀ (hs₀ (s₀ + 1) (by omega))
  set L₀ := (wSched s₀).length with hL₀
  obtain ⟨K₁, hK₁⟩ := exists_nat_ge (((L₀ : ℝ) + v.length) / (ε / 5))
  obtain ⟨K₂, hK₂⟩ := exists_nat_ge ((v.length : ℝ) / (ε / 5))
  set K := max (max K₁ K₂) 1 with hK
  -- boundary: whole scheduled words past stage `s₀ + K` are `2ε/5`-good
  have hbound : ∀ s, s₀ + K ≤ s → CFDiscLt v (wSched s) γv (2 * (ε / 5)) := by
    intro s hs
    set k := s - s₀ with hk
    have hks : s = s₀ + k := by omega
    have hk1 : 1 ≤ k := by omega
    have htail : CFDiscLt v (tailSched s₀ s) γv (ε / 5) := by
      have h := hchain (k - 1)
      have h2 : s₀ + (k - 1) + 1 = s := by omega
      rwa [h2] at h
    have hlen : (K : ℕ) ≤ (tailSched s₀ s).length := by
      have h := le_tailSched_length s₀ k
      rw [← hks] at h
      omega
    have hshort : ((wSched s₀).length : ℝ) + ((v.length : ℝ) - 1)
        < (ε / 5) * (tailSched s₀ s).length := by
      have hKk : ((L₀ : ℝ) + v.length) ≤ (ε / 5) * K₁ := by
        rw [div_le_iff₀ hε5] at hK₁
        linarith
      have hK₁K : (K₁ : ℝ) ≤ K := by
        exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)
      have hKlen : (K : ℝ) ≤ (tailSched s₀ s).length := by
        exact_mod_cast hlen
      have := mul_le_mul_of_nonneg_left (le_trans hK₁K hKlen) hε5.le
      rw [hL₀] at hKk
      linarith
    have h := cfDiscLt_short_append hne hγ0 hγ1 htail hshort
    have hsplit := wSched_eq_append_tail s₀ k
    rw [← hks] at hsplit
    rwa [← hsplit] at h
  -- interior shortness: the next block is short relative to the word
  have hshort2 : ∀ s, s₀ + K ≤ s →
      ((uSched s).length : ℝ) + ((v.length : ℝ) - 1)
        < 2 * (ε / 5) * (wSched s).length := by
    intro s hs
    set t := tSched (s + 1) with htdef
    have hTt : T ≤ t := hs₀ (s + 1) (by omega)
    have ht1 : 1 ≤ t := le_trans hT1 hTt
    have htR : (0 : ℝ) < t := by exact_mod_cast ht1
    have hdom := uSched_dominance s
    have hdomR : (t : ℝ) * (uSched s).length ≤ (wSched s).length := by
      exact_mod_cast hdom
    have hLpos : (0 : ℝ) ≤ ((wSched s).length : ℝ) := Nat.cast_nonneg _
    -- |u| ≤ L/t ≤ (ε/10)·L
    have hu : ((uSched s).length : ℝ)
        ≤ (ε / 5 / 2) * (wSched s).length := by
      have hinv := hTinv t hTt
      have h1 : ((uSched s).length : ℝ) ≤ (wSched s).length * (1 / t) := by
        rw [mul_one_div, le_div_iff₀ htR]
        linarith
      calc ((uSched s).length : ℝ) ≤ (wSched s).length * (1 / t) := h1
        _ ≤ (wSched s).length * (ε / 5 / 2) :=
          mul_le_mul_of_nonneg_left hinv hLpos
        _ = (ε / 5 / 2) * (wSched s).length := by ring
    -- |v| ≤ (ε/5)·L
    have hvL : (v.length : ℝ) ≤ (ε / 5) * (wSched s).length := by
      have hK₂K : (K₂ : ℕ) ≤ K :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hlen : (K₂ : ℕ) ≤ (wSched s).length := by
        have h1 := wSched_length_ge s₀ (s - s₀)
        have h2 : s₀ + (s - s₀) = s := by omega
        rw [h2] at h1
        omega
      have hlenR : (K₂ : ℝ) ≤ (wSched s).length := by exact_mod_cast hlen
      have hvK : (v.length : ℝ) ≤ (ε / 5) * K₂ := by
        rw [div_le_iff₀ hε5] at hK₂
        linarith
      calc (v.length : ℝ) ≤ (ε / 5) * K₂ := hvK
        _ ≤ (ε / 5) * (wSched s).length :=
          mul_le_mul_of_nonneg_left hlenR hε5.le
    nlinarith
  -- interior: every prefix past stage `s₀ + K` is `4ε/5`-good
  have hprefix : ∀ p, (wSched (s₀ + K)).length ≤ p →
      CFDiscLt v (cfPrefix p) γv (2 * (2 * (ε / 5))) := by
    intro p hp
    obtain ⟨s, hs1, hsp, hsp1⟩ := exists_stage (s₀ + K) p hp
    have hdecomp : cfPrefix p = wSched s ++ (uSched s).take (p - (wSched s).length) := by
      rw [cfPrefix_take hsp1.le, cfPrefix_eq_wSched, wSched_succ,
        List.take_append, List.take_of_length_le hsp]
    rw [hdecomp]
    exact cfDiscLt_append_take hne hγ0 hγ1 (hbound s hs1) (hshort2 s hs1) _
  -- convert to the metric statement
  set N := max (wSched (s₀ + K)).length 1 with hN
  refine ⟨N, fun p hp => ?_⟩
  have hp1 : 1 ≤ p := le_trans (le_max_right _ _) hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  have h := hprefix p (le_trans (le_max_left _ _) hp)
  rw [CFDiscLt, cfPrefix_length] at h
  rw [Real.dist_eq]
  have heq : (countOccurrences v (cfPrefix p) : ℝ) / p - γv
      = ((countOccurrences v (cfPrefix p) : ℝ) - γv * p) / p := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpR, div_lt_iff₀ hpR]
  calc |(countOccurrences v (cfPrefix p) : ℝ) - γv * p|
      < 2 * (2 * (ε / 5)) * p := h
    _ ≤ ε * p := by nlinarith
  -- (4ε/5 < ε)

end NormalNumbers
