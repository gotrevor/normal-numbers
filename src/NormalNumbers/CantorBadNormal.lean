/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SchmidtGames
import NormalNumbers.CantorLiouvilleAll
import NormalNumbers.EntropyProfiles

/-!
# `K ∩ BAD ∩ normal`: a badly approximable Cantor point normal to every base prime to 3

Row 2 of `docs/OPEN-PROBLEMS-SWEEP-2026-10-04.md`, the triple of the same shape as Bugeaud 2012
§10.37 (which `CantorLiouvilleAll` answered for Liouville numbers).  The three sets meet pairwise:

* `K ∩ BAD`: Kristensen–Thorn–Velani, Kleinbock–Weiss (full dimension `log 2 / log 3`; Bugeaud
  2012 p. 167); here `SchmidtGames.le_dimH_U_inter_Bad_inter_cantor_of`, from cited BFS inputs;
* `K ∩ N(b)` for `3 ∤ b`: Cassels 1959, Schmidt 1960; here `CantorLiouvilleAll`;
* `BAD ∩ N`: Kaufman 1980; here `BadNormal.exists_computable_absNormal_bad`.

Bugeaud p. 167 also records that `μ_K`-almost no point of `K` is badly approximable, so the
Cantor measure that carries the Cassels argument gives zero mass to the target set.

**Freshness.**  The 2026-10-04 sweep's prior-art log found the triple unrecorded (about 60%).
-/

namespace NormalNumbers.CantorBadNormal

open SchmidtGames MeasureTheory Filter Topology
open CantorLiouville CantorLiouvilleAll DecayAeNormal ExplicitSquare

/-! ## Reduction: a law on `K ∩ Bad` with a Cassels power saving

Everything in this section is proved.  The headline follows from one law (`Law`) and the
power-saving second moment (`CasselsPower`) for each base prime to 3
(`exists_of_law`). -/

/-- The Cantor point with ternary digit `2` exactly where the selector `σ` is `true`. -/
noncomputable def cpt (σ : ℕ → Bool) : ℝ := pt (fun _ => true) σ

theorem cpt_mem_cantorSet (σ : ℕ → Bool) : cpt σ ∈ cantorSet := pt_mem_cantorSet _ _

theorem measurable_cpt : Measurable cpt := measurable_pt _

/-- A law on `K ∩ Bad`: fair coins pushed through a measurable digit selector `φ` whose points
are all badly approximable. -/
structure Law where
  φ : (ℕ → Bool) → (ℕ → Bool)
  meas : Measurable φ
  bad : ∀ ω, cpt (φ ω) ∈ Bad

/-- **Cassels power saving** for the law `L` in base `b`: for each frequency `h ≠ 0`, the
second moment of the Weyl sum of `h bᵏ x` is `O(N^{2−δ})`. -/
def CasselsPower (L : Law) (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure ≤
      C * (N : ℝ) ^ 2 * (N : ℝ) ^ (-δ)

/-- Any power saving is summable along `CantorLiouville.sched`. -/
theorem summable_sched_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j => (sched j : ℝ) ^ (-δ) := by
  have hB := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (ev_log_le (r := 1 / 2)
    (ε := δ / 2) (by norm_num) (by positivity))
  refine Summable.of_norm_bounded_eventually summable_inv_sq_nat ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hB, eventually_ge_atTop 1] with j hjB hj1
  have hs : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.le _), ← exp_neg_two_log j hj1]
  calc (sched j : ℝ) ^ (-δ) ≤ (Real.exp (Real.sqrt j)) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (exp_sqrt_le_sched j hj1) (by linarith)
    _ = Real.exp (-(δ * Real.sqrt j)) := by rw [← Real.exp_mul]; ring_nf
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        rw [Real.sqrt_eq_rpow]; nlinarith

/-- A logarithmic saving `(log N)^{−δ}`, `δ > 2`, is summable along `sched` (`log sched j ≥ √j`). -/
theorem summable_sched_log_rpow {δ : ℝ} (hδ : 2 < δ) :
    Summable fun j => (Real.log (sched j : ℝ)) ^ (-δ) := by
  have hs : Summable fun j : ℕ => (j : ℝ) ^ (-(δ / 2)) :=
    Real.summable_nat_rpow.2 (by linarith)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hs
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [sched]; exact Real.rpow_nonneg le_rfl _
    · have hn : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
      have := (Real.le_log_iff_exp_le hn).2 (exp_sqrt_le_sched j hj)
      exact Real.rpow_nonneg ((Real.sqrt_nonneg _).trans this) _
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [sched]
      rw [Real.zero_rpow (by linarith)]
      exact Real.rpow_nonneg le_rfl _
    · have hn : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
      have hl := (Real.le_log_iff_exp_le hn).2 (exp_sqrt_le_sched j hj)
      have hsq : 0 < Real.sqrt j := Real.sqrt_pos.2 (by exact_mod_cast hj)
      calc Real.log (sched j : ℝ) ^ (-δ) ≤ (Real.sqrt j) ^ (-δ) :=
            Real.rpow_le_rpow_of_nonpos hsq hl (by linarith)
        _ = (j : ℝ) ^ (-(δ / 2)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]; ring_nf

/-- **Cassels rate** for `L` in base `b`: the second moment is `C N² W(N)` for a rate `W` that is
summable along `CantorLiouville.sched` (`sched j ≈ e^{√j}`, so `W = (log N)^{−1−ε}·…` such as
`(log N)^{−3}` already suffices).  Weaker than `CasselsPower`. -/
def CasselsRate (L : Law) (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N →
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure ≤
      C * (N : ℝ) ^ 2 * W N

theorem casselsRate_of_casselsPower {L : Law} {b : ℕ} (hL : CasselsPower L b) : CasselsRate L b :=
  fun h hh => by
    obtain ⟨C, δ, hδ, hC⟩ := hL h hh
    exact ⟨C, fun N => (N : ℝ) ^ (-δ), summable_sched_rpow hδ, hC⟩

/-- **Rate ⇒ a.e. normal.**  Proved (DEL along `sched`). -/
theorem ae_isNormal_of_casselsRate (L : Law) {b : ℕ} (hb : 2 ≤ b) (hL : CasselsRate L b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (cpt (L.φ ω)) := by
  refine ae_isNormal_of_secondMoment coinMeasure hb _ (measurable_cpt.comp L.meas) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  obtain ⟨C, W, hW, hC⟩ := hL h hh
  refine (hW.mul_left C).of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
    (fun j => ?_)
  have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := hC (sched j) (one_le_sched j)
    _ = _ := by ring

/-- **Power saving ⇒ a.e. normal.**  Proved (DEL along `sched`). -/
theorem ae_isNormal_of_casselsPower (L : Law) {b : ℕ} (hb : 2 ≤ b) (hL : CasselsPower L b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (cpt (L.φ ω)) := by
  refine ae_isNormal_of_secondMoment coinMeasure hb _ (measurable_cpt.comp L.meas) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  obtain ⟨C, δ, hδ, hC⟩ := hL h hh
  refine ((summable_sched_rpow hδ).mul_left C).of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
    (fun j => ?_)
  have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := hC (sched j) (one_le_sched j)
    _ = _ := by ring

theorem cpt_eq_cantorPt (σ : ℕ → Bool) :
    cpt σ = EntropyProfiles.cantorPt (fun i => if σ i then 1 else 0) := by
  unfold cpt pt EntropyProfiles.cantorPt
  congr 1; funext i
  by_cases hσ : σ i <;> simp [ptDigit, hσ]

/-- **Known-false control: no law on `K` has a Cassels rate in base 3.**  Proved: a rate would give a
3-normal Cantor point (`ae_isNormal_of_casselsRate`), which `not_isNormal_three_pow_cantorPt` forbids.
So any proof of the crux (`midStages`) must use `3 ∤ b`. -/
theorem not_casselsRate_three (L : Law) : ¬ CasselsRate L 3 := by
  intro hL
  obtain ⟨ω, hω⟩ := (ae_isNormal_of_casselsRate L (by norm_num) hL).exists
  rw [cpt_eq_cantorPt] at hω
  exact EntropyProfiles.not_isNormal_three_pow_cantorPt _ (k := 1) one_pos (by simpa using hω)

/-- **The reduction.**  Proved: a law on `K ∩ Bad` with a Cassels rate in every base
prime to 3 has a point with all three properties. -/
theorem exists_of_law (L : Law) (hL : ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → CasselsRate L b) :
    ∃ x : ℝ, x ∈ cantorSet ∧ x ∈ Bad ∧ ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b x := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cpt (L.φ ω)) := by
    rw [ae_all_iff]; intro b
    by_cases hb : 2 ≤ b
    · by_cases h3 : 3 ∣ b
      · exact Eventually.of_forall fun _ _ h => absurd h3 h
      · filter_upwards [ae_isNormal_of_casselsRate L hb (hL b hb h3)] with ω hω _ _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hb
  obtain ⟨ω, hω⟩ := hall.exists
  exact ⟨_, cpt_mem_cantorSet _, L.bad ω, hω⟩

/-! ## The deletion descent

Blocks of `2r` ternary digits (selectors in `{0, 2}`).  At the stage whose prefix `w` has length
`L = 2rs`, a child `w ++ u` is *alive* when its cylinder avoids every obstacle `B(p/q, 2c/q²)`
charged to this stage, `3^{L−r} ≤ q² < 3^{L+r}`.  The coin block picks the child; a dead pick is
replaced by an alive one.  Constants: `r = 5`, `c = 3⁻¹⁶/4` (`descentLaw`). -/

/-- Left endpoint of the ternary cylinder with digit selectors `w`. -/
noncomputable def cylLeft (w : List Bool) : ℝ :=
  ∑ i ∈ Finset.range w.length, (if w.getD i false then 2 else 0) / (3 : ℝ) ^ (i + 1)

/-- The closed cylinder of `w`. -/
def cyl (w : List Bool) : Set ℝ := Set.Icc (cylLeft w) (cylLeft w + 1 / 3 ^ w.length)

/-- The child `w ++ u` avoids every obstacle charged to the stage with prefix `w`. -/
def Alive (r : ℕ) (c : ℝ) (w u : List Bool) : Prop :=
  ∀ (p : ℤ) (q : ℕ), 0 < q → (3 : ℝ) ^ w.length ≤ (q : ℝ) ^ 2 * 3 ^ r →
    (q : ℝ) ^ 2 * 3 ^ r < 3 ^ (w.length + 2 * r) →
      ∀ y ∈ cyl (w ++ u), 2 * c / (q : ℝ) ^ 2 ≤ |y - p / q|

open Classical in
/-- The child selector: keep the coin block if alive, else some alive block (if any). -/
noncomputable def sel (r : ℕ) (c : ℝ) (w u : List Bool) : List Bool :=
  if Alive r c w u then u else
    if h : ∃ v : List Bool, v.length = 2 * r ∧ Alive r c w v then h.choose else u

/-- The descent prefix after `s` stages, from coins `ω`. -/
noncomputable def build (r : ℕ) (c : ℝ) : ℕ → (ℕ → Bool) → List Bool
  | 0, _ => []
  | s + 1, ω => build r c s ω ++ sel r c (build r c s ω) (List.ofFn fun i : Fin (2 * r) => ω (2 * r * s + i))

/-- The digit selector of the descent point. -/
noncomputable def descent (r : ℕ) (c : ℝ) (ω : ℕ → Bool) (i : ℕ) : Bool :=
  (build r c (i + 1) ω).getD i false

section Meas

local instance : MeasurableSpace (List Bool) := ⊤

local instance : MeasurableSingletonClass (List Bool) := ⟨fun _ => trivial⟩

theorem measurable_build (r : ℕ) (c : ℝ) (s : ℕ) : Measurable (build r c s) := by
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
    have hb : Measurable fun ω : ℕ → Bool => (fun i : Fin (2 * r) => ω (2 * r * s + i)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    have hg : Measurable fun x : List Bool × (Fin (2 * r) → Bool) =>
        x.1 ++ sel r c x.1 (List.ofFn x.2) := measurable_of_countable _
    exact hg.comp (ih.prodMk hb)

theorem measurable_descent (r : ℕ) (c : ℝ) : Measurable (descent r c) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact (measurable_from_top (f := fun l : List Bool => l.getD i false)).comp
    (measurable_build r c (i + 1))

end Meas

/-- The descent constants: `r = 5`, `c = 3⁻¹⁶ / 4`. -/
noncomputable def c₀ : ℝ := 1 / (4 * 3 ^ 16)

/-- Child index of a 10-digit selector block. -/
def J (f : Fin 10 → Bool) : ℕ := ∑ i : Fin 10, (if f i then 2 else 0) * 3 ^ (9 - (i : ℕ))

theorem J_lt (f : Fin 10 → Bool) : J f < 3 ^ 10 := by
  revert f; unfold J; native_decide

theorem J_inj : ∀ f g : Fin 10 → Bool, J f = J g → f = g := by
  unfold J; native_decide

theorem cylLeft_append (w u : List Bool) :
    cylLeft (w ++ u) = cylLeft w +
      ∑ i ∈ Finset.range u.length, (if u.getD i false then 2 else 0) / (3 : ℝ) ^ (w.length + i + 1) := by
  unfold cylLeft
  rw [List.length_append, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [List.getD_append _ _ _ _ hi]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp

theorem cylLeft_child (w : List Bool) (f : Fin 10 → Bool) :
    cylLeft (w ++ List.ofFn f) = cylLeft w + (J f : ℝ) * (1 / 3 ^ (w.length + 10)) := by
  rw [cylLeft_append]
  congr 1
  simp only [List.length_ofFn, J, Finset.sum_range_succ, Finset.sum_range_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp [List.getD_eq_getElem?_getD, Fin.succ]
  have h : ∀ (b : Bool) (c : ℝ), (if b = true then c else 0) = c * (b.toNat : ℝ) := by
    intro b c; cases b <;> simp
  simp only [h]
  field_simp
  ring

theorem sep_rat {p p' : ℤ} {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hne : (p : ℝ) / q ≠ p' / q') : 1 / ((q : ℝ) * q') ≤ |(p : ℝ) / q - p' / q'| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have heq : (p : ℝ) / q - p' / q' = ((p * q' - p' * q : ℤ) : ℝ) / ((q : ℝ) * q') := by
    push_cast; field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * q')]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hz : p * q' - p' * q ≠ 0 := by
    intro h; apply hne
    rw [div_eq_div_iff hq0.ne' hq0'.ne']
    have : ((p * q' - p' * q : ℤ) : ℝ) = 0 := by exact_mod_cast h
    push_cast at this; linarith
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hz


open UniformBad in
/-- **Bucket count.**  Dead children each carry a centre `v f` within `ℓ/6` of their cylinder;
centres lie in `B` buckets of width `sp` above `a − ℓ/6` and distinct centres are `sp`-separated.
Then at most `2B` children are dead. -/
theorem card_le_of_buckets (a ℓ sp : ℝ) (hℓ : 0 < ℓ) (hsp : 0 < sp) (B : ℕ)
    (D : Finset (Fin 10 → Bool)) (v : (Fin 10 → Bool) → ℝ)
    (hnear : ∀ f ∈ D, ∃ y ∈ Set.Icc (a + (J f : ℝ) * ℓ) (a + (J f : ℝ) * ℓ + ℓ),
      y ∈ Set.Icc (v f - ℓ / 6) (v f + ℓ / 6))
    (hrange : ∀ f ∈ D, (v f - (a - ℓ / 6)) / sp < B)
    (hsep : ∀ f ∈ D, ∀ g ∈ D, v f ≠ v g → sp ≤ |v f - v g|) :
    D.card ≤ 2 * B := by
  classical
  set lo := a - ℓ / 6
  set β : (Fin 10 → Bool) → ℕ := fun f => ⌊(v f - lo) / sp⌋₊ with hβ
  have hvlo : ∀ f ∈ D, 0 ≤ v f - lo := by
    intro f hf
    obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := hnear f hf
    have : (0 : ℝ) ≤ J f := by positivity
    have : 0 ≤ (J f : ℝ) * ℓ := by positivity
    simp only [lo]; linarith
  have hsame : ∀ f ∈ D, ∀ g ∈ D, β f = β g → v f = v g := by
    intro f hf g hg hfg
    by_contra hne
    have h1 := Nat.floor_le (div_nonneg (hvlo f hf) hsp.le)
    have h2 := Nat.lt_floor_add_one ((v f - lo) / sp)
    have h3 := Nat.floor_le (div_nonneg (hvlo g hg) hsp.le)
    have h4 := Nat.lt_floor_add_one ((v g - lo) / sp)
    simp only [hβ] at hfg
    rw [hfg] at h1 h2
    have : |(v f - lo) / sp - (v g - lo) / sp| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hsp, div_lt_one hsp] at this
    have := hsep f hf g hg hne
    simp at *; linarith
  have hfib : ∀ t ∈ D.image β, (D.filter fun x => β x = t).card ≤ 2 := by
    intro t ht
    obtain ⟨f₀, hf₀D, hf₀⟩ := Finset.mem_image.1 ht
    set F := D.filter fun x => β x = t
    rw [← Finset.card_image_of_injective F (fun f g h => J_inj f g h)]
    refine le_trans (Finset.card_le_card ?_) (card_children_le (v f₀) (ℓ / 6) a ℓ (by linarith) (3 ^ 10))
    intro j hj
    obtain ⟨f, hfF, rfl⟩ := Finset.mem_image.1 hj
    have hfD := (Finset.mem_filter.1 hfF).1
    have hfv : v f = v f₀ := hsame f hfD f₀ hf₀D (by rw [(Finset.mem_filter.1 hfF).2, hf₀])
    obtain ⟨y, hy1, hy2⟩ := hnear f hfD
    rw [hfv] at hy2
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (J_lt f), y, hy2, ?_⟩
    push_cast; exact hy1
  have hcard := Finset.card_le_mul_card_image D 2 hfib
  have himg : (D.image β).card ≤ B := by
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range B))
    intro t ht
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_range.2 ((Nat.floor_lt' (by
      rintro rfl; have := hrange f hf; have := div_nonneg (hvlo f hf) hsp.le; simp at *; linarith)).2
      (by exact_mod_cast hrange f hf))
  omega

open Classical in
/-- **Dead children at a stage: at most 488 of 1024.** -/
theorem card_dead_le (w : List Bool) :
    ((Finset.univ : Finset (Fin 10 → Bool)).filter fun f => ¬ Alive 5 c₀ w (List.ofFn f)).card ≤ 488 := by
  classical
  set D := (Finset.univ : Finset (Fin 10 → Bool)).filter fun f => ¬ Alive 5 c₀ w (List.ofFn f)
  have hdead : ∀ f : Fin 10 → Bool, ∃ pq : ℤ × ℕ, f ∈ D → (0 < pq.2 ∧
      (3 : ℝ) ^ w.length ≤ (pq.2 : ℝ) ^ 2 * 3 ^ 5 ∧ (pq.2 : ℝ) ^ 2 * 3 ^ 5 < 3 ^ (w.length + 2 * 5) ∧
      ∃ y ∈ cyl (w ++ List.ofFn f), |y - pq.1 / pq.2| < 2 * c₀ / (pq.2 : ℝ) ^ 2) := by
    intro f
    by_cases hf : f ∈ D
    · have := (Finset.mem_filter.1 hf).2
      unfold Alive at this; push Not at this
      obtain ⟨p, q, hq, h1, h2, y, hy, hlt⟩ := this
      exact ⟨(p, q), fun _ => ⟨hq, h1, h2, y, hy, hlt⟩⟩
    · exact ⟨(0, 1), fun h => absurd h hf⟩
  choose pq hpq using hdead
  set L := w.length
  set a := cylLeft w
  set T : ℝ := (3 : ℝ) ^ L with hT
  have hTpos : 0 < T := by positivity
  set ℓ : ℝ := 1 / (T * 3 ^ 10) with hℓ
  set sp : ℝ := 1 / (T * 3 ^ 5) with hsp
  have hℓpos : 0 < ℓ := by positivity
  have hsppos : 0 < sp := by positivity
  set v : (Fin 10 → Bool) → ℝ := fun f => ((pq f).1 : ℝ) / (pq f).2 with hv
  have hrad : ∀ f ∈ D, 2 * c₀ / ((pq f).2 : ℝ) ^ 2 ≤ ℓ / 6 := by
    intro f hf
    obtain ⟨hq, h1, -, -⟩ := hpq f hf
    have hq0 : (0:ℝ) < (pq f).2 := by exact_mod_cast hq
    have hq2 : (0 : ℝ) < ((pq f).2 : ℝ) ^ 2 := by positivity
    rw [hℓ, c₀, div_le_iff₀ hq2]
    field_simp
    nlinarith
  have hchild : ∀ f, cyl (w ++ List.ofFn f) = Set.Icc (a + (J f : ℝ) * ℓ) (a + (J f : ℝ) * ℓ + ℓ) := by
    intro f
    unfold cyl
    rw [cylLeft_child, List.length_append, List.length_ofFn, pow_add, ← hT]
  have hnear : ∀ f ∈ D, ∃ y ∈ Set.Icc (a + (J f : ℝ) * ℓ) (a + (J f : ℝ) * ℓ + ℓ),
      y ∈ Set.Icc (v f - ℓ / 6) (v f + ℓ / 6) := by
    intro f hf
    obtain ⟨-, -, -, y, hy, hlt⟩ := hpq f hf
    rw [hchild] at hy
    have := (hlt.trans_le (hrad f hf)).le
    rw [abs_le] at this
    exact ⟨y, hy, ⟨by simp only [hv]; linarith [this.1, this.2], by simp only [hv]; linarith [this.1, this.2]⟩⟩
  have hrange : ∀ f ∈ D, (v f - (a - ℓ / 6)) / sp < (244 : ℕ) := by
    intro f hf
    obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := hnear f hf
    have hJ : (J f : ℝ) + 1 ≤ 3 ^ 10 := by
      have := J_lt f; exact_mod_cast (by omega : J f + 1 ≤ 3 ^ 10)
    have hℓT : (3 : ℝ) ^ 10 * ℓ = 1 / T := by rw [hℓ]; field_simp
    have hup : v f - (a - ℓ / 6) ≤ 1 / T + ℓ / 3 := by
      have : (J f : ℝ) * ℓ + ℓ ≤ 3 ^ 10 * ℓ := by nlinarith
      linarith
    rw [div_lt_iff₀ hsppos]
    have : 1 / T + ℓ / 3 < 244 * sp := by
      rw [hℓ, hsp]; field_simp; norm_num
    push_cast; linarith
  have hsep : ∀ f ∈ D, ∀ g ∈ D, v f ≠ v g → sp ≤ |v f - v g| := by
    intro f hf g hg hne
    have hsep := sep_rat (hpq f hf).1 (hpq g hg).1 hne
    have hf0 : (0:ℝ) < (pq f).2 := by exact_mod_cast (hpq f hf).1
    have hg0 : (0:ℝ) < (pq g).2 := by exact_mod_cast (hpq g hg).1
    have hqq : ((pq f).2 : ℝ) * (pq g).2 < T * 3 ^ 5 := by
      have hf2 := (hpq f hf).2.2.1; have hg2 := (hpq g hg).2.2.1
      rw [pow_add, ← hT] at hf2 hg2
      norm_num at hf2 hg2
      have ha : ((pq f).2 : ℝ) ^ 2 < T * 3 ^ 5 := by nlinarith
      have hb : ((pq g).2 : ℝ) ^ 2 < T * 3 ^ 5 := by nlinarith
      nlinarith [sq_nonneg (((pq f).2 : ℝ) - (pq g).2)]
    have : sp < 1 / (((pq f).2 : ℝ) * (pq g).2) := by
      rw [hsp]; exact one_div_lt_one_div_of_lt (by positivity) hqq
    simp only [hv]; linarith
  exact card_le_of_buckets a ℓ sp hℓpos hsppos 244 D v hnear hrange hsep

/-- **Game half: an alive child always exists.**  Proved.

English proof.  Fix `w`, `L = |w|`.  Charged rationals have `q² < 3^{L+5}`, so distinct ones are
`3^{−L−5}`-separated; those whose obstacle (radius `2c₀/q² ≤ 3^{−L−10}/6`) meets the parent
cylinder (length `3^{−L}`) fall in 244 buckets of width `3^{−L−5}`, one centre each.  Children are `2¹⁰` cylinders of length
`3^{−L−10}`, pairwise separated by gaps at least their length, so each obstacle meets at most 2
children (`card_children_le`).  `2 · 244 = 488 < 1024`. -/
theorem exists_alive (w : List Bool) : ∃ u : List Bool, u.length = 2 * 5 ∧ Alive 5 c₀ w u := by
  classical
  by_contra hcon
  push Not at hcon
  have h := card_dead_le w
  rw [Finset.filter_true_of_mem fun f _ => hcon (List.ofFn f) (by simp)] at h
  simp at h


/-- **The Cantor point lies in the cylinder of each prefix.**  Proved: the tail
`Σ_{i ≥ n} σᵢ · 2 · 3^{−i−1}` lies in `[0, 3^{−n}]`. -/
theorem cpt_mem_cyl (σ : ℕ → Bool) (n : ℕ) : cpt σ ∈ cyl (List.ofFn fun i : Fin n => σ i) := by
  set f : ℕ → ℝ := fun i => (ptDigit (fun _ => true) σ i : ℝ) / (3 : ℝ) ^ (i + 1) with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => by positivity
  have hfle : ∀ i, f i ≤ 2 * (1/3 : ℝ) ^ (i + 1) := fun i => by
    simp only [hf, ptDigit]; rw [one_div_pow]; split_ifs <;> simp [div_eq_mul_inv]
  have hg : Summable fun i : ℕ => 2 * (1/3 : ℝ) ^ (i + 1) :=
    (((summable_geometric_of_lt_one (r := (1/3 : ℝ)) (by norm_num) (by norm_num)).mul_left (1/3)).mul_left 2).congr
      fun i => by rw [pow_succ]; ring
  have hs : Summable f := hg.of_nonneg_of_le hf0 hfle
  have hcpt : cpt σ = ∑' i, f i := rfl
  have hsplit := (hs.sum_add_tsum_nat_add n).symm
  have hhead : ∑ i ∈ Finset.range n, f i = cylLeft (List.ofFn fun i : Fin n => σ i) := by
    unfold cylLeft; rw [List.length_ofFn]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [hf, ptDigit, List.getD_eq_getElem?_getD, hi]
  have htail0 : 0 ≤ ∑' k, f (k + n) := tsum_nonneg fun k => hf0 _
  have htail1 : ∑' k, f (k + n) ≤ 1 / 3 ^ n := by
    have hgn : Summable fun k : ℕ => 2 * (1/3 : ℝ) ^ (k + n + 1) := (summable_nat_add_iff n).2 hg
    calc ∑' k, f (k + n) ≤ ∑' k : ℕ, 2 * (1/3 : ℝ) ^ (k + n + 1) :=
          ((summable_nat_add_iff n).2 hs).tsum_le_tsum (fun k => hfle _) hgn
      _ = ∑' k : ℕ, (2 * (1/3 : ℝ) ^ (n + 1)) * (1/3) ^ k := tsum_congr fun k => by ring
      _ = 1 / 3 ^ n := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          rw [pow_succ, one_div_pow]; norm_num; field_simp
  rw [hcpt, hsplit, hhead]
  unfold cyl; rw [List.length_ofFn]
  exact ⟨by linarith, by linarith⟩


theorem length_sel {r : ℕ} {c : ℝ} {w u : List Bool} (hu : u.length = 2 * r) :
    (sel r c w u).length = 2 * r := by
  unfold sel; split_ifs with h1 h2
  · exact hu
  · exact h2.choose_spec.1
  · exact hu

theorem length_build (r : ℕ) (c : ℝ) (ω : ℕ → Bool) (s : ℕ) :
    (build r c s ω).length = 2 * r * s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [build, ih, length_sel, List.length_ofFn]; ring

theorem build_prefix (r : ℕ) (c : ℝ) (ω : ℕ → Bool) {s t : ℕ} (h : s ≤ t) :
    build r c s ω <+: build r c t ω := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (List.prefix_append _ _)

theorem getD_build (r : ℕ) (hr : 0 < r) (c : ℝ) (ω : ℕ → Bool) {s i : ℕ} (hi : i < 2 * r * s) :
    descent r c ω i = (build r c s ω).getD i false := by
  unfold descent
  have key : ∀ {a b : ℕ}, a ≤ b → i < 2 * r * a →
      (build r c a ω).getD i false = (build r c b ω).getD i false := by
    intro a b hab hia
    obtain ⟨l, hl⟩ := build_prefix r c ω hab
    rw [← hl, List.getD_append _ _ _ _ (by rw [length_build]; exact hia)]
  have h1 : i < 2 * r * (i + 1) := by nlinarith
  rw [key (le_max_left (i+1) s) h1, key (le_max_right (i+1) s) hi]

theorem ofFn_descent (r : ℕ) (hr : 0 < r) (c : ℝ) (ω : ℕ → Bool) (s : ℕ) :
    (List.ofFn fun i : Fin (2 * r * s) => descent r c ω i) = build r c s ω := by
  apply List.ext_getElem
  · simp [length_build]
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    rw [getD_build r hr c ω (by simpa using h1), List.getD_eq_getElem _ _ h2]

theorem sel_alive (w u : List Bool) : Alive 5 c₀ w (sel 5 c₀ w u) := by
  unfold sel; split_ifs with h1 h2
  · exact h1
  · exact h2.choose_spec.2
  · exact absurd (exists_alive w) h2

/-- **The descent point is badly approximable** (given `exists_alive`).  Proved.

English proof.  For `p/q`, take the stage `s` with `3^{10s} ≤ q² 3⁵ < 3^{10s+10}`.  By
`exists_alive` the selected block `u` of stage `s` is alive, and `build (s+1)` is a prefix of
`descent ω` (`build` only appends), so `cpt_mem_cyl` puts `x` in `cyl (build (s+1) ω)`, whence
`|x − p/q| ≥ 2c₀/q² > c₀/q²`.  So `x ∈ BA c₀`. -/
theorem descent_bad (ω : ℕ → Bool) : cpt (descent 5 c₀ ω) ∈ Bad := by
  have hc : (0 : ℝ) < c₀ := by unfold c₀; positivity
  refine Set.mem_iUnion.2 ⟨c₀, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩
  intro p q hq
  set s := Nat.log 3 (q ^ 2 * 3 ^ 5) / 10
  have hne : q ^ 2 * 3 ^ 5 ≠ 0 := by positivity
  have hlo : 3 ^ (10 * s) ≤ q ^ 2 * 3 ^ 5 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le _ _)) (Nat.pow_log_le_self 3 hne)
  have hhi : q ^ 2 * 3 ^ 5 < 3 ^ (10 * s + 10) :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmem := cpt_mem_cyl (descent 5 c₀ ω) (2 * 5 * (s + 1))
  rw [ofFn_descent 5 (by norm_num)] at hmem
  have hal := sel_alive (build 5 c₀ s ω)
    (List.ofFn fun i : Fin (2 * 5) => ω (2 * 5 * s + i))
  have hlen := length_build 5 c₀ ω s
  have := hal p q hq (by rw [hlen]; exact_mod_cast (by simpa [mul_comm] using hlo))
    (by rw [hlen]; exact_mod_cast (by simpa [mul_comm] using hhi)) _ hmem
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have : c₀ / (q : ℝ) ^ 2 < 2 * c₀ / (q : ℝ) ^ 2 := by
    rw [div_lt_div_iff_of_pos_right hq2]; linarith
  linarith

/-- The descent law. -/
noncomputable def descentLaw : Law := ⟨descent 5 c₀, measurable_descent 5 c₀, descent_bad⟩

/-- `|ν̂_L(ξ)|`: the modulus of the Fourier coefficient of the law `L`. -/
noncomputable def fourierAbs (L : Law) (ξ : ℝ) : ℝ :=
  ‖∫ ω, ee (ξ * cpt (L.φ ω)) ∂coinMeasure‖

/-- **Second-moment expansion for any law.**  Proved (copy of `secondMoment_expand_b`). -/
theorem secondMoment_le_fourier (L : Law) (b : ℕ) (h : ℤ) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, fourierAbs L (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) := by
  have hG : Measurable fun ω => cpt (L.φ ω) := measurable_cpt.comp L.meas
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * cpt (L.φ ω))) coinMeasure := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * (b : ℝ) ^ k * cpt (L.φ ω))]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  exact Finset.sum_le_sum fun n _ => norm_sum_le _ _

/-- **Fourier pair-sum power saving**: the averaged `|ν̂|` over the Cassels frequencies
`h(bⁿ − bᵐ)`, `n, m < N`, is `O(N^{2−δ})`. -/
def FourierPairPower (L : Law) (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, fourierAbs L (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) ≤
      C * (N : ℝ) ^ 2 * (N : ℝ) ^ (-δ)

/-- **Fourier pair-sum rate**: `Σ_{n,m<N} |ν̂(h(bⁿ − bᵐ))| ≤ C N² W(N)` with `W` summable along
`sched`. -/
def FourierPairRate (L : Law) (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, fourierAbs L (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) ≤
      C * (N : ℝ) ^ 2 * W N

/-- Proved: the pair-sum rate gives the Cassels rate. -/
theorem casselsRate_of_fourierPairRate {L : Law} {b : ℕ} (hL : FourierPairRate L b) :
    CasselsRate L b := fun h hh => by
  obtain ⟨C, W, hW, hC⟩ := hL h hh
  exact ⟨C, W, hW, fun N hN => (secondMoment_le_fourier L b h N).trans (hC N hN)⟩

/-- Proved: the pair-sum saving gives the Cassels power saving. -/
theorem casselsPower_of_fourierPairPower {L : Law} {b : ℕ} (hL : FourierPairPower L b) :
    CasselsPower L b := fun h hh => by
  obtain ⟨C, δ, hδ, hC⟩ := hL h hh
  exact ⟨C, δ, hδ, fun N hN => (secondMoment_le_fourier L b h N).trans (hC N hN)⟩

/-- **Conjecture node (formerly the crux): the Fourier pair-sum rate for the choose-based
descent law.**  Any `W` summable along `sched` suffices, e.g. `(log N)^{−3}`.  Retired as a
blocking obligation by the 2026-10-05 operator resolution: `descentLaw` replaces dead blocks by
`Classical.choose` (`descent_eq_descentR`, `repC_ok`), so a proof could only use `RepOK repC`,
and `AdversarialReplacement` (55%) says some admissible rule breaks base-2 normality.  The
headline now runs through `resLaw` (`fourierPairRate_resLaw`).  Confidence that this node is
true for the actual `repC`: 50% (it depends on an unspecified choice).

The sweep's guard (`docs/OPEN-PROBLEMS-SWEEP-2026-10-04.md` §2.3) applies: a proof that uses
only that each block's dead fraction is small also proves base-2 normality of a descent
against `B(a/2ⁿ, 2^{−n−C})`, which is false (`perStage_deadCount_not_enough`).  Known-false
sibling inside the mechanism: `b = 3` (`cantor_not_normal_three_pow`). -/
def FourierPairRateChoose : Prop :=
  ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → FourierPairRate descentLaw b

/-- Cassels' second moment for the descent law, from the conjecture node. -/
theorem casselsRate_descent (hC : FourierPairRateChoose) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    CasselsRate descentLaw b :=
  casselsRate_of_fourierPairRate (hC b hb h3)

/-! ## Obstruction: the crux sees the replacement rule only through `Classical.choose`

`sel` replaces a dead coin block by `h.choose`, an alive block about which nothing but
`Alive` is known.  So a proof of `FourierPairRateChoose` is in effect a proof for *every*
alive-valued replacement rule `rep` (`descent_eq_descentR`, `repC_ok`).  The conjecture node
`AdversarialReplacement` says some such rule destroys base-2 normality; if it holds, the crux is
true or false according to the unspecified choice and is not provable from `choose_spec`. -/

open Classical in
/-- The selector with an explicit replacement rule `rep`. -/
noncomputable def selR (rep : List Bool → List Bool) (w u : List Bool) : List Bool :=
  if Alive 5 c₀ w u then u else rep w

/-- The descent prefix with replacement rule `rep`. -/
noncomputable def buildR (rep : List Bool → List Bool) : ℕ → (ℕ → Bool) → List Bool
  | 0, _ => []
  | s + 1, ω => buildR rep s ω ++ selR rep (buildR rep s ω) (List.ofFn fun i : Fin (2 * 5) => ω (2 * 5 * s + i))

/-- The digit selector with replacement rule `rep`. -/
noncomputable def descentR (rep : List Bool → List Bool) (ω : ℕ → Bool) (i : ℕ) : Bool :=
  (buildR rep (i + 1) ω).getD i false

/-- A replacement rule is admissible when it always returns an alive block of the right length. -/
def RepOK (rep : List Bool → List Bool) : Prop :=
  ∀ w, (rep w).length = 2 * 5 ∧ Alive 5 c₀ w (rep w)

open Classical in
/-- The replacement rule hidden in `sel`. -/
noncomputable def repC (w : List Bool) : List Bool :=
  if h : ∃ v : List Bool, v.length = 2 * 5 ∧ Alive 5 c₀ w v then h.choose else []

theorem repC_ok : RepOK repC := fun w => by
  unfold repC; rw [dif_pos (exists_alive w)]; exact (exists_alive w).choose_spec

theorem sel_eq_selR (w u : List Bool) : sel 5 c₀ w u = selR repC w u := by
  unfold sel selR repC; split_ifs with h1 h2 <;> first | rfl | exact absurd (exists_alive w) h2

theorem build_eq_buildR (s : ℕ) (ω : ℕ → Bool) : build 5 c₀ s ω = buildR repC s ω := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [build, buildR, ih, sel_eq_selR]

/-- `descentLaw` is the replacement-rule descent for `repC`.  Proved. -/
theorem descent_eq_descentR : descent 5 c₀ = descentR repC := by
  funext ω i; simp only [descent, descentR, build_eq_buildR]

/-- **Conjecture node (believed, 55%): an adversarial replacement rule breaks base-2 normality.**

Heuristic.  Along a typical path a stage has a dead coin block with probability bounded below
by some `η > 0` (an obstacle `p/q`, `q² ≍ 3^{10s}`, lies within `c₀/q²` of a surviving child
with probability `≍ c₀`, if rationals near `K` behave like random points; cf. He–Liao on
rationals against Cantor cylinders).  On a dead stage the rule sees the whole prefix `w` and
chooses among `≥ 536` alive blocks; ten ternary digits fix `2ᵏ x mod 1` to within `3⁻⁵` for the
`k` with `2ᵏ ≈ 3^{10s+5}`, so it can force `2ᵏ x mod 1 < 1/2`.  That shifts the frequency of
the binary digit `0` by `≍ η / (20 log₂ 3) > 0` compared with the coin choice.

Evidence (`scripts/cantorbad_eta.py`, exact rationals, 600 coin paths × 7 stages, seed 2): dead
coin blocks per stage `7, 2, 0, 0, 0, 1, 0` of 600.  Stages 0–1 are dominated by rationals of `K`
itself (`1/4, 3/4`); at stages 2–6 the rate is `1/3000`, consistent with a small constant `η` but
too few events to separate it from slow decay.  Deeper run (seeds 3–6, 1600 paths × 10 stages):
stages 2–5 give `7/6400`, stages 6–9 give `4/6400`, flat within noise at `η ≈ 10⁻³`; the count
heuristic (rationals equidistributed against `μ_K`) also predicts a constant `≍ 3⁻⁵`-order rate.
Confidence 55%.  The step most in doubt is the lower bound on `η` (a Diophantine
count of rationals near `K`).  Implication: if true, `FourierPairRateChoose` can only be
proved by a law whose replacement is canonical (e.g. uniform resampling among alive blocks),
not by `Classical.choose`. -/
def AdversarialReplacement : Prop :=
  ∃ rep, RepOK rep ∧ ¬ ∀ᵐ ω ∂coinMeasure, IsNormal 2 (cpt (descentR rep ω))

/-- **Conjecture node (believed false, 85%): almost surely only finitely many stages are dead.**

If true, the descent point differs from the coin point `cpt ω` by a ternary rational, so the
headline would follow from Cassels (`μ_K`-a.e. normality to bases prime to 3) and invariance of
normality under rational translation, with no Fourier estimate.  Evidence against: the
dead-stage rate is flat at `≈ 10⁻³` over stages 2–9 (see `AdversarialReplacement`), and the
count heuristic gives a constant rate, so `Σ_s P(dead at s) = ∞`. -/
def FinitelyManyDead : Prop :=
  ∀ᵐ ω ∂coinMeasure, ∀ᶠ s in atTop,
    Alive 5 c₀ (build 5 c₀ s ω) (List.ofFn fun i : Fin (2 * 5) => ω (2 * 5 * s + i))

/-- The coin block at stage `s` is dead (the descent intervenes there). -/
def DeadAt (s : ℕ) (ω : ℕ → Bool) : Prop :=
  ¬ Alive 5 c₀ (build 5 c₀ s ω) (List.ofFn fun i : Fin (2 * 5) => ω (2 * 5 * s + i))

/-- **Open node: Cesàro decay of the dead-stage probability**, at a rate summable along
`sched`.  Believed false (80%): the numerics in `AdversarialReplacement` show a flat rate
`η ≈ 10⁻³`.  Recorded because it is exactly what the rule-independent reduction below needs. -/
def DeadRateDecay : Prop :=
  ∃ W : ℕ → ℝ, Summable (fun j => W (sched j)) ∧ ∀ S : ℕ, 1 ≤ S →
    (∑ s ∈ Finset.range S, (coinMeasure {ω | DeadAt s ω}).toReal) ≤ S * W S

/-- **Rule-independent reduction (believed, 75%): dead-stage decay gives the crux.**

English proof.  Write `ν̂(ξ) = E[Π_s X_s]`, `X_s = e(ξ·3^{−10s}·y_s)` for the block digits `y_s`.
Conditioning on the prefix, `E[X_s | F_{s−1}] = ρ_s(ξ) + ε_s`, `ρ_s` the uniform-block character and
`|ε_s| ≤ 2·(4/1024)·1{DeadAt s}`-mass, with additionally `|ε_s| ≤ 8π|ξ|3^{−10(s+1)}·1{dead}` for blocks
finer than `ξ`.  This holds for EVERY admissible replacement rule (only the dead coin mass moves).
Peeling from the top: `|ν̂(ξ)| ≤ Π|ρ_s| + Σ_S P(DeadAt S)·min(1, |ξ|3^{−10S})·Π_{s>S}|ρ_s|`.  For
`ξ = h(bⁿ−bᵐ)`, `3 ∤ b`, the Cantor products decay on average over `(n,m)` (Cassels/Feldman–Smorodinsky),
so only `O(1)` stages near `S ≈ n log₃ b / 10` survive and the pair sum is `O(N² W(N)) + o(N²)` at a
summable rate.  The step most in doubt: a quantitative pair-average of the partial Cantor products.
Consequence: with `AdversarialReplacement`, the crux is essentially equivalent to `DeadRateDecay`. -/
theorem fourierPairRate_descent_of_deadRateDecay (hD : DeadRateDecay) {b : ℕ} (hb : 2 ≤ b)
    (h3 : ¬ 3 ∣ b) : FourierPairRate descentLaw b := by
  sorry

/-! ## The resampling law: dead blocks replaced uniformly from fresh coins

Stage `s` reads the coin blocks `blk ω s t`, `t = 0, 1, 2, …` (disjoint, via `Nat.pair`), and
keeps the first alive one.  So, given the prefix, the stage block is uniform on the alive
children (rejection sampling), not an unspecified choice.  The fallback `repC` is used only on
the null event that no block is alive. -/

/-- The `t`-th coin block of stage `s`: ten fresh coins at `10 · pair(s, t) + i`. -/
def blk (ω : ℕ → Bool) (s t : ℕ) : List Bool :=
  List.ofFn fun i : Fin 10 => ω (10 * Nat.pair s t + i)

open Classical in
/-- The first attempt index `t` whose block is alive (`0` if none is). -/
noncomputable def firstAlive (w : List Bool) (ω : ℕ → Bool) (s : ℕ) : ℕ :=
  Nat.find (p := fun t => Alive 5 c₀ w (blk ω s t) ∨ ¬ ∃ t', Alive 5 c₀ w (blk ω s t'))
    (by by_cases h : ∃ t', Alive 5 c₀ w (blk ω s t')
        · obtain ⟨t, ht⟩ := h; exact ⟨t, Or.inl ht⟩
        · exact ⟨0, Or.inr h⟩)

open Classical in
/-- The resampled stage block: the first alive coin block, else `repC`. -/
noncomputable def selU (w : List Bool) (ω : ℕ → Bool) (s : ℕ) : List Bool :=
  if Alive 5 c₀ w (blk ω s (firstAlive w ω s)) then blk ω s (firstAlive w ω s) else repC w

/-- The resampling descent prefix after `s` stages. -/
noncomputable def buildU : ℕ → (ℕ → Bool) → List Bool
  | 0, _ => []
  | s + 1, ω => buildU s ω ++ selU (buildU s ω) ω s

/-- The resampling descent selector. -/
noncomputable def descentU (ω : ℕ → Bool) (i : ℕ) : Bool := (buildU (i + 1) ω).getD i false

theorem selU_alive (w : List Bool) (ω : ℕ → Bool) (s : ℕ) :
    (selU w ω s).length = 10 ∧ Alive 5 c₀ w (selU w ω s) := by
  unfold selU; split_ifs with h
  · exact ⟨by simp [blk], h⟩
  · exact repC_ok w

theorem length_buildU (ω : ℕ → Bool) (s : ℕ) : (buildU s ω).length = 10 * s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [buildU, ih, (selU_alive _ ω s).1]; ring

theorem buildU_prefix (ω : ℕ → Bool) {s t : ℕ} (h : s ≤ t) : buildU s ω <+: buildU t ω := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (List.prefix_append _ _)

theorem ofFn_descentU (ω : ℕ → Bool) (s : ℕ) :
    (List.ofFn fun i : Fin (10 * s) => descentU ω i) = buildU s ω := by
  have key : ∀ {i a b : ℕ}, a ≤ b → i < 10 * a →
      (buildU a ω).getD i false = (buildU b ω).getD i false := by
    intro i a b hab hia
    obtain ⟨l, hl⟩ := buildU_prefix ω hab
    rw [← hl, List.getD_append _ _ _ _ (by rw [length_buildU]; exact hia)]
  apply List.ext_getElem
  · simp [length_buildU]
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    have hi : i < 10 * s := by simpa using h1
    have h1' : i < 10 * (i + 1) := by omega
    unfold descentU
    rw [key (le_max_left (i+1) s) h1', ← key (le_max_right (i+1) s) hi,
      List.getD_eq_getElem _ _ h2]

section MeasU
local instance : MeasurableSpace (List Bool) := ⊤
local instance : MeasurableSingletonClass (List Bool) := ⟨fun _ => trivial⟩

theorem measurable_blk (s t : ℕ) : Measurable fun ω : ℕ → Bool => blk ω s t := by
  have hb : Measurable fun ω : ℕ → Bool => (fun i : Fin 10 => ω (10 * Nat.pair s t + i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  exact (measurable_of_countable (fun f : Fin 10 → Bool => List.ofFn f)).comp hb

theorem measurable_selU (w : List Bool) (s : ℕ) : Measurable fun ω => selU w ω s := by
  classical
  have hset : ∀ t, MeasurableSet {ω : ℕ → Bool | Alive 5 c₀ w (blk ω s t) ∨
      ¬ ∃ t', Alive 5 c₀ w (blk ω s t')} := by
    intro t
    refine (measurable_blk s t (MeasurableSpace.measurableSet_top (s := {v | Alive 5 c₀ w v}))).union ?_
    have : {ω : ℕ → Bool | ¬ ∃ t', Alive 5 c₀ w (blk ω s t')} =
        ⋂ t', (fun ω => blk ω s t') ⁻¹' {v | Alive 5 c₀ w v}ᶜ := by ext; simp
    change MeasurableSet {ω : ℕ → Bool | ¬ ∃ t', Alive 5 c₀ w (blk ω s t')}
    rw [this]
    exact MeasurableSet.iInter fun t' => measurable_blk s t' MeasurableSpace.measurableSet_top
  have hT : Measurable fun ω => firstAlive w ω s := measurable_find _ hset
  have hB : Measurable fun ω => blk ω s (firstAlive w ω s) := by
    have h2 : Measurable fun x : (ℕ → Bool) × ℕ => blk x.1 s x.2 :=
      measurable_from_prod_countable_left fun t => measurable_blk s t
    exact h2.comp (measurable_id.prodMk hT)
  exact (measurable_from_top (f := fun v : List Bool => if Alive 5 c₀ w v then v else repC w)).comp hB

theorem measurable_buildU (s : ℕ) : Measurable (buildU s) := by
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
    have h2 : Measurable fun x : (ℕ → Bool) × List Bool => x.2 ++ selU x.2 x.1 s :=
      measurable_from_prod_countable_left fun w =>
        (measurable_from_top (f := fun v : List Bool => w ++ v)).comp (measurable_selU w s)
    exact h2.comp (measurable_id.prodMk ih)

theorem measurable_descentU : Measurable descentU := by
  refine measurable_pi_lambda _ fun i => ?_
  exact (measurable_from_top (f := fun l : List Bool => l.getD i false)).comp (measurable_buildU (i + 1))
end MeasU

/-- **Every selector whose stage blocks are alive gives a badly approximable point.**  Proved
(the argument of `descent_bad`, abstracted over how the blocks were chosen). -/
theorem cpt_bad_of_alive (σ : ℕ → Bool) (hσ : ∀ s, ∃ w u : List Bool, w.length = 10 * s ∧
    Alive 5 c₀ w u ∧ w ++ u = List.ofFn fun i : Fin (10 * (s + 1)) => σ i) : cpt σ ∈ Bad := by
  have hc : (0 : ℝ) < c₀ := by unfold c₀; positivity
  refine Set.mem_iUnion.2 ⟨c₀, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩
  intro p q hq
  set s := Nat.log 3 (q ^ 2 * 3 ^ 5) / 10
  have hne : q ^ 2 * 3 ^ 5 ≠ 0 := by positivity
  have hlo : 3 ^ (10 * s) ≤ q ^ 2 * 3 ^ 5 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le _ _)) (Nat.pow_log_le_self 3 hne)
  have hhi : q ^ 2 * 3 ^ 5 < 3 ^ (10 * s + 10) :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨w, u, hlen, hal, hwu⟩ := hσ s
  have hmem := cpt_mem_cyl σ (10 * (s + 1))
  rw [← hwu] at hmem
  have := hal p q hq (by rw [hlen]; exact_mod_cast (by simpa [mul_comm] using hlo))
    (by rw [hlen]; exact_mod_cast (by simpa [mul_comm] using hhi)) _ hmem
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have : c₀ / (q : ℝ) ^ 2 < 2 * c₀ / (q : ℝ) ^ 2 := by
    rw [div_lt_div_iff_of_pos_right hq2]; linarith
  linarith

theorem descentU_bad (ω : ℕ → Bool) : cpt (descentU ω) ∈ Bad :=
  cpt_bad_of_alive _ fun s => ⟨buildU s ω, selU (buildU s ω) ω s, length_buildU ω s,
    (selU_alive _ ω s).2, by rw [ofFn_descentU]; rfl⟩

/-- The resampling law. -/
noncomputable def resLaw : Law := ⟨descentU, measurable_descentU, descentU_bad⟩

/-! ### Independence of the coin blocks

`MS P` is the σ-algebra of the coins whose block key `unpair (j / 10)` satisfies `P`. -/

/-- The σ-algebra of coin `j`. -/
def mcoord (j : ℕ) : MeasurableSpace (ℕ → Bool) :=
  MeasurableSpace.comap (fun ω : ℕ → Bool => ω j) inferInstance

/-- The σ-algebra of the coins in the blocks with key satisfying `P`. -/
def MS (P : ℕ × ℕ → Prop) : MeasurableSpace (ℕ → Bool) :=
  ⨆ j ∈ {j : ℕ | P (Nat.unpair (j / 10))}, mcoord j

theorem idx_key (s t : ℕ) (i : Fin 10) : Nat.unpair ((10 * Nat.pair s t + i) / 10) = (s, t) := by
  rw [show (10 * Nat.pair s t + i) / 10 = Nat.pair s t by omega]; simp

theorem mset_coord {P : ℕ × ℕ → Prop} {s t : ℕ} (hP : P (s, t)) (i : Fin 10) (b : Bool) :
    MeasurableSet[MS P] {ω : ℕ → Bool | ω (10 * Nat.pair s t + i) = b} :=
  le_iSup₂ (f := fun j (_ : j ∈ {j : ℕ | P (Nat.unpair (j / 10))}) => mcoord j)
    (10 * Nat.pair s t + i) (by simp only [Set.mem_setOf_eq, idx_key]; exact hP) _ ⟨{b}, trivial, rfl⟩

theorem mset_blk {P : ℕ × ℕ → Prop} {s t : ℕ} (hP : P (s, t)) (X : Set (List Bool)) :
    MeasurableSet[MS P] {ω : ℕ → Bool | blk ω s t ∈ X} := by
  have : {ω : ℕ → Bool | blk ω s t ∈ X} =
      ⋃ (f : Fin 10 → Bool) (_ : List.ofFn f ∈ X), ⋂ i : Fin 10,
        {ω : ℕ → Bool | ω (10 * Nat.pair s t + i) = f i} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    constructor
    · intro h; exact ⟨fun i => ω (10 * Nat.pair s t + i), h, fun i => rfl⟩
    · rintro ⟨f, hf, hω⟩
      have : blk ω s t = List.ofFn f := by unfold blk; congr 1; funext i; exact hω i
      rw [this]; exact hf
  rw [this]
  exact MeasurableSet.iUnion fun f => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iInter fun i => mset_coord hP i (f i)

theorem MS_mono {P Q : ℕ × ℕ → Prop} (h : ∀ x, P x → Q x) : MS P ≤ MS Q :=
  iSup₂_le fun j hj => le_iSup₂ (f := fun j (_ : j ∈ {j : ℕ | Q (Nat.unpair (j / 10))}) => mcoord j)
    j (h _ hj)

theorem MS_le (P : ℕ × ℕ → Prop) : MS P ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  iSup₂_le fun j _ => (measurable_pi_apply j).comap_le

theorem indep_MS {P Q : ℕ × ℕ → Prop} (h : ∀ x, P x → ¬ Q x) {A B : Set (ℕ → Bool)}
    (hA : MeasurableSet[MS P] A) (hB : MeasurableSet[MS Q] B) :
    coinMeasure (A ∩ B) = coinMeasure A * coinMeasure B := by
  have hind : ProbabilityTheory.iIndep mcoord coinMeasure := by
    have := ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure) (X := fun _ (b : Bool) => b)
      (fun _ => measurable_id)
    exact (ProbabilityTheory.iIndepFun_iff_iIndep _ _ _).1 this
  have hI := ProbabilityTheory.indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le)
    hind (S := {j : ℕ | P (Nat.unpair (j / 10))}) (T := {j : ℕ | Q (Nat.unpair (j / 10))})
    (Set.disjoint_left.2 fun j hP hQ => h _ hP hQ)
  exact (ProbabilityTheory.Indep_iff _ _ _).1 hI A B hA hB

open Classical in
/-- The alive children of `w`, as a finset of selector blocks. -/
noncomputable def aliveSet (w : List Bool) : Finset (Fin 10 → Bool) :=
  Finset.univ.filter fun f => Alive 5 c₀ w (List.ofFn f)


/-- The `t`-th stage-`s` coin block as a vector. -/
def blkVec (ω : ℕ → Bool) (s t : ℕ) : Fin 10 → Bool := fun i => ω (10 * Nat.pair s t + i)

theorem coin_blkVec (s t : ℕ) (F : Finset (Fin 10 → Bool)) :
    coinMeasure {ω | blkVec ω s t ∈ F} = F.card / 1024 := by
  have hm : Measurable fun ω => blkVec ω s t := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hinj : Function.Injective fun i : Fin 10 => 10 * Nat.pair s t + (i : ℕ) :=
    fun a b h => Fin.ext (by simpa using h)
  have hmap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure) hinj
  have h1 : coinMeasure {ω | blkVec ω s t ∈ F} = (coinMeasure.map fun ω => blkVec ω s t) ↑F := by
    rw [Measure.map_apply hm F.finite_toSet.measurableSet]; rfl
  rw [h1]
  unfold coinMeasure
  rw [show (fun ω : ℕ → Bool => blkVec ω s t) = fun ω i => ω (10 * Nat.pair s t + (i : ℕ)) from rfl,
    hmap, ← MeasureTheory.sum_measure_singleton]
  have hs : ∀ f : Fin 10 → Bool,
      Measure.infinitePi (fun _ : Fin 10 => (PMF.uniformOfFintype Bool).toMeasure) {f} = 1 / 1024 := by
    intro f
    rw [Measure.infinitePi_singleton_of_fintype]
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← ENNReal.inv_pow]; norm_num
  simp only [hs, Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div]

theorem coin_blk_eq (s t : ℕ) (f : Fin 10 → Bool) :
    coinMeasure {ω | blk ω s t = List.ofFn f} = 1 / 1024 := by
  have := coin_blkVec s t {f}
  rw [Finset.card_singleton, Nat.cast_one] at this
  rw [← this]; congr 1; ext ω
  simp only [Set.mem_setOf_eq, Finset.mem_singleton, blk]
  exact ⟨fun h => List.ofFn_injective h, fun h => by rw [← h]; rfl⟩

theorem coin_dead (w : List Bool) (s t : ℕ) :
    coinMeasure {ω | ¬ Alive 5 c₀ w (blk ω s t)} = ((1024 - (aliveSet w).card : ℕ) : ENNReal) / 1024 := by
  classical
  have := coin_blkVec s t (Finset.univ \ aliveSet w)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at this
  rw [show Fintype.card (Fin 10 → Bool) = 1024 by simp] at this
  rw [← this]; congr 1; ext ω
  simp [aliveSet, blk, blkVec]

theorem card_aliveSet_pos (w : List Bool) : 0 < (aliveSet w).card := by
  classical
  obtain ⟨u, hu, hal⟩ := exists_alive w
  refine Finset.card_pos.2 ⟨fun i => u[i]'(by omega), ?_⟩
  simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
  convert hal
  apply List.ext_getElem (by simp [hu]); intro i h1 h2; rw [List.getElem_ofFn]; rfl

theorem card_aliveSet_le (w : List Bool) : (aliveSet w).card ≤ 1024 := by
  have := Finset.card_le_univ (aliveSet w); simpa using this

open Classical in
theorem selU_eq_iff {w v : List Bool} (hv : Alive 5 c₀ w v) (ω : ℕ → Bool) (s : ℕ) :
    selU w ω s = v ↔ (∃ t, (∀ t' < t, ¬ Alive 5 c₀ w (blk ω s t')) ∧ blk ω s t = v) ∨
      ((∀ t, ¬ Alive 5 c₀ w (blk ω s t)) ∧ repC w = v) := by
  by_cases hex : ∃ t, Alive 5 c₀ w (blk ω s t)
  · have hspec := Nat.find_spec (p := fun t => Alive 5 c₀ w (blk ω s t) ∨
        ¬ ∃ t', Alive 5 c₀ w (blk ω s t')) (firstAlive._proof_1 w ω s)
    have hT : Alive 5 c₀ w (blk ω s (firstAlive w ω s)) := hspec.resolve_right (not_not.2 hex)
    have hsel : selU w ω s = blk ω s (firstAlive w ω s) := by unfold selU; rw [if_pos hT]
    have hmin : ∀ t' < firstAlive w ω s, ¬ Alive 5 c₀ w (blk ω s t') := fun t' ht' h =>
      Nat.find_min (firstAlive._proof_1 w ω s) ht' (Or.inl h)
    rw [hsel]
    constructor
    · intro h; exact Or.inl ⟨_, hmin, h⟩
    · rintro (⟨t, ht, hb⟩ | ⟨hn, _⟩)
      · have hat : Alive 5 c₀ w (blk ω s t) := hb ▸ hv
        have : firstAlive w ω s = t := by
          rcases lt_trichotomy (firstAlive w ω s) t with h | h | h
          · exact absurd hT (ht _ h)
          · exact h
          · exact absurd hat (hmin _ h)
        rw [this, hb]
      · exact absurd hex (by push Not; exact hn)
  · push Not at hex
    have hsel : selU w ω s = repC w := by unfold selU; rw [if_neg (hex _)]
    rw [hsel]
    constructor
    · intro h; exact Or.inr ⟨hex, h⟩
    · rintro (⟨t, _, hb⟩ | ⟨_, h⟩)
      · exact absurd (hb ▸ hv) (hex t)
      · exact h


open Classical in
theorem selU_eq_iff' (w v : List Bool) (ω : ℕ → Bool) (s : ℕ) :
    selU w ω s = v ↔ (∃ t, (∀ t' < t, ¬ Alive 5 c₀ w (blk ω s t')) ∧
        (Alive 5 c₀ w (blk ω s t) ∧ blk ω s t = v)) ∨
      ((∀ t, ¬ Alive 5 c₀ w (blk ω s t)) ∧ repC w = v) := by
  by_cases hex : ∃ t, Alive 5 c₀ w (blk ω s t)
  · have hspec := Nat.find_spec (p := fun t => Alive 5 c₀ w (blk ω s t) ∨
        ¬ ∃ t', Alive 5 c₀ w (blk ω s t')) (firstAlive._proof_1 w ω s)
    have hT : Alive 5 c₀ w (blk ω s (firstAlive w ω s)) := hspec.resolve_right (not_not.2 hex)
    have hsel : selU w ω s = blk ω s (firstAlive w ω s) := by unfold selU; rw [if_pos hT]
    have hmin : ∀ t' < firstAlive w ω s, ¬ Alive 5 c₀ w (blk ω s t') := fun t' ht' h =>
      Nat.find_min (firstAlive._proof_1 w ω s) ht' (Or.inl h)
    rw [hsel]
    constructor
    · intro h; exact Or.inl ⟨_, hmin, hT, h⟩
    · rintro (⟨t, ht, hat, hb⟩ | ⟨hn, _⟩)
      · have : firstAlive w ω s = t := by
          rcases lt_trichotomy (firstAlive w ω s) t with h | h | h
          · exact absurd hT (ht _ h)
          · exact h
          · exact absurd hat (hmin _ h)
        rw [this, hb]
      · exact absurd hex (by push Not; exact hn)
  · push Not at hex
    have hsel : selU w ω s = repC w := by unfold selU; rw [if_neg (hex _)]
    rw [hsel]
    constructor
    · intro h; exact Or.inr ⟨hex, h⟩
    · rintro (⟨t, _, hat, _⟩ | ⟨_, h⟩)
      · exact absurd hat (hex t)
      · exact h

/-- Dead blocks after prefix `w`. -/
def deadL (w : List Bool) : Set (List Bool) := {x | ¬ Alive 5 c₀ w x}

/-- Alive blocks equal to `v`. -/
def hitL (w v : List Bool) : Set (List Bool) := {x | Alive 5 c₀ w x ∧ x = v}

theorem mset_selU (w v : List Bool) (s : ℕ) :
    MeasurableSet[MS fun x => x.1 = s] {ω | selU w ω s = v} := by
  have : {ω | selU w ω s = v} =
      (⋃ t, (⋂ t' ∈ {t' | t' < t}, {ω | blk ω s t' ∈ deadL w}) ∩ {ω | blk ω s t ∈ hitL w v}) ∪
        ((⋂ t, {ω | blk ω s t ∈ deadL w}) ∩ {_ω | repC w = v}) := by
    ext ω
    refine (selU_eq_iff' w v ω s).trans ?_
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [this]
  refine MeasurableSet.union (MeasurableSet.iUnion fun t => ?_) ?_
  · exact (MeasurableSet.biInter (Set.to_countable _) fun t' _ =>
      mset_blk (P := fun x => x.1 = s) (s := s) (t := t') rfl (deadL w)).inter
      (mset_blk (P := fun x => x.1 = s) (s := s) (t := t) rfl (hitL w v))
  · refine (MeasurableSet.iInter fun t =>
      mset_blk (P := fun x => x.1 = s) (s := s) (t := t) rfl (deadL w)).inter ?_
    by_cases h : repC w = v
    · simp only [h, Set.setOf_true]; exact @MeasurableSet.univ _ (MS _)
    · simp only [h, Set.setOf_false]; exact @MeasurableSet.empty _ (MS _)

theorem mset_buildU (s : ℕ) (w : List Bool) :
    MeasurableSet[MS fun x => x.1 < s] {ω | buildU s ω = w} := by
  induction s generalizing w with
  | zero =>
    show MeasurableSet[MS _] {_ω : ℕ → Bool | ([] : List Bool) = w}
    by_cases h : ([] : List Bool) = w
    · simp only [h, Set.setOf_true]; exact @MeasurableSet.univ _ (MS _)
    · simp only [h, Set.setOf_false]; exact @MeasurableSet.empty _ (MS _)
  | succ s ih =>
    by_cases hw : w.length = 10 * (s + 1)
    · have : {ω | buildU (s + 1) ω = w} =
          {ω | buildU s ω = w.take (10 * s)} ∩ {ω | selU (w.take (10 * s)) ω s = w.drop (10 * s)} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, buildU]
        constructor
        · intro h
          have hl := length_buildU ω s
          rw [← h, List.take_left' hl, List.drop_left' hl]; exact ⟨rfl, rfl⟩
        · rintro ⟨h1, h2⟩; rw [h1, h2, List.take_append_drop]
      rw [this]
      exact (MS_mono (fun x (hx : x.1 < s) => by omega) _ (ih _)).inter
        (MS_mono (fun x (hx : x.1 = s) => by omega) _ (mset_selU _ _ s))
    · have : {ω | buildU (s + 1) ω = w} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h; apply hw; rw [← h, length_buildU]
      rw [this]; exact @MeasurableSet.empty _ (MS _)

/-- The run of dead attempts before attempt `t`. -/
def deadRun (w : List Bool) (s t : ℕ) : Set (ℕ → Bool) :=
  ⋂ t' ∈ {t' | t' < t}, {ω | blk ω s t' ∈ deadL w}

theorem mset_deadRun (w : List Bool) (s t : ℕ) :
    MeasurableSet[MS fun x => x.1 = s ∧ x.2 < t] (deadRun w s t) :=
  MeasurableSet.biInter (Set.to_countable _) fun t' (ht' : t' < t) => mset_blk ⟨rfl, ht'⟩ _

theorem coin_deadRun (w : List Bool) (s t : ℕ) :
    coinMeasure (deadRun w s t) = (((1024 - (aliveSet w).card : ℕ) : ENNReal) / 1024) ^ t := by
  induction t with
  | zero => simp [deadRun]
  | succ t ih =>
    have : deadRun w s (t + 1) = deadRun w s t ∩ {ω | blk ω s t ∈ deadL w} := by
      ext ω; simp only [deadRun, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h; exact ⟨fun t' ht' => h t' (by omega), h t (by omega)⟩
      · rintro ⟨h1, h2⟩ t' ht'
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h | rfl
        · exact h1 t' h
        · exact h2
    rw [this, indep_MS (P := fun x => x.1 = s ∧ x.2 < t) (Q := fun x => x.1 = s ∧ x.2 = t)
      (fun x hP hQ => by omega) (mset_deadRun w s t) (mset_blk ⟨rfl, rfl⟩ _), ih, pow_succ]
    congr 1
    exact coin_dead w s t


/-- **The resampled block is uniform on the alive set**: `P(selU = v) · |A(w)| = 1`. -/
theorem coin_selU (s : ℕ) (w v : List Bool) (hv : v.length = 10 ∧ Alive 5 c₀ w v) :
    coinMeasure {ω | selU w ω s = v} * (aliveSet w).card = 1 := by
  set c := (aliveSet w).card with hc
  set r : ENNReal := ((1024 - c : ℕ) : ENNReal) / 1024 with hr
  have hc0 := card_aliveSet_pos w
  have hc1 := card_aliveSet_le w
  set f : Fin 10 → Bool := fun i => v[i]'(by omega) with hf
  have hvf : v = List.ofFn f := by
    apply List.ext_getElem (by simp [hv.1]); intro i h1 h2; rw [List.getElem_ofFn]; rfl
  set G : ℕ → Set (ℕ → Bool) := fun t => deadRun w s t ∩ {ω | blk ω s t ∈ ({v} : Set (List Bool))}
  have hGm : ∀ t, MeasurableSet (G t) := fun t =>
    MS_le _ _ ((MS_mono (fun x (hx : x.1 = s ∧ x.2 < t) => hx.1) _ (mset_deadRun w s t)).inter
      (mset_blk (P := fun x => x.1 = s) (s := s) (t := t) rfl _))
  have hGμ : ∀ t, coinMeasure (G t) = r ^ t * (1 / 1024) := by
    intro t
    rw [indep_MS (P := fun x => x.1 = s ∧ x.2 < t) (Q := fun x => x.1 = s ∧ x.2 = t)
      (fun x hP hQ => by omega) (mset_deadRun w s t) (mset_blk ⟨rfl, rfl⟩ _), coin_deadRun]
    congr 1
    rw [← coin_blk_eq s t f, hvf]; rfl
  have hdisj : Pairwise (Function.onFun Disjoint G) := by
    intro t1 t2 hne
    refine Set.disjoint_left.2 fun ω h1 h2 => ?_
    have hb1 : blk ω s t1 = v := h1.2
    have hb2 : blk ω s t2 = v := h2.2
    rcases lt_or_gt_of_ne hne with h | h
    · have := Set.mem_iInter₂.1 h2.1 t1 h
      exact this (hb1 ▸ hv.2)
    · have := Set.mem_iInter₂.1 h1.1 t2 h
      exact this (hb2 ▸ hv.2)
  set N : Set (ℕ → Bool) := ⋂ t, {ω | blk ω s t ∈ deadL w}
  have hN : coinMeasure N = 0 := by
    have hle : ∀ t, coinMeasure N ≤ r ^ t := fun t => by
      rw [← coin_deadRun]
      exact measure_mono fun ω hω => Set.mem_iInter₂.2 fun t' _ => Set.mem_iInter.1 hω t'
    have hr1 : r < 1 := by
      rw [hr, ENNReal.div_lt_iff (by norm_num) (by norm_num), one_mul]
      exact_mod_cast (by omega : 1024 - c < 1024)
    exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1) hle)
      bot_le
  have hset : {ω | selU w ω s = v} = (⋃ t, G t) ∪ (N ∩ {_ω | repC w = v}) := by
    ext ω
    refine (selU_eq_iff hv.2 ω s).trans ?_
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, G, deadRun, N]
    rfl
  have hμ : coinMeasure {ω | selU w ω s = v} = ∑' t, r ^ t * (1 / 1024) := by
    rw [hset, show (∑' t, r ^ t * (1 / 1024)) = ∑' t, coinMeasure (G t) from
      tsum_congr fun t => (hGμ t).symm, ← measure_iUnion hdisj hGm]
    refine le_antisymm ((measure_union_le _ _).trans ?_) (measure_mono Set.subset_union_left)
    rw [measure_mono_null Set.inter_subset_left hN, add_zero]
  rw [hμ, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have h1r : 1 - r = (c : ENNReal) / 1024 := by
    refine ENNReal.sub_eq_of_eq_add (by rw [hr]; exact ENNReal.div_ne_top (by simp) (by norm_num)) ?_
    rw [hr, ENNReal.div_add_div_same, ← Nat.cast_add, show c + (1024 - c) = 1024 by omega,
      Nat.cast_ofNat, ENNReal.div_self (by norm_num) (by norm_num)]
  rw [h1r, mul_assoc, one_div, mul_comm ((1024 : ENNReal)⁻¹), ← div_eq_mul_inv]
  exact ENNReal.inv_mul_cancel (by simp; omega) (ENNReal.div_ne_top (by simp) (by norm_num))

/-- **Conditional uniformity of the resampled block** (open leaf, believed 97%; standard
rejection sampling).  Given the prefix `w` after `s` stages, each alive child `v` is the next
block with probability `1/|A(w)|`.  English proof: the stage-`s` coin blocks `blk ω s t` are
i.i.d. uniform and independent of `buildU s` (which reads only blocks `pair(s', t)`, `s' < s`);
the first alive one among i.i.d. uniform draws is uniform on `A(w)`, and `|A(w)| ≥ 536 > 0`
(`card_dead_le`) so one exists a.s. -/
theorem buildU_succ_uniform (s : ℕ) (w v : List Bool) (hv : v.length = 10 ∧ Alive 5 c₀ w v) :
    coinMeasure {ω | buildU (s + 1) ω = w ++ v} * (aliveSet w).card =
      coinMeasure {ω | buildU s ω = w} := by
  by_cases hw : w.length = 10 * s
  · have hset : {ω | buildU (s + 1) ω = w ++ v} =
        {ω | buildU s ω = w} ∩ {ω | selU w ω s = v} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, buildU]
      constructor
      · intro h
        have h1 := (List.append_inj h (by rw [length_buildU, hw])).1
        rw [h1] at h
        exact ⟨h1, List.append_cancel_left h⟩
      · rintro ⟨h1, h2⟩; rw [h1, h2]
    rw [hset, indep_MS (P := fun x => x.1 < s) (Q := fun x => x.1 = s) (fun x hP hQ => by omega)
      (mset_buildU s w) (mset_selU w v s), mul_assoc, coin_selU s w v hv, mul_one]
  · have h1 : {ω | buildU s ω = w} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hw (h ▸ length_buildU ω s)
    have h2 : {ω | buildU (s + 1) ω = w ++ v} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have := congrArg List.length h
      rw [length_buildU, List.length_append, hv.1] at this
      exact hw (by omega)
    rw [h1, h2]; simp

/-! ### Decomposition of the crux: Cantor part plus dead-children characters

Let `ν_S` follow `resLaw` for stages `< S` and the Cantor coin measure after.  Then `ν_0 = μ_K`,
`ν_S → ν`, and by uniformity on `A(w)` the stage-`S` conditional character of `ν` minus that of
`μ_K` is `−|A(w)|⁻¹ Σ_{f dead} (e(ξ J f 3^{−L−10}) − ρ_S(ξ))`: only the dead children appear, not
the replacement (`deadErr`).  Under an arbitrary rule the replacement's own character would
appear here, which is how `AdversarialReplacement` steers. -/

/-- `μ̂_K(ξ)`: the Fourier coefficient of the Cantor measure. -/
noncomputable def muK (ξ : ℝ) : ℂ := ∫ ω, ee (ξ * cpt ω) ∂coinMeasure

/-- The stage character `ρ(ξ) = 2⁻¹⁰ Σ_f e(ξ J f / 3^{L+10})` of a uniform ten-digit block. -/
noncomputable def rhoS (ξ : ℝ) (L : ℕ) : ℂ :=
  (1 / 1024 : ℂ) * ∑ f : Fin 10 → Bool, ee (ξ * J f / 3 ^ (L + 10))

/-- The dead-children error of the stage after prefix `w`. -/
noncomputable def deadErr (ξ : ℝ) (w : List Bool) : ℂ :=
  (1 / ((aliveSet w).card : ℂ)) *
    ∑ f ∈ Finset.univ \ aliveSet w, (ee (ξ * J f / 3 ^ (w.length + 10)) - rhoS ξ w.length)

/-- The stage-`S` dead-children character of `resLaw`. -/
noncomputable def deadChar (ξ : ℝ) (S : ℕ) : ℂ :=
  ∫ ω, ee (ξ * cylLeft (buildU S ω)) * deadErr ξ (buildU S ω) ∂coinMeasure

open CantorLiouvilleAll CantorLiouville in
/-- The pair sum of the Riesz majorants `Bf` behind `CantorLiouvilleAll.secondMoment_le_explicit_b`
(its proof, without the second-moment expansion).  Proved. -/
theorem pairSum_Bf_le_explicit_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        Bf free (Nat.log 3 N / 2) (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) ≤
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
        3 * (3 ^ (padicValNat 3 h.natAbs + tb b) + 2 * (3 / 2 : ℝ) ^ tb b) * (N : ℝ) ^ 2 *
          Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2)) := by
  set e := padicValNat 3 h.natAbs
  set t := tb b
  set M := Nat.log 3 N / 2
  set F := freeCount free M
  set W := F / 2
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hMN : 3 ^ M ≤ N :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
      (Nat.pow_log_le_self 3 (by omega))
  set G : ℕ → ℕ → ℝ := fun d m => Bf free M (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m)
  have hpair := pair_sum_le (fun n m => Bf free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))) G
    (fun d m => Bf_nonneg _ _ _) (fun n => Bf_le_one _ _ _)
    (fun n m hmn => le_of_eq (by
      simp only [G]; congr 1
      rw [show (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m by rw [← pow_add]; congr 1; omega]; ring))
    (fun n m hmn => le_of_eq (by
      simp only [G]; rw [← Bf_neg]; congr 1
      rw [show (b : ℝ) ^ m = (b : ℝ) ^ (m - n) * (b : ℝ) ^ n by rw [← pow_add]; congr 1; omega]; ring)) N
  set P := (2 / 3 : ℝ) ^ W
  set T := (3 / 2 : ℝ) ^ t
  have hT : 0 ≤ T := by positivity
  have hshift : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      (if W ≤ e + padicValNat 3 (b ^ d - 1) then (N : ℝ) else 0) + 2 * N * T * P := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hd1 : 1 ≤ b ^ d - 1 := by
      have : 2 ≤ b ^ d := le_trans hb (Nat.le_self_pow (by omega) b)
      omega
    split_ifs with hbad
    · refine (Finset.sum_le_sum fun m _ => Bf_le_one free M _).trans ?_
      have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
      simp; linarith
    · rw [zero_add]
      set c := h.natAbs * (b ^ d - 1)
      have hc : c ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.2 hh) (by omega)
      have hv : padicValNat 3 c = e + padicValNat 3 (b ^ d - 1) :=
        padicValNat.mul (Int.natAbs_ne_zero.2 hh) (by omega)
      refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_)
        (good_shift_b free hb h3 M N hMN c hc (by omega))
      simp only [G]
      rw [← Bf_abs]
      congr 1
      have hd2 : (0 : ℝ) ≤ (b : ℝ) ^ d - 1 := by
        have : (1:ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ hb1; linarith
      simp only [c]
      push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 0 < b))]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (b : ℝ) ^ m),
        abs_of_nonneg hd2, Nat.cast_natAbs, Int.cast_abs]
  have hsumd : ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      N * ((N / 3 ^ (W - e - t) : ℕ) : ℝ) + N * (2 * N * T * P) := by
    refine (Finset.sum_le_sum hshift).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico]
    have hbc := bad_count_b hb h3 e W N
    have : (((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 3 (b ^ m - 1))).card : ℝ) ≤
        ((N / 3 ^ (W - e - t) : ℕ) : ℝ) := by exact_mod_cast hbc
    have hN1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
    nlinarith
  have hdiv : ((N / 3 ^ (W - e - t) : ℕ) : ℝ) ≤ N * 3 ^ (e + t) * P := by
    have h1 : (N / 3 ^ (W - e - t)) * 3 ^ W ≤ N * 3 ^ (e + t) := by
      calc (N / 3 ^ (W - e - t)) * 3 ^ W ≤ (N / 3 ^ (W - e - t)) * (3 ^ (W - e - t) * 3 ^ (e + t)) := by
            gcongr; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (N / 3 ^ (W - e - t)) * 3 ^ (W - e - t) * 3 ^ (e + t) := by ring
        _ ≤ N * 3 ^ (e + t) := by gcongr; exact Nat.div_mul_le_self _ _
    have h2 : ((N / 3 ^ (W - e - t) : ℕ) : ℝ) * 3 ^ W ≤ N * 3 ^ (e + t) := by exact_mod_cast h1
    have h3' : (2 / 3 : ℝ) ^ W * 3 ^ W = 2 ^ W := by rw [← mul_pow]; norm_num
    have h4 : (1 : ℝ) ≤ 2 ^ W := one_le_pow₀ (by norm_num)
    have h5 : (0 : ℝ) < 3 ^ W := by positivity
    rw [← mul_le_mul_iff_of_pos_right h5]
    calc _ ≤ (N : ℝ) * 3 ^ (e + t) := h2
      _ ≤ (N : ℝ) * 3 ^ (e + t) * 2 ^ W := le_mul_of_one_le_right (by positivity) h4
      _ = _ := by rw [mul_assoc _ ((2 / 3 : ℝ) ^ W), h3']
  have hexp := pow_two_sub_le W F rfl
  have hNr : (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = N * N ^ (1 : ℝ) by rw [Real.rpow_one]; ring, mul_assoc,
        ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]
    have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN0 (by norm_num)
    nlinarith
  have hI := hpair
  set E := Real.exp (-(Real.log (3 / 2) / 2) * F)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hP : 0 ≤ P := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hfin : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        Bf free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) ≤
      N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * P) := by
    have := mul_le_mul_of_nonneg_left hdiv hN0
    nlinarith
  have hK : (0 : ℝ) ≤ 3 ^ (e + t) + 2 * T := by positivity
  calc _ ≤ N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * P) := hfin
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * (3 / 2 * E)) := by
        gcongr
    _ = _ := by simp only [T, E, F, M]; ring

/-- **Cassels for the Cantor digit products** (proved): the pair sum of `|μ̂_K|` over the
frequencies `h(bⁿ − bᵐ)` has a power saving.  This is the bound inside
`CantorLiouvilleAll.secondMoment_le_explicit_b` with `free = fun _ => true` (there it is applied
to the second moment; `charFun_real` bounds `|μ̂|` by the truncated product `Bf`). -/
theorem cassels_Bf {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, CantorLiouville.Bf (fun _ => true) (Nat.log 3 N / 2) (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) ≤
        C * (N : ℝ) ^ 2 * W N := by
  set e := padicValNat 3 h.natAbs
  set t := CantorLiouvilleAll.tb b
  set c : ℝ := Real.log (3 / 2) / 2
  have hc : 0 ≤ c := by unfold c; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3 / 2); positivity
  set δ : ℝ := c / (2 * Real.log 3)
  set K : ℝ := 3 * (3 ^ (e + t) + 2 * (3 / 2 : ℝ) ^ t)
  have hK : 0 ≤ K := by positivity
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hE : ∀ N : ℕ, 1 ≤ N → Real.exp (-c * ((Nat.log 3 N / 2 : ℕ) : ℝ)) ≤
      Real.exp c * (N : ℝ) ^ (-δ) := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    set k := Nat.log 3 N
    have hlt : N < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hlog : Real.log N < (k + 1) * Real.log 3 := by
      have : (N : ℝ) < (3 : ℝ) ^ (k + 1) := by exact_mod_cast hlt
      have := Real.log_lt_log hN0 this
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
    have hk2 : (k : ℝ) - 1 ≤ 2 * ((k / 2 : ℕ) : ℝ) := by
      have : k ≤ 2 * (k / 2) + 1 := by omega
      have : (k : ℝ) ≤ 2 * ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
      linarith
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : Real.log N * (1 / Real.log 3) < k + 1 := by
      rw [← div_eq_mul_one_div, div_lt_iff₀ hl3]; linarith
    have hδ : Real.log N * -δ = -(c / 2) * (Real.log N * (1 / Real.log 3)) := by
      unfold δ; field_simp
    rw [hδ]
    nlinarith
  refine ⟨K + 1, fun N => (N : ℝ) ^ (-(1 / 2 : ℝ)) + Real.exp c * (N : ℝ) ^ (-δ),
    (summable_sched_rpow (by norm_num)).add ((summable_sched_rpow (by
      unfold δ; have : 0 < c := by unfold c; have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); positivity
      positivity)).mul_left _), fun N hN => ?_⟩
  have hB := pairSum_Bf_le_explicit_b (fun _ => true) hb h3 h hh N hN
  have hfc : ∀ M, CantorLiouville.freeCount (fun _ => true) M = M := by
    intro M; simp [CantorLiouville.freeCount]
  rw [hfc] at hB
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hr2 : (0 : ℝ) ≤ Real.exp c * (N : ℝ) ^ (-δ) := by positivity
  have hEN := hE N hN
  calc _ ≤ _ := hB
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + K * (N : ℝ) ^ 2 * (Real.exp c * (N : ℝ) ^ (-δ)) := by
        have := mul_le_mul_of_nonneg_left hEN (mul_nonneg hK hN2)
        simp only [K] at this ⊢
        linarith
    _ ≤ _ := by nlinarith [mul_nonneg hN2 hr, mul_nonneg hN2 hr2, mul_nonneg (mul_nonneg hK hN2) hr]

/-- **Cassels for `μ_K`**, proved from `cassels_Bf` and `charFun_real`. -/
theorem cassels_muK {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖muK (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))‖ ≤
        C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C, W, hW, hC⟩ := cassels_Bf hb h3 h hh
  exact ⟨C, W, hW, fun N hN => le_trans (Finset.sum_le_sum fun n _ => Finset.sum_le_sum
    fun m _ => CantorLiouville.charFun_real _ _ _) (hC N hN)⟩

/-- The prefix character `T_S(ξ) = E e(ξ · cylLeft(buildU S))` of `resLaw`. -/
noncomputable def prefChar (ξ : ℝ) (S : ℕ) : ℂ :=
  ∫ ω, ee (ξ * cylLeft (buildU S ω)) ∂coinMeasure

/-- `Π_{a ≤ p < M} |cos(2πξ/3^{p+1})|`: the Cantor digit factors from `a` to `M`. -/
noncomputable def tailProd (ξ : ℝ) (a M : ℕ) : ℝ :=
  ∏ p ∈ Finset.Ico a M, |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))|

theorem tailProd_nonneg (ξ : ℝ) (a M : ℕ) : 0 ≤ tailProd ξ a M :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem tailProd_le_one (ξ : ℝ) (a M : ℕ) : tailProd ξ a M ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _

theorem tailProd_mul (ξ : ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    tailProd ξ a b * tailProd ξ b c = tailProd ξ a c :=
  Finset.prod_Ico_consecutive _ hab hbc

theorem tailProd_self (ξ : ℝ) (a : ℕ) : tailProd ξ a a = 1 := by simp [tailProd]

theorem tailProd_zero_eq_Bf (ξ : ℝ) (M : ℕ) :
    tailProd ξ 0 M = CantorLiouville.Bf (fun _ => true) M ξ := by
  unfold tailProd CantorLiouville.Bf
  rw [Finset.filter_true_of_mem (fun _ _ => rfl), Finset.range_eq_Ico]

/-- The possible prefixes after `S` stages. -/
noncomputable def LS (S : ℕ) : Finset (List Bool) :=
  Finset.univ.image fun g : Fin (10 * S) → Bool => List.ofFn g

theorem buildU_mem_LS (ω : ℕ → Bool) (S : ℕ) : buildU S ω ∈ LS S :=
  Finset.mem_image.2 ⟨_, Finset.mem_univ _, ofFn_descentU ω S⟩

theorem length_of_mem_LS {S : ℕ} {w : List Bool} (hw : w ∈ LS S) : w.length = 10 * S := by
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.1 hw; simp

theorem mset_buildU' (S : ℕ) (w : List Bool) : MeasurableSet {ω | buildU S ω = w} :=
  MS_le _ _ (mset_buildU S w)

theorem integral_buildU (S : ℕ) (G : List Bool → ℂ) :
    ∫ ω, G (buildU S ω) ∂coinMeasure =
      ∑ w ∈ LS S, coinMeasure.real {ω | buildU S ω = w} • G w := by
  have hpt : ∀ ω, G (buildU S ω) =
      ∑ w ∈ LS S, {ω | buildU S ω = w}.indicator (fun _ => G w) ω := by
    intro ω
    rw [Finset.sum_eq_single (buildU S ω)]
    · simp [Set.indicator]
    · intro w _ hw; simp [Set.indicator, Ne.symm hw]
    · intro h; exact absurd (buildU_mem_LS ω S) h
  simp_rw [hpt]
  rw [integral_finset_sum _ fun w _ => (integrable_const _).indicator (mset_buildU' S w)]
  exact Finset.sum_congr rfl fun w _ => integral_indicator_const _ (mset_buildU' S w)

theorem integral_buildU_succ (S : ℕ) (G : List Bool → ℂ) :
    ∫ ω, G (buildU (S + 1) ω) ∂coinMeasure =
      ∑ w ∈ LS S, ∑ f : Fin 10 → Bool,
        coinMeasure.real {ω | buildU (S + 1) ω = w ++ List.ofFn f} • G (w ++ List.ofFn f) := by
  have hpt : ∀ ω, G (buildU (S + 1) ω) = ∑ w ∈ LS S, ∑ f : Fin 10 → Bool,
      {ω | buildU (S + 1) ω = w ++ List.ofFn f}.indicator (fun _ => G (w ++ List.ofFn f)) ω := by
    intro ω
    set w0 := buildU S ω
    have hlen := (selU_alive w0 ω S).1
    set f0 : Fin 10 → Bool := fun i => (selU w0 ω S)[i]'(by omega)
    have hsel : selU w0 ω S = List.ofFn f0 := by
      apply List.ext_getElem (by simp [hlen]); intro i h1 h2; rw [List.getElem_ofFn]; rfl
    have hb : buildU (S + 1) ω = w0 ++ List.ofFn f0 := by
      show buildU S ω ++ selU (buildU S ω) ω S = _; rw [hsel]
    rw [Finset.sum_eq_single w0, Finset.sum_eq_single f0]
    · simp [Set.indicator, hb]
    · intro f _ hf
      simp only [Set.indicator, Set.mem_setOf_eq, hb]
      rw [if_neg]; intro h
      exact hf (List.ofFn_injective (List.append_cancel_left h)).symm
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro w hw hne
      refine Finset.sum_eq_zero fun f _ => ?_
      simp only [Set.indicator, Set.mem_setOf_eq, hb]
      rw [if_neg]; intro h
      exact hne (List.append_inj h (by rw [length_buildU, length_of_mem_LS hw])).1.symm
    · intro h; exact absurd (buildU_mem_LS ω S) h
  simp_rw [hpt]
  have hm : ∀ (w : List Bool) (f : Fin 10 → Bool),
      MeasurableSet {ω | buildU (S + 1) ω = w ++ List.ofFn f} := fun w f =>
    mset_buildU' _ _
  rw [integral_finset_sum _ fun w _ => integrable_finset_sum _ fun f _ =>
    (integrable_const _).indicator (hm w f)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [integral_finset_sum _ fun f _ => (integrable_const _).indicator (hm w f)]
  exact Finset.sum_congr rfl fun f _ => integral_indicator_const _ (hm w f)

/-- The alive average of the child characters is `ρ − deadErr`.  Proved. -/
theorem alive_avg (ξ : ℝ) (w : List Bool) :
    (1 / ((aliveSet w).card : ℂ)) * ∑ f ∈ aliveSet w, ee (ξ * J f / 3 ^ (w.length + 10)) =
      rhoS ξ w.length - deadErr ξ w := by
  classical
  set e : (Fin 10 → Bool) → ℂ := fun f => ee (ξ * J f / 3 ^ (w.length + 10))
  have hc : ((aliveSet w).card : ℂ) ≠ 0 := by exact_mod_cast (card_aliveSet_pos w).ne'
  have hsplit := Finset.sum_sdiff (f := e) (Finset.subset_univ (aliveSet w))
  have hD : ((Finset.univ \ aliveSet w).card : ℂ) = 1024 - (aliveSet w).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      show Fintype.card (Fin 10 → Bool) = 1024 by simp,
      Nat.cast_sub (card_aliveSet_le w)]; norm_num
  unfold deadErr rhoS
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hD]
  change (1 / ((aliveSet w).card : ℂ)) * ∑ f ∈ aliveSet w, e f =
    1 / 1024 * ∑ f, e f - 1 / ((aliveSet w).card : ℂ) *
      (∑ f ∈ Finset.univ \ aliveSet w, e f - (1024 - ((aliveSet w).card : ℂ)) *
        (1 / 1024 * ∑ f, e f))
  rw [← hsplit]
  field_simp
  ring

/-- **Stage recursion** (open leaf, believed 97%):
`T_{S+1} = ρ_S T_S − deadChar(ξ, S)`.  English proof: condition on `buildU S = w`; by
`buildU_succ_uniform` the next block is uniform on `A(w)`, so the conditional character is
`e(ξ cylLeft w) · |A|⁻¹ Σ_{f∈A} e(ξ J f/3^{|w|+10})` (`cylLeft_child`), and
`|A|⁻¹ Σ_{f∈A} e_f = ρ − deadErr` since `Σ_f e_f = 1024 ρ`. -/
theorem prefChar_succ (ξ : ℝ) (S : ℕ) :
    prefChar ξ (S + 1) = rhoS ξ (10 * S) * prefChar ξ S - deadChar ξ S := by
  classical
  unfold prefChar deadChar
  rw [integral_buildU_succ S (fun w' => ee (ξ * cylLeft w')),
    integral_buildU S (fun w => ee (ξ * cylLeft w)),
    integral_buildU S (fun w => ee (ξ * cylLeft w) * deadErr ξ w),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hl := length_of_mem_LS hw
  set m := coinMeasure.real {ω | buildU S ω = w}
  set c := (aliveSet w).card
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast (card_aliveSet_pos w).ne'
  have hE : ∀ f : Fin 10 → Bool, coinMeasure.real {ω | buildU (S + 1) ω = w ++ List.ofFn f} =
      if f ∈ aliveSet w then m / c else 0 := by
    intro f
    split_ifs with hf
    · have h1 := buildU_succ_uniform S w (List.ofFn f) ⟨by simp, (Finset.mem_filter.1 hf).2⟩
      have h2 := congrArg ENNReal.toReal h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2
      rw [eq_div_iff hc]; exact h2
    · have : {ω | buildU (S + 1) ω = w ++ List.ofFn f} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        change buildU S ω ++ selU (buildU S ω) ω S = w ++ List.ofFn f at h
        have h1 := (List.append_inj h (by rw [length_buildU, hl])).1
        rw [h1] at h
        have h2 := List.append_cancel_left h
        apply hf
        simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← h2, ← h1]; exact (selU_alive _ ω S).2
      rw [this]; simp
  have hch : ∀ f : Fin 10 → Bool, ee (ξ * cylLeft (w ++ List.ofFn f)) =
      ee (ξ * cylLeft w) * ee (ξ * J f / 3 ^ (w.length + 10)) := by
    intro f; rw [cylLeft_child, ← ee_add]; congr 1; ring
  simp only [hE, hch, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, show 10 * S = w.length from hl.symm]
  have avg := alive_avg ξ w
  have hsum : ∑ f ∈ aliveSet w, (m / c) • (ee (ξ * cylLeft w) * ee (ξ * J f / 3 ^ (w.length + 10))) =
      (m : ℂ) * ee (ξ * cylLeft w) *
        ((1 / (c : ℂ)) * ∑ f ∈ aliveSet w, ee (ξ * J f / 3 ^ (w.length + 10))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Complex.real_smul]; push_cast
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    field_simp
  rw [hsum, avg, Complex.real_smul, Complex.real_smul]
  ring

/-- The block character as a product of digit factors. -/
theorem rhoS_eq_prod (ξ : ℝ) (L : ℕ) :
    rhoS ξ L = ∏ i : Fin 10, (1 + ee (2 * ξ / 3 ^ (L + (i : ℕ) + 1))) / 2 := by
  have hterm : ∀ (f : Fin 10 → Bool) (i : Fin 10),
      ξ * (((if f i then 2 else 0 : ℕ) : ℝ) * (3 : ℝ) ^ (9 - (i : ℕ))) / 3 ^ (L + 10) =
        if f i then 2 * ξ / 3 ^ (L + (i : ℕ) + 1) else 0 := by
    intro f i
    have hp : (3 : ℝ) ^ (L + 10) = 3 ^ (9 - (i : ℕ)) * 3 ^ (L + (i : ℕ) + 1) := by
      rw [← pow_add]; congr 1; omega
    cases f i
    · simp
    · simp only [if_true, Nat.cast_ofNat]
      rw [hp]; field_simp
  have hee_sum : ∀ a : Fin 10 → ℝ, ee (∑ i, a i) = ∏ i, ee (a i) := by
    intro a; unfold ee
    rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum]
  have key : ∀ f : Fin 10 → Bool, ee (ξ * J f / 3 ^ (L + 10)) =
      ∏ i, (if f i then ee (2 * ξ / 3 ^ (L + (i : ℕ) + 1)) else 1) := by
    intro f
    have : ξ * (J f : ℝ) / 3 ^ (L + 10) = ∑ i, (if f i then 2 * ξ / 3 ^ (L + (i : ℕ) + 1) else 0) := by
      unfold J; push_cast
      rw [Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [← hterm f i]; push_cast; ring
    rw [this, hee_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs <;> simp [ee]
  unfold rhoS
  simp only [key]
  rw [← Fintype.prod_sum (fun (i : Fin 10) (b : Bool) =>
    if b then ee (2 * ξ / 3 ^ (L + (i : ℕ) + 1)) else 1)]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [add_comm (1 : ℂ)]
  norm_num [div_eq_inv_mul]

/-- **The block character is a cosine product** (proved):
`|ρ_L(ξ)| = Π_{L ≤ p < L+10} |cos(2πξ/3^{p+1})|`, since
`ρ_L = Π_{i<10} (1 + e(2ξ/3^{L+i+1}))/2`. -/
theorem norm_rhoS (ξ : ℝ) (L : ℕ) : ‖rhoS ξ L‖ = tailProd ξ L (L + 10) := by
  have hρ := rhoS_eq_prod ξ L
  rw [hρ, norm_prod]
  simp only [CantorLiouville.norm_one_add_ee_div_two]
  unfold tailProd
  rw [Finset.prod_Ico_eq_prod_range, show L + 10 - L = 10 by omega, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2; field_simp

theorem norm_ee_sub_ee (a b : ℝ) : ‖ee a - ee b‖ ≤ 2 * Real.pi * |a - b| := by
  have h : ee a = ee b * ee (a - b) := by rw [← ee_add]; congr 1; ring
  rw [h, ← mul_sub_one, norm_mul, norm_ee, one_mul]
  have : ee (a - b) = Complex.exp (Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ)) := by
    unfold ee; congr 1; push_cast; ring
  rw [this]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

section MeasP
local instance : MeasurableSpace (List Bool) := ⊤

theorem integrable_ee_prefix (ξ : ℝ) (S : ℕ) :
    Integrable (fun ω => ee (ξ * cylLeft (buildU S ω))) coinMeasure :=
  Integrable.of_bound ((measurable_ee.comp ((measurable_from_top (f := cylLeft)).comp
    (measurable_buildU S) |>.const_mul ξ)).aestronglyMeasurable) 1
    (Eventually.of_forall fun ω => (norm_ee _).le)
end MeasP

theorem integrable_ee_cpt (ξ : ℝ) :
    Integrable (fun ω => ee (ξ * cpt (resLaw.φ ω))) coinMeasure :=
  Integrable.of_bound ((measurable_ee.comp ((measurable_cpt.comp resLaw.meas).const_mul ξ)).aestronglyMeasurable) 1
    (Eventually.of_forall fun ω => (norm_ee _).le)

/-- **The prefix determines the point to `3^{−10S}`** (open leaf, believed 99%):
`cpt (descentU ω) ∈ cyl (buildU S ω)` (`cpt_mem_cyl`, `ofFn_descentU`), and `e` is
`2π`-Lipschitz. -/
theorem norm_fourier_sub_prefChar (ξ : ℝ) (S : ℕ) :
    ‖(∫ ω, ee (ξ * cpt (resLaw.φ ω)) ∂coinMeasure) - prefChar ξ S‖ ≤ 16 * |ξ| / 3 ^ (10 * S) := by
  have hS : ∀ ω, ‖ee (ξ * cpt (resLaw.φ ω)) - ee (ξ * cylLeft (buildU S ω))‖ ≤
      16 * |ξ| / 3 ^ (10 * S) := by
    intro ω
    have hmem := cpt_mem_cyl (descentU ω) (10 * S)
    rw [ofFn_descentU] at hmem
    unfold cyl at hmem
    rw [length_buildU] at hmem
    have h0 : (0 : ℝ) < 3 ^ (10 * S) := by positivity
    have e : resLaw.φ ω = descentU ω := rfl
    have hd : |cpt (resLaw.φ ω) - cylLeft (buildU S ω)| ≤ 1 / 3 ^ (10 * S) := by
      rw [e, abs_le]
      have h1 := hmem.1; have h2 := hmem.2
      constructor <;> linarith
    refine (norm_ee_sub_ee _ _).trans ?_
    rw [← mul_sub, abs_mul]
    calc 2 * Real.pi * (|ξ| * |cpt (resLaw.φ ω) - cylLeft (buildU S ω)|)
        ≤ 2 * Real.pi * (|ξ| * (1 / 3 ^ (10 * S))) := by gcongr
      _ ≤ 8 * (|ξ| * (1 / 3 ^ (10 * S))) := by gcongr; linarith [Real.pi_lt_four]
      _ ≤ 16 * |ξ| / 3 ^ (10 * S) := by
          rw [mul_one_div, mul_div_assoc']; gcongr; norm_num
  unfold prefChar
  rw [← integral_sub (integrable_ee_cpt ξ) (integrable_ee_prefix ξ S)]
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hS)).trans ?_
  simp

theorem prefChar_zero (ξ : ℝ) : prefChar ξ 0 = 1 := by
  simp [prefChar, buildU, cylLeft, ee]

/-- **Unrolled recursion.**  Proved from `prefChar_succ` and `norm_rhoS`:
`|T_S| ≤ Π_{p<10S}|cos| + Σ_{S'<S} |deadChar(ξ,S')| · Π_{10S'+10 ≤ p < 10S}|cos|`. -/
theorem norm_prefChar_le (ξ : ℝ) (S : ℕ) :
    ‖prefChar ξ S‖ ≤ tailProd ξ 0 (10 * S) +
      ∑ S' ∈ Finset.range S, ‖deadChar ξ S'‖ * tailProd ξ (10 * S' + 10) (10 * S) := by
  induction S with
  | zero => simp [prefChar_zero, tailProd_self]
  | succ S ih =>
    rw [prefChar_succ, show 10 * (S + 1) = 10 * S + 10 by ring]
    set R := tailProd ξ (10 * S) (10 * S + 10)
    have hR0 : 0 ≤ R := tailProd_nonneg _ _ _
    calc ‖rhoS ξ (10 * S) * prefChar ξ S - deadChar ξ S‖
        ≤ ‖rhoS ξ (10 * S)‖ * ‖prefChar ξ S‖ + ‖deadChar ξ S‖ :=
          (norm_sub_le _ _).trans (by rw [norm_mul])
      _ ≤ R * (tailProd ξ 0 (10 * S) +
            ∑ S' ∈ Finset.range S, ‖deadChar ξ S'‖ * tailProd ξ (10 * S' + 10) (10 * S)) +
          ‖deadChar ξ S‖ := by rw [norm_rhoS]; gcongr
      _ = _ := by
          rw [Finset.sum_range_succ, mul_add, Finset.mul_sum, tailProd_self, mul_one,
            show R * tailProd ξ 0 (10 * S) = tailProd ξ 0 (10 * S + 10) by
              rw [mul_comm]; exact tailProd_mul ξ (by omega) (by omega)]
          have hs : ∑ S' ∈ Finset.range S, R * (‖deadChar ξ S'‖ * tailProd ξ (10 * S' + 10) (10 * S)) =
              ∑ S' ∈ Finset.range S, ‖deadChar ξ S'‖ * tailProd ξ (10 * S' + 10) (10 * S + 10) := by
            refine Finset.sum_congr rfl fun S' hS' => ?_
            rw [Finset.mem_range] at hS'
            rw [mul_left_comm, mul_comm R, tailProd_mul ξ (by omega) (by omega)]
          rw [hs, add_assoc]

/-- Pointwise bound for `resLaw`, at any depth `S`.  Proved. -/
theorem fourierAbs_resLaw_le (ξ : ℝ) (S : ℕ) :
    fourierAbs resLaw ξ ≤ tailProd ξ 0 (10 * S) +
      ∑ S' ∈ Finset.range S, ‖deadChar ξ S'‖ * tailProd ξ (10 * S' + 10) (10 * S) +
        16 * |ξ| / 3 ^ (10 * S) := by
  unfold fourierAbs
  have h1 := norm_fourier_sub_prefChar ξ S
  have h2 := norm_prefChar_le ξ S
  have h3 := norm_add_le ((∫ ω, ee (ξ * cpt (resLaw.φ ω)) ∂coinMeasure) - prefChar ξ S) (prefChar ξ S)
  rw [sub_add_cancel] at h3
  linarith

/-- **Conjecture node (formerly the crux; absolute form).**  Believed, confidence 40%.
Superseded by the weaker signed crux `deadCharSigned` (`deadCharSigned_of_abs`).  The step most
in doubt: for stages `S'` with `log₃ N < 10S' < log₃|ξ|` the Cassels averaging over `(n, m)`
(which reaches only ternary positions `< log₃ N`) does not apply, so this form needs Fourier
decay at the middle ternary digits of `bⁿ`, an open-problem-strength input.

Uniformly in the depth `S`,
`Σ_{n,m<N} Σ_{S'<S} |deadChar(ξ, S')|·Π_{10S'+10 ≤ p < 10S}|cos(2πξ/3^{p+1})| = O(N² W(N))`,
`ξ = h(bⁿ − bᵐ)`.  The Cantor digit factors localize `S'` to `O(1)` stages near `log₃|ξ|/10`
on average over `(n, m)` (as in `cassels_Bf`); below that scale `|deadErr| ≤ 4π|ξ|3^{−10S'}`
is tiny.  At the surviving stages a dead child sits within `c₀/q²` of an obstacle `p/q`,
`q² ≍ 3^{10S'}`, so `deadChar ≈ E_ν Σ_{p/q near w} e(ξ p/q)·(…)`: an exponential sum of
`h bⁿ p/q` over rationals near `K`, weighted by `ν`.  The bound needs cancellation in `n` of
`e(h bⁿ p / q)`.  The trivial bound `|deadChar| ≤ 2·P(dead at S')` is the `DeadRateDecay` route
(believed false).

Guards: `b = 3` is false (`cantor_not_normal_three_pow`; `3ⁿ p/q` with `q | 3^k` does not
cancel), and the base-2 dyadic sibling (`perStage_deadCount_not_enough`) has centres `p/2ᵏ`,
for which `e(2ⁿ p/2ᵏ) = 1` once `n ≥ k`: no cancellation, as required. -/
def DeadCharCancelAbs (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ,
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range S, ‖deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S'‖ *
          tailProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (10 * S' + 10) (10 * S) ≤
        C * (N : ℝ) ^ 2 * W N

/-- **The crux for the resampling law**, from the decomposition.  Proved modulo the leaves
`prefChar_succ`, `norm_rhoS`, `norm_fourier_sub_prefChar` and the crux `deadCharCancel`.

The mechanism uses uniformity through `prefChar_succ`: a proof that uses only that the stage
block is alive (any admissible rule) reduces to `DeadRateDecay` (believed false), and per-stage
dead counts alone are refuted by `perStage_deadCount_not_enough` (whose sibling with uniform
resampling is still never 2-normal).  So `deadCharCancel` must use the arithmetic of the
centres `p/q`.  Known-false sibling: `b = 3` (`cantor_not_normal_three_pow`). -/
theorem fourierPairRate_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (hD : DeadCharCancelAbs b) :
    FourierPairRate resLaw b := by
  intro h hh
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := cassels_Bf hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := hD h hh
  refine ⟨|C₁| + |C₂| + 1, fun N => |W₁ N| + |W₂ N| + (N : ℝ) ^ (-(1 / 2 : ℝ)),
    (hW₁.abs.add hW₂.abs).add (summable_sched_rpow (by norm_num)), fun N hN => ?_⟩
  set ξ : ℕ → ℕ → ℝ := fun n m => h * ((b : ℝ) ^ n - (b : ℝ) ^ m) with hξ
  have h₂' : ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ∑ S' ∈ Finset.range S, ‖deadChar (ξ n m) S'‖ * tailProd (ξ n m) (10 * S' + 10) (10 * S) ≤
        C₂ * (N : ℝ) ^ 2 * W₂ N := h₂
  set K : ℝ := ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m|
  set S : ℕ := ⌈K⌉₊ + Nat.log 3 N
  have hK : K ≤ 3 ^ (10 * S) := by
    have h1 : K ≤ (S : ℝ) := (Nat.le_ceil K).trans (by exact_mod_cast Nat.le_add_right _ _)
    have h2 : S < 3 ^ (10 * S) := (Nat.lt_pow_self (by norm_num)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact h1.trans (by exact_mod_cast h2.le)
  have hM : Nat.log 3 N / 2 ≤ 10 * S := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hrN : (1 : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (N : ℝ) ^ (3 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]; exact Real.one_le_rpow hN1 (by norm_num)
  have h3S : (0 : ℝ) < 3 ^ (10 * S) := by positivity
  have hA : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, tailProd (ξ n m) 0 (10 * S) ≤
      C₁ * (N : ℝ) ^ 2 * W₁ N := by
    refine le_trans (Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_) (h₁ N hN)
    rw [← tailProd_zero_eq_Bf, ← tailProd_mul (ξ n m) (Nat.zero_le _) hM]
    exact mul_le_of_le_one_right (tailProd_nonneg _ _ _) (tailProd_le_one _ _ _)
  have hC : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m| / 3 ^ (10 * S) ≤
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simp only [← Finset.sum_div]
    rw [div_le_iff₀ h3S]
    nlinarith
  have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
    (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
  calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (tailProd (ξ n m) 0 (10 * S) +
            ∑ S' ∈ Finset.range S, ‖deadChar (ξ n m) S'‖ * tailProd (ξ n m) (10 * S' + 10) (10 * S) +
              16 * |ξ n m| / 3 ^ (10 * S)) :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => fourierAbs_resLaw_le _ S
    _ = _ + _ + _ := by simp only [Finset.sum_add_distrib]
    _ ≤ C₁ * (N : ℝ) ^ 2 * W₁ N + C₂ * (N : ℝ) ^ 2 * W₂ N +
          (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := add_le_add (add_le_add hA (h₂' N hN S)) hC
    _ ≤ |C₁| * (N : ℝ) ^ 2 * |W₁ N| + |C₂| * (N : ℝ) ^ 2 * |W₂ N| +
          (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith [k C₁ (W₁ N), k C₂ (W₂ N)]
    _ ≤ _ := by
        have a1 := abs_nonneg C₁; have a2 := abs_nonneg C₂
        have b1 := abs_nonneg (W₁ N); have b2 := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) b2, mul_nonneg (mul_nonneg a2 hN2) b1,
          mul_nonneg (mul_nonneg a1 hN2) hr, mul_nonneg (mul_nonneg a2 hN2) hr,
          mul_nonneg hN2 b1, mul_nonneg hN2 b2]


/-! ### The signed route: the crux without absolute values

`prefChar_eq` unrolls the stage recursion exactly, with signs.  The second moment is a *signed*
sum of Fourier coefficients (`secondMoment_le_norm_sum`), so the crux only needs the signed
pair sum of the dead-children terms (`deadCharSigned`), which is weaker than the absolute form
`DeadCharCancelAbs` (`deadCharSigned_of_abs`). -/

/-- `Π_{a ≤ s < S} ρ_s(ξ)`. -/
noncomputable def rhoProd (ξ : ℝ) (a S : ℕ) : ℂ := ∏ s ∈ Finset.Ico a S, rhoS ξ (10 * s)

theorem norm_rhoProd (ξ : ℝ) {a S : ℕ} (h : a ≤ S) : ‖rhoProd ξ a S‖ = tailProd ξ (10 * a) (10 * S) := by
  induction S, h using Nat.le_induction with
  | base => simp [rhoProd, tailProd_self]
  | succ S haS ih =>
    rw [rhoProd, Finset.prod_Ico_succ_top haS, norm_mul, ← rhoProd, ih, norm_rhoS,
      show 10 * (S + 1) = 10 * S + 10 by ring, tailProd_mul ξ (by omega) (by omega)]

/-- **Exact unrolled recursion.**  Proved from `prefChar_succ`. -/
theorem prefChar_eq (ξ : ℝ) (S : ℕ) :
    prefChar ξ S = rhoProd ξ 0 S - ∑ S' ∈ Finset.range S, deadChar ξ S' * rhoProd ξ (S' + 1) S := by
  induction S with
  | zero => simp [prefChar_zero, rhoProd]
  | succ S ih =>
    rw [prefChar_succ, ih, Finset.sum_range_succ]
    have h1 : rhoProd ξ 0 (S + 1) = rhoProd ξ 0 S * rhoS ξ (10 * S) := by
      rw [rhoProd, Finset.prod_Ico_succ_top (Nat.zero_le _)]; rfl
    have h2 : ∀ S' ∈ Finset.range S, rhoProd ξ (S' + 1) (S + 1) =
        rhoProd ξ (S' + 1) S * rhoS ξ (10 * S) := by
      intro S' hS'
      rw [Finset.mem_range] at hS'
      rw [rhoProd, Finset.prod_Ico_succ_top (by omega)]; rfl
    have h3 : rhoProd ξ (S + 1) (S + 1) = 1 := by simp [rhoProd]
    have hs : ∑ S' ∈ Finset.range S, deadChar ξ S' * rhoProd ξ (S' + 1) (S + 1) =
        rhoS ξ (10 * S) * ∑ S' ∈ Finset.range S, deadChar ξ S' * rhoProd ξ (S' + 1) S := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S' hS' => ?_
      rw [h2 S' hS']; ring
    rw [h1, h3, hs]
    ring

/-- The second moment is the real part of a signed pair sum of Fourier coefficients.  Proved. -/
theorem secondMoment_le_norm_sum (L : Law) (b : ℕ) (h : ℤ) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure ≤
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) ∂coinMeasure‖ := by
  have hG : Measurable fun ω => cpt (L.φ ω) := measurable_cpt.comp L.meas
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * cpt (L.φ ω))) coinMeasure := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * (b : ℝ) ^ k * cpt (L.φ ω))]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  exact Complex.re_le_norm _

/-- **Each child character is within `2π|ξ|/3^L` of the stage average.**  Proved. -/
theorem norm_ee_sub_rhoS_le (ξ : ℝ) (L : ℕ) (f : Fin 10 → Bool) :
    ‖ee (ξ * J f / 3 ^ (L + 10)) - rhoS ξ L‖ ≤ 2 * Real.pi * |ξ| / 3 ^ L := by
  have h3 : (0 : ℝ) < 3 ^ L := by positivity
  have hrw : ee (ξ * J f / 3 ^ (L + 10)) - rhoS ξ L =
      (1 / 1024 : ℂ) * ∑ g : Fin 10 → Bool, (ee (ξ * J f / 3 ^ (L + 10)) - ee (ξ * J g / 3 ^ (L + 10))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin 10 → Bool) = 1024 by simp, rhoS]
    simp only [nsmul_eq_mul]; push_cast; ring
  have hterm : ∀ g : Fin 10 → Bool,
      ‖ee (ξ * J f / 3 ^ (L + 10)) - ee (ξ * J g / 3 ^ (L + 10))‖ ≤ 2 * Real.pi * |ξ| / 3 ^ L := by
    intro g
    refine (norm_ee_sub_ee _ _).trans ?_
    have hJ : |(J f : ℝ) - J g| ≤ 3 ^ 10 := by
      have a := J_lt f; have b := J_lt g
      rw [abs_le]; constructor <;> [skip; skip] <;>
        · have : ((J f : ℕ) : ℝ) < 3 ^ 10 := by exact_mod_cast a
          have : ((J g : ℕ) : ℝ) < 3 ^ 10 := by exact_mod_cast b
          have := (Nat.cast_nonneg (α := ℝ) (J f)); have := (Nat.cast_nonneg (α := ℝ) (J g))
          linarith
    have : ξ * J f / 3 ^ (L + 10) - ξ * J g / 3 ^ (L + 10) = ξ * ((J f : ℝ) - J g) / (3 ^ L * 3 ^ 10) := by
      rw [pow_add]; ring
    rw [this, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ L * 3 ^ 10)]
    have hp : 0 ≤ 2 * Real.pi := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) h3]
    have := mul_le_mul_of_nonneg_left hJ (abs_nonneg ξ)
    nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt h3), abs_nonneg ξ, Real.pi_pos]
  rw [hrw, norm_mul]
  calc ‖(1 / 1024 : ℂ)‖ * ‖∑ g : Fin 10 → Bool, _‖
      ≤ (1 / 1024) * ∑ g : Fin 10 → Bool, 2 * Real.pi * |ξ| / 3 ^ L := by
        rw [show ‖(1 / 1024 : ℂ)‖ = 1 / 1024 by norm_num]
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => hterm g)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, show Fintype.card (Fin 10 → Bool) = 1024 by simp]
        simp only [nsmul_eq_mul]; push_cast; ring

/-- **The dead-children error is `O(|ξ| 3^{−L})`.**  Proved. -/
theorem norm_deadErr_le (ξ : ℝ) (w : List Bool) :
    ‖deadErr ξ w‖ ≤ 1024 * (2 * Real.pi * |ξ| / 3 ^ w.length) := by
  unfold deadErr
  have hA : (1 : ℝ) ≤ (aliveSet w).card := by exact_mod_cast card_aliveSet_pos w
  rw [norm_mul]
  calc ‖1 / ((aliveSet w).card : ℂ)‖ * ‖∑ f ∈ Finset.univ \ aliveSet w, _‖
      ≤ 1 * ∑ f ∈ Finset.univ \ aliveSet w, 2 * Real.pi * |ξ| / 3 ^ w.length := by
        gcongr
        · rw [norm_div, norm_one, Complex.norm_natCast]
          exact div_le_one_of_le₀ hA (by positivity)
        · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => norm_ee_sub_rhoS_le _ _ _)
    _ ≤ _ := by
        rw [one_mul, Finset.sum_const, nsmul_eq_mul]
        gcongr
        have : (Finset.univ \ aliveSet w).card ≤ 1024 := (Finset.card_le_univ _).trans (by simp)
        exact_mod_cast this

/-- **The stage-`S'` dead character is `O(|ξ| 3^{−10S'})`.**  Proved. -/
theorem norm_deadChar_le (ξ : ℝ) (S : ℕ) :
    ‖deadChar ξ S‖ ≤ 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * S)) := by
  unfold deadChar
  have := norm_integral_le_of_norm_le_const (μ := coinMeasure)
    (f := fun ω => ee (ξ * cylLeft (buildU S ω)) * deadErr ξ (buildU S ω))
    (C := 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * S))) (Eventually.of_forall fun ω => by
      rw [norm_mul, norm_ee, one_mul, ← length_buildU ω S]; exact norm_deadErr_le _ _)
  simpa using this
theorem nat_tail_ineq {b N k : ℕ} (hb : 2 ≤ b) (hN : 1 ≤ N) :
    3 ^ 10 * k * b ^ N * N ≤ 3 ^ (9 * (N * b + k)) := by
  have h1 : k ≤ 3 ^ k := (Nat.lt_pow_self (by norm_num)).le
  have h2 : b ^ N ≤ 3 ^ (b * N) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_pow_self (by norm_num)).le _
  have h3 : N ≤ 3 ^ (b * N) :=
    (Nat.lt_pow_self (by norm_num)).le.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have h4 : 3 ^ 10 ≤ 3 ^ (5 * (b * N)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc 3 ^ 10 * k * b ^ N * N ≤ 3 ^ (5 * (b * N)) * 3 ^ k * 3 ^ (b * N) * 3 ^ (b * N) := by gcongr
    _ = 3 ^ (7 * (b * N) + k) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **Stages beyond `S₀ = N b + |h|` are negligible** (locality, from `norm_deadChar_le`).
Proved: the tail of the signed stage sum is at most `1/N` for each pair `(n, m)`. -/
theorem deadChar_tail_le {b : ℕ} (hb : 2 ≤ b) (h : ℤ) {N n m : ℕ} (hN : 1 ≤ N) (hn : n ≤ N)
    (hm : m ≤ N) (S : ℕ) :
    ‖∑ S' ∈ Finset.Ico (N * b + h.natAbs) S, deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
        rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ 1 / N := by
  set ξ : ℝ := h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  set S₀ := N * b + h.natAbs
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hξ : |ξ| ≤ 2 * h.natAbs * (b : ℝ) ^ N := by
    have e1 : (b : ℝ) ^ n ≤ (b : ℝ) ^ N := pow_le_pow_right₀ hb1 hn
    have e2 : (b : ℝ) ^ m ≤ (b : ℝ) ^ N := pow_le_pow_right₀ hb1 hm
    have p1 : (0 : ℝ) ≤ (b : ℝ) ^ n := by positivity
    have p2 : (0 : ℝ) ≤ (b : ℝ) ^ m := by positivity
    have hna : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [abs_mul, hna]
    have : |(b : ℝ) ^ n - (b : ℝ) ^ m| ≤ 2 * (b : ℝ) ^ N := by rw [abs_le]; constructor <;> linarith
    calc |(h : ℝ)| * |(b : ℝ) ^ n - (b : ℝ) ^ m| ≤ |(h : ℝ)| * (2 * (b : ℝ) ^ N) := by gcongr
      _ = _ := by ring
  set Y : ℝ := 1024 * (2 * Real.pi * |ξ|) / 3 ^ (9 * S₀)
  have hterm : ∀ S' ∈ Finset.Ico S₀ S, ‖deadChar ξ S' * rhoProd ξ (S' + 1) S‖ ≤ Y * (1 / 3) ^ S' := by
    intro S' hS'
    rw [Finset.mem_Ico] at hS'
    have hp : (3 : ℝ) ^ (9 * S₀) * 3 ^ S' ≤ 3 ^ (10 * S') := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [norm_mul, norm_rhoProd _ (by omega)]
    calc ‖deadChar ξ S'‖ * tailProd ξ (10 * (S' + 1)) (10 * S) ≤ ‖deadChar ξ S'‖ :=
          mul_le_of_le_one_right (norm_nonneg _) (tailProd_le_one _ _ _)
      _ ≤ 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * S')) := norm_deadChar_le ξ S'
      _ = 1024 * (2 * Real.pi * |ξ|) / 3 ^ (10 * S') := by ring
      _ ≤ 1024 * (2 * Real.pi * |ξ|) / (3 ^ (9 * S₀) * 3 ^ S') :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hp
      _ = Y * (1 / 3) ^ S' := by simp only [Y]; rw [one_div_pow]; field_simp
  have hgeo : ∑ S' ∈ Finset.Ico S₀ S, (1 / 3 : ℝ) ^ S' ≤ 3 / 2 :=
    (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans (by
      rw [div_le_iff₀ (by norm_num)]
      have : (1 / 3 : ℝ) ^ S₀ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith)
  have hY : 0 ≤ Y := by positivity
  have hfin : Y * (3 / 2) ≤ 1 / N := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have key : ((3 ^ 10 * h.natAbs * b ^ N * N : ℕ) : ℝ) ≤ ((3 ^ (9 * S₀) : ℕ) : ℝ) := by
      exact_mod_cast nat_tail_ineq hb hN
    push_cast at key
    rw [le_div_iff₀ hNpos]
    have hpi := Real.pi_lt_four
    have h1 : 1024 * (2 * Real.pi * |ξ|) * (3 / 2) * N ≤ 3 ^ 10 * h.natAbs * (b : ℝ) ^ N * N := by
      have : 1024 * (2 * Real.pi * |ξ|) * (3 / 2) ≤ 3 ^ 10 * h.natAbs * (b : ℝ) ^ N := by
        have hh0 : (0 : ℝ) ≤ h.natAbs * (b : ℝ) ^ N := by positivity
        nlinarith [abs_nonneg ξ, Real.pi_pos]
      exact mul_le_mul_of_nonneg_right this hNpos.le
    have h3 : (0 : ℝ) < 3 ^ (9 * S₀) := by positivity
    calc Y * (3 / 2) * N = 1024 * (2 * Real.pi * |ξ|) * (3 / 2) * N / 3 ^ (9 * S₀) := by
          simp only [Y]; ring
      _ ≤ 1 := by rw [div_le_one h3]; exact h1.trans (by norm_num at key ⊢; linarith)
  calc _ ≤ ∑ S' ∈ Finset.Ico S₀ S, ‖deadChar ξ S' * rhoProd ξ (S' + 1) S‖ := norm_sum_le _ _
    _ ≤ ∑ S' ∈ Finset.Ico S₀ S, Y * (1 / 3) ^ S' := Finset.sum_le_sum hterm
    _ = Y * ∑ S' ∈ Finset.Ico S₀ S, (1 / 3 : ℝ) ^ S' := by rw [Finset.mul_sum]
    _ ≤ Y * (3 / 2) := mul_le_mul_of_nonneg_left hgeo hY
    _ ≤ _ := hfin

/-- **Refuted route: the Cauchy–Schwarz bootstrap.**  The recurrence
`f(N) ≤ f_K(N) + c √(η f(N))` that it produces for `f = E|S_N|²/N²` does not force decay: with
`f_K ≡ 0` (the best possible Cantor input), the constant `f ≡ c² η` satisfies it and stays bounded away from `0`.
So `deadCharSigned_core` cannot follow from Cauchy–Schwarz on dead events.  Proved. -/
theorem cs_bootstrap_floor {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∃ f : ℕ → ℝ, (∀ N, f N ≤ 0 + c * Real.sqrt (η * f N)) ∧ ∀ N, f N = c ^ 2 * η ∧ 0 < f N := by
  refine ⟨fun _ => c ^ 2 * η, fun N => ?_, fun N => ⟨rfl, by positivity⟩⟩
  have : η * (c ^ 2 * η) = (c * η) ^ 2 := by ring
  rw [this, Real.sqrt_sq (by positivity)]; nlinarith

/-- **Conjecture node: per-stage saving.**  Believed 20%, and open-problem strength (see the `S' = 0` analysis below).  Each stage `S'` contributes to the
signed pair sum at most `C N W(N)` (`W` summable along `sched`; e.g. `N^{−δ}`), uniformly in `S'` and in the depth `S`.

Heuristic: the stage changes only `O(1)` frozen terms of `S_N` (see `deadCharSigned_core`), so it
contributes `≈ P(dead at S') · E[|A| | dead]`.  That is `O(η √n₀)` if the lacunary sums
`Σ_{n<n₀} e(h bⁿ p/q)` at the obstacle centres near `K` have square-root size on average.  The
per-stage form is stronger than needed (only the sum over the `O(N)` stages matters), but it isolates
the decorrelation input at a single scale `3^{10S'}`.

Test case `S' = 0` (no dead history, deterministic prefix `[]`): the term is
`E_{τ₁}|S_N|² − E_{τ₀}|S_N|²` for two scaled Cantor copies (the dead-child mix and the uniform mix).
Both are `N + o(N)`, since off-diagonal lags `d` have limit `∫ e(h(b^d − 1)x) dx = 0`.  So the leaf at
`S' = 0` asks for an `N W(N)` rate in that limit (for a power `W`), which is Schmidt-type power saving
(Schmidt 1960, *On normal numbers*, the cosine-product lemma: `Σ_{n<N} Π_k |cos(π h rⁿ/s^k)| ≤ 2N^{1−δ}`).
That rate is known for the frequencies `h bⁿ`, but not uniformly for the differences
`h(bⁿ − bᵐ)` that appear here.  Worse, at `S' = 0` the node asks for `E|S_N|² = N + O(N W(N))` under a scaled Cantor copy.  That is
variance at CLT scale for `×b` on `μ_K`: Schmidt's bound, uniform in the frequency, sums over the
`N` lags to only `N^{2−δ}`.  So the per-stage triangle inequality is lossy, and
`deadCharSigned_core_of_stageSaving` is kept only as a recorded implication.  The trivial bound is `2N²`, from
`|deadChar| ≤ 2`, and `cs_bootstrap_floor` shows that Cauchy–Schwarz cannot improve the exponent. -/
def StageSaving (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S S' : ℕ,
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
            rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * N * W N

/-- **Hybrid telescope.**  Proved from `prefChar_succ`.  The dead-character stage sum is
`Π_{s<S} ρ_s − T_a · Π_{a≤s<S} ρ_s`, the character of uniform digits minus that of the hybrid law
(`resLaw` for `a` stages, then uniform digits to depth `S`). -/
theorem stage_telescope (ξ : ℝ) {a S : ℕ} (haS : a ≤ S) :
    ∑ S' ∈ Finset.range a, deadChar ξ S' * rhoProd ξ (S' + 1) S =
      rhoProd ξ 0 S - prefChar ξ a * rhoProd ξ a S := by
  induction a with
  | zero => simp [prefChar_zero, rhoProd]
  | succ a ih =>
    rw [Finset.sum_range_succ, ih (by omega), prefChar_succ]
    have : rhoProd ξ a S = rhoS ξ (10 * a) * rhoProd ξ (a + 1) S := by
      rw [rhoProd, rhoProd, Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    rw [this]; ring

/-- `exp(−c ⌊log₃N⌋/2) ≤ e^c N^{−c/(2 log 3)}`.  Proved (from the `cassels_Bf` bookkeeping). -/
theorem exp_neg_log3_le {c : ℝ} (hc : 0 ≤ c) {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (-c * ((Nat.log 3 N / 2 : ℕ) : ℝ)) ≤ Real.exp c * (N : ℝ) ^ (-(c / (2 * Real.log 3))) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set k := Nat.log 3 N
  have hlt : N < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlog : Real.log N < (k + 1) * Real.log 3 := by
    have : (N : ℝ) < (3 : ℝ) ^ (k + 1) := by exact_mod_cast hlt
    have := Real.log_lt_log hN0 this
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
  have hk2 : (k : ℝ) - 1 ≤ 2 * ((k / 2 : ℕ) : ℝ) := by
    have : k ≤ 2 * (k / 2) + 1 := by omega
    have : (k : ℝ) ≤ 2 * ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have : Real.log N * (1 / Real.log 3) < k + 1 := by
    rw [← div_eq_mul_one_div, div_lt_iff₀ hl3]; linarith
  have hδ : Real.log N * -(c / (2 * Real.log 3)) = -(c / 2) * (Real.log N * (1 / Real.log 3)) := by
    field_simp
  rw [hδ]
  nlinarith

/-- **Cassels for the Cantor digits above position `p₀`** (proved).  If `2p₀ ≤ ⌊log₃N⌋/2`, the
pair sum of the digit products over positions `p₀ ≤ p < ⌊log₃N⌋/2` has a power saving, uniformly
in `p₀`. -/
theorem cassels_tail {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ p₀ : ℕ,
      2 * p₀ ≤ Nat.log 3 N / 2 →
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        tailProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) p₀ (Nat.log 3 N / 2) ≤ C * (N : ℝ) ^ 2 * W N := by
  set e := padicValNat 3 h.natAbs
  set t := CantorLiouvilleAll.tb b
  set c : ℝ := Real.log (3 / 2) / 2
  have hc : 0 < c := by unfold c; have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); positivity
  set c' : ℝ := c / 2
  have hc' : 0 < c' := by positivity
  set δ : ℝ := c' / (2 * Real.log 3)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set K : ℝ := 3 * (3 ^ (e + t) + 2 * (3 / 2 : ℝ) ^ t)
  have hK : 0 ≤ K := by positivity
  refine ⟨K * Real.exp c' * Real.exp c' + 1,
    fun N => (N : ℝ) ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (-δ),
    (summable_sched_rpow (by norm_num)).add (summable_sched_rpow (by positivity)),
    fun N hN p₀ hp => ?_⟩
  set M := Nat.log 3 N / 2
  set free : ℕ → Bool := fun p => decide (p₀ ≤ p)
  have hB := pairSum_Bf_le_explicit_b free hb h3 h hh N hN
  have hBf : ∀ ξ : ℝ, CantorLiouville.Bf free M ξ = tailProd ξ p₀ M := by
    intro ξ
    unfold CantorLiouville.Bf tailProd
    congr 1
    ext p; simp [free, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hBf _] at hB
  have hF : (M : ℝ) - 1 ≤ 2 * (CantorLiouville.freeCount free M : ℝ) := by
    have : M - p₀ ≤ CantorLiouville.freeCount free M := by
      unfold CantorLiouville.freeCount
      rw [← Nat.card_Ico]
      refine Finset.card_le_card fun i hi => ?_
      simp only [Finset.mem_Ico] at hi
      simp only [Finset.mem_filter, Finset.mem_range, free]
      exact ⟨hi.2, by simpa using hi.1⟩
    have h2 : M ≤ 2 * CantorLiouville.freeCount free M + 1 := by omega
    have : (M : ℝ) ≤ 2 * (CantorLiouville.freeCount free M : ℝ) + 1 := by exact_mod_cast h2
    linarith
  have hexp : Real.exp (-c * CantorLiouville.freeCount free M) ≤
      Real.exp c' * (Real.exp c' * (N : ℝ) ^ (-δ)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (exp_neg_log3_le hc'.le hN) (Real.exp_pos _).le)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    simp only [c']; nlinarith
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hr2 : (0 : ℝ) ≤ (N : ℝ) ^ (-δ) := by positivity
  have hE2 : 0 ≤ Real.exp c' * Real.exp c' := by positivity
  calc _ ≤ _ := hB
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
          K * (N : ℝ) ^ 2 * (Real.exp c' * (Real.exp c' * (N : ℝ) ^ (-δ))) := by
        have := mul_le_mul_of_nonneg_left hexp (mul_nonneg hK hN2)
        simp only [K, c] at this ⊢
        linarith
    _ ≤ _ := by
        have h1 := mul_nonneg (mul_nonneg hK hE2) (mul_nonneg hN2 hr)
        nlinarith [mul_nonneg hN2 hr, mul_nonneg hN2 hr2, mul_nonneg (mul_nonneg hK hN2) hr]

/-- **The hybrid Cassels bound for few `resLaw` stages** (proved; special case of
`hybridCassels`).  If `20a ≤ ⌊log₃N⌋/2 ≤ 10S`, the hybrid law (`a` stages of `resLaw`, then
uniform digits) has the Cassels power saving, uniformly in `a` and `S`. -/
theorem hybridCassels_low {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ a S : ℕ,
      2 * (10 * a) ≤ Nat.log 3 N / 2 → Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        prefChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) a *
          rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) a S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C, W, hW, hC⟩ := cassels_tail hb h3 h hh
  refine ⟨C, W, hW, fun N hN a S ha hS => ?_⟩
  refine le_trans ?_ (hC N hN (10 * a) ha)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun m _ => ?_))
  set ξ : ℝ := h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  have haS : a ≤ S := by omega
  have hpc : ‖prefChar ξ a‖ ≤ 1 := by
    unfold prefChar
    refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω => ?_)).trans
      (by simp)
    rw [norm_ee]
  rw [norm_mul, norm_rhoProd _ haS]
  calc ‖prefChar ξ a‖ * tailProd ξ (10 * a) (10 * S) ≤ 1 * tailProd ξ (10 * a) (10 * S) :=
        mul_le_mul_of_nonneg_right hpc (tailProd_nonneg _ _ _)
    _ = tailProd ξ (10 * a) (Nat.log 3 N / 2) * tailProd ξ (Nat.log 3 N / 2) (10 * S) := by
        rw [one_mul, tailProd_mul ξ (by omega) hS]
    _ ≤ _ := mul_le_of_le_one_right (tailProd_nonneg _ _ _) (tailProd_le_one _ _ _)

/-- **The crux, middle stages only** (open; believed 55%).  The signed dead-character sum over the
stages `a₁ ≤ S' < a`, where `a₁ = min a (⌊log₃N⌋/2/20)` and `a = min S (N b + |h|)`, is
`O(N² W(N))`.  The low stages `S' < a₁` are free (`hybridCassels_low`) and the high ones are
local (`deadChar_tail_le`).  What remains is exactly the stages whose scale `3^{10S'}` lies
between `N^{1/40}` and the frequency scale `b^N`.  This is where the decorrelation of dead events
(rationals near `K`) from the lacunary sums is needed.

Off the headline path since lap 6 (the headline now goes through the local route,
`localDeadBias_resLaw`).  Reason: this is a Cassels *rate* for `resLaw`, and any stage-by-stage
bound of it multiplies each dead correction by `rhoProd ξ (S' + 1) S`, whose modulus lives on the
middle and leading ternary digits of `bⁿ`.  Granting the decorrelation, a rate still needs
quantitative equidistribution of `n log₃ b` (Baker-type input).  The local route needs only its
irrationality. -/
theorem midStages {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ,
      Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.Ico (min (min S (N * b + h.natAbs)) (Nat.log 3 N / 2 / 20))
            (min S (N * b + h.natAbs)),
          deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
            rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  sorry

/-- **The hybrid-law Cassels bound.**  Proved from `hybridCassels_low` and `midStages` (open).  The pair sum of
the hybrid characters `T_a(ξ) Π_{a≤s<S} ρ_s(ξ)`, which is `E|S_N|²` under `resLaw` for `a`
stages followed by uniform Cantor digits, is `O(N² W(N))` for `a = min S (N b + |h|)`.  It
implies `deadCharSigned_core`, because the uniform part is
`cassels_Bf`. -/
theorem hybridCassels {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        prefChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (min S (N * b + h.natAbs)) *
          rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (min S (N * b + h.natAbs)) S‖ ≤
        C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := hybridCassels_low hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := midStages hb h3 h hh
  refine ⟨|C₁| + |C₂|, fun N => |W₁ N| + |W₂ N|, hW₁.abs.add hW₂.abs, fun N hN S hS => ?_⟩
  set a := min S (N * b + h.natAbs)
  set a₁ := min a (Nat.log 3 N / 2 / 20)
  set ξ : ℕ → ℕ → ℝ := fun n m => h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  have haS : a ≤ S := min_le_left _ _
  have ha₁ : a₁ ≤ a := min_le_left _ _
  have hH : ∀ n m, prefChar (ξ n m) a * rhoProd (ξ n m) a S =
      prefChar (ξ n m) a₁ * rhoProd (ξ n m) a₁ S -
        ∑ S' ∈ Finset.Ico a₁ a, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S := by
    intro n m
    have e1 := stage_telescope (ξ n m) haS
    have e2 := stage_telescope (ξ n m) (ha₁.trans haS)
    rw [← Finset.sum_range_add_sum_Ico _ ha₁] at e1
    rw [e2] at e1
    linear_combination e1
  have hlow := h₁ N hN a₁ S (by omega) hS
  have hmid := h₂ N hN S hS
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
    (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
  calc _ = ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, prefChar (ξ n m) a₁ * rhoProd (ξ n m) a₁ S -
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ∑ S' ∈ Finset.Ico a₁ a, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S‖ := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => hH n m
    _ ≤ _ := norm_sub_le _ _
    _ ≤ C₁ * (N : ℝ) ^ 2 * W₁ N + C₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add hlow hmid
    _ ≤ _ := by
        have := k C₁ (W₁ N); have := k C₂ (W₂ N)
        have a1 := abs_nonneg C₁; have a2 := abs_nonneg C₂
        have b1 := abs_nonneg (W₁ N); have b2 := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) b2, mul_nonneg (mul_nonneg a2 hN2) b1]

/-- **The crux, localized to the first `S₀ = N b + |h|` stages.**  Proved from `hybridCassels`
(via `stage_telescope`) and `cassels_Bf`.  The analysis below is of the open input.

This is `deadCharSigned` with the stage sum cut at `S₀(N) = N b + |h|`.  The cut loses
nothing, since later stages contribute `≤ 1/N` per pair (`deadChar_tail_le`).  So only the
`O(N)` stages whose scale `3^{10S'}` is at most about `b^N` remain.

What a proof must supply.  The `S'`-term equals `E_{ν_{S'+1}}|S_N|² − E_{ν_{S'}}|S_N|²` for the
hybrid laws `ν_{S'}` (`resLaw` for `S'` stages, then Cantor coins).  Write
`S_N = A + B`, where `A` holds the terms with `bⁿ < 3^{10S'}` (frozen by the prefix) and `B` the
terms randomized by the Cantor tail.  Changing the stage-`S'` block moves only `O(1)` terms of
`A`, so that stage changes `|A|²` by `O(P(dead at S') · E[|A| | dead at S'])`.

Two routes are recorded as insufficient here.
(1) Cauchy–Schwarz bootstrap (`cs_bootstrap_floor`).  Bounding `E[1_dead |A|] ≤ √(η E|A|²)` gives
`f(N) ≤ f_K(N) + c√(η f(N))` for `f = E|S_N|²/N²`.  That recurrence has the constant solution
`f ≍ η`, so it gives only a floor, never decay.
(2) Large sieve over the obstacle centres `p/q`, `q² ≍ 3^{10S'}`.  This bounds the average of
`|A(p/q)|²` over all Farey fractions by `O(n₀)`.  The centres near `K` are a sparse subset, and
restricting to them loses the factor `(3/2)^{10S'}`.
What is needed is the decorrelation `E_ν[1_{dead at S'} |A|²] ≲ P(dead at S') · n₀^{2−δ}`: the
lacunary sums `Σ_{n<n₀} e(h bⁿ p/q)` are not inflated at the centres `p/q` near `K`.
Heuristically this follows from the equidistribution of rationals near `K` (Khalil–Lüthi;
Bénard–He–Zhang) together with Cassels decay of `μ̂_K` at the reduced frequencies
`h(bⁿ − bᵐ) mod q`.  Guards: it fails for `b = 3` and for dyadic centres
(`perStage_deadCount_not_enough`). -/
theorem deadCharSigned_core {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range (min S (N * b + h.natAbs)),
          deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
            rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := cassels_Bf hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := hybridCassels hb h3 h hh
  refine ⟨|C₁| + |C₂|, fun N => |W₁ N| + |W₂ N|, hW₁.abs.add hW₂.abs, fun N hN S hS => ?_⟩
  set a := min S (N * b + h.natAbs)
  set ξ : ℕ → ℕ → ℝ := fun n m => h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  have hA : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ ≤
      C₁ * (N : ℝ) ^ 2 * W₁ N := by
    refine le_trans (Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_) (h₁ N hN)
    rw [norm_rhoProd _ (Nat.zero_le _), mul_zero, ← tailProd_zero_eq_Bf,
      ← tailProd_mul (ξ n m) (Nat.zero_le _) hS]
    exact mul_le_of_le_one_right (tailProd_nonneg _ _ _) (tailProd_le_one _ _ _)
  have hB := h₂ N hN S hS
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
    (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
  calc _ = ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, rhoProd (ξ n m) 0 S -
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, prefChar (ξ n m) a * rhoProd (ξ n m) a S‖ := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => stage_telescope _ (min_le_left _ _)
    _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ +
        ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, prefChar (ξ n m) a * rhoProd (ξ n m) a S‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n _ => norm_sum_le _ _)) le_rfl)
    _ ≤ C₁ * (N : ℝ) ^ 2 * W₁ N + C₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add hA hB
    _ ≤ _ := by
        have := k C₁ (W₁ N); have := k C₂ (W₂ N)
        have a1 := abs_nonneg C₁; have a2 := abs_nonneg C₂
        have b1 := abs_nonneg (W₁ N); have b2 := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) b2, mul_nonneg (mul_nonneg a2 hN2) b1]

/-- The node `StageSaving` implies the localized crux.  Proved, by summing over the at most
`(b + |h|) N` stages. -/
theorem deadCharSigned_core_of_stageSaving {b : ℕ} (hS : StageSaving b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range (min S (N * b + h.natAbs)),
          deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
            rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C, W, hW, hC⟩ := hS h hh
  refine ⟨|C| * (b + h.natAbs), fun N => |W N|, hW.abs, fun N hN S _ => ?_⟩
  set a := min S (N * b + h.natAbs)
  have hswap : ∀ F : ℕ → ℕ → ℕ → ℂ, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ∑ S' ∈ Finset.range a, F n m S' =
        ∑ S' ∈ Finset.range a, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, F n m S' := by
    intro F
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_comm]
    exact Finset.sum_comm
  rw [hswap]
  have ha : (a : ℝ) ≤ (b + h.natAbs) * N := by
    have : a ≤ N * b + h.natAbs := min_le_right _ _
    have h2 : (a : ℝ) ≤ N * b + h.natAbs := by exact_mod_cast this
    have : (h.natAbs : ℝ) ≤ h.natAbs * N := le_mul_of_one_le_right (by positivity)
      (by exact_mod_cast hN)
    nlinarith
  have hk : 0 ≤ |C| * N * |W N| := by positivity
  calc _ ≤ ∑ S' ∈ Finset.range a, |C| * N * |W N| :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun S' _ => (hC N hN S S').trans (by
          have := le_abs_self (C * N * W N)
          rw [abs_mul, abs_mul, Nat.abs_cast] at this; exact this))
    _ = a * (|C| * N * |W N|) := by simp
    _ ≤ (b + h.natAbs) * N * (|C| * N * |W N|) := mul_le_mul_of_nonneg_right ha hk
    _ = _ := by ring

/-- **The crux (signed form): cancellation in the dead-children terms.**  Proved from the
localized crux `deadCharSigned_core` (stages `< N b + |h|`, open) and the tail bound
`deadChar_tail_le`.

Uniformly in the depth `S`, `‖Σ_{n,m<N} Σ_{S'<S} deadChar(ξ, S')·Π_{S'<s<S} ρ_s(ξ)‖ = O(N² W(N))`,
`ξ = h(bⁿ − bᵐ)`.  For each `S'` the inner pair sum is `∫ |S_N|² dτ_{S'}` for the signed measure
`τ_{S'}` = (`resLaw` to stage `S'`) ⊗ (dead child minus its share of a uniform child) ⊗ (Cantor
tail): the diagonal `n = m` cancels exactly (equal masses), terms with `bⁿ ≪ 3^{10S'}` change by
`O(1)` in total between the two parts, so heuristically each stage contributes
`O(P(dead at S')·N^{1/2}·N)` and the sum is `O(η N^{3/2})`.  This is weaker than
`DeadCharCancelAbs` (`deadCharSigned_of_abs`), whose triangle inequality over `(n, m)` forfeits
this cancellation and needs Fourier decay at the middle ternary digits of `bⁿ`.

Guards: `b = 3` is false (`cantor_not_normal_three_pow`), and the base-2 dyadic sibling
(`perStage_deadCount_not_enough`) must fail: its dead children sit at `p/2ᵏ`, where
`|S_N|²` is maximal, so `∫ |S_N|² dτ` has a sign and does not cancel. -/
theorem deadCharSigned {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range S, deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
          rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C, W, hW, hC⟩ := deadCharSigned_core hb h3 h hh
  refine ⟨|C| + 1, fun N => |W N| + (N : ℝ) ^ (-(1 / 2 : ℝ)),
    hW.abs.add (summable_sched_rpow (by norm_num)), fun N hN S hS => ?_⟩
  set S₀ := N * b + h.natAbs
  set F : ℕ → ℕ → ℕ → ℂ := fun n m S' => deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
    rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : ∀ n m, ∑ S' ∈ Finset.range S, F n m S' =
      ∑ S' ∈ Finset.range (min S S₀), F n m S' + ∑ S' ∈ Finset.Ico (min S S₀) S, F n m S' :=
    fun n m => (Finset.sum_range_add_sum_Ico _ (min_le_left _ _)).symm
  have htail : ∀ n ∈ Finset.range N, ∀ m ∈ Finset.range N,
      ‖∑ S' ∈ Finset.Ico (min S S₀) S, F n m S'‖ ≤ 1 / N := by
    intro n hn m hm
    rw [Finset.mem_range] at hn hm
    by_cases hS : S₀ ≤ S
    · rw [min_eq_right hS]; exact deadChar_tail_le hb h hN hn.le hm.le S
    · rw [min_eq_left (by omega), Finset.Ico_self, Finset.sum_empty, norm_zero]; positivity
  have hC' := hC N hN S hS
  have hT : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ‖∑ S' ∈ Finset.Ico (min S S₀) S, F n m S'‖ ≤ N := by
    calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (1 / N : ℝ) :=
          Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => htail n hn m hm
      _ = N := by simp; field_simp
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hrN : (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 : ℝ) by
        rw [← Real.rpow_add hNpos]; norm_num, mul_assoc, ← Real.rpow_add hNpos, Real.rpow_one]
      norm_num
    rw [this]
    exact le_mul_of_one_le_right hNpos.le (Real.one_le_rpow (by exact_mod_cast hN) (by norm_num))
  calc ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ S' ∈ Finset.range S, F n m S'‖
      ≤ ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ S' ∈ Finset.range (min S S₀), F n m S'‖ +
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ‖∑ S' ∈ Finset.Ico (min S S₀) S, F n m S'‖ := by
        simp_rw [hsplit, Finset.sum_add_distrib]
        exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n _ => norm_sum_le _ _)))
    _ ≤ C * (N : ℝ) ^ 2 * W N + N := add_le_add hC' hT
    _ ≤ _ := by
        have k : C * (N : ℝ) ^ 2 * W N ≤ |C| * (N : ℝ) ^ 2 * |W N| :=
          (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
        have a1 := abs_nonneg C; have b1 := abs_nonneg (W N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) hr, mul_nonneg hN2 b1]

/-- The absolute crux implies the signed one.  Proved. -/
theorem deadCharSigned_of_abs {b : ℕ} (hD : DeadCharCancelAbs b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range S, deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
          rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C, W, hW, hC⟩ := hD h hh
  refine ⟨C, W, hW, fun N hN S _ => le_trans ?_ (hC N hN S)⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun m _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun S' hS' => ?_)))
  rw [Finset.mem_range] at hS'
  rw [norm_mul, norm_rhoProd _ (by omega), show 10 * (S' + 1) = 10 * S' + 10 by ring]

/-- **Cassels rate for the resampling law**, from the signed crux.  Proved modulo
`deadCharSigned`. -/
theorem casselsRate_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : CasselsRate resLaw b := by
  intro h hh
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := cassels_Bf hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := deadCharSigned hb h3 h hh
  refine ⟨|C₁| + |C₂| + 1, fun N => |W₁ N| + |W₂ N| + (N : ℝ) ^ (-(1 / 2 : ℝ)),
    (hW₁.abs.add hW₂.abs).add (summable_sched_rpow (by norm_num)), fun N hN => ?_⟩
  set ξ : ℕ → ℕ → ℝ := fun n m => h * ((b : ℝ) ^ n - (b : ℝ) ^ m) with hξ
  have h₂' : ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S → ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ∑ S' ∈ Finset.range S, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S‖ ≤
        C₂ * (N : ℝ) ^ 2 * W₂ N := h₂
  set K : ℝ := ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m|
  set S : ℕ := ⌈K⌉₊ + Nat.log 3 N
  have hK : K ≤ 3 ^ (10 * S) := by
    have h1 : K ≤ (S : ℝ) := (Nat.le_ceil K).trans (by exact_mod_cast Nat.le_add_right _ _)
    have h2 : S < 3 ^ (10 * S) := (Nat.lt_pow_self (by norm_num)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact h1.trans (by exact_mod_cast h2.le)
  have hM : Nat.log 3 N / 2 ≤ 10 * S := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hrN : (1 : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (N : ℝ) ^ (3 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]; exact Real.one_le_rpow hN1 (by norm_num)
  have h3S : (0 : ℝ) < 3 ^ (10 * S) := by positivity
  have hA : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ ≤
      C₁ * (N : ℝ) ^ 2 * W₁ N := by
    refine le_trans (Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_) (h₁ N hN)
    rw [norm_rhoProd _ (Nat.zero_le _), mul_zero, ← tailProd_zero_eq_Bf,
      ← tailProd_mul (ξ n m) (Nat.zero_le _) hM]
    exact mul_le_of_le_one_right (tailProd_nonneg _ _ _) (tailProd_le_one _ _ _)
  have hC : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m| / 3 ^ (10 * S) ≤
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simp only [← Finset.sum_div]
    rw [div_le_iff₀ h3S]
    nlinarith
  have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
    (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
  -- ν̂ = (ν̂ − T_S) + Πρ − Σ deadChar·Πρ
  set ν : ℝ → ℂ := fun x => ∫ ω, ee (x * cpt (resLaw.φ ω)) ∂coinMeasure
  have hsplit : ∀ n m, ν (ξ n m) = (ν (ξ n m) - prefChar (ξ n m) S) + rhoProd (ξ n m) 0 S -
      ∑ S' ∈ Finset.range S, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S := by
    intro n m; rw [prefChar_eq]; ring
  have hsum : ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ν (ξ n m)‖ ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m| / 3 ^ (10 * S) +
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ +
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range S, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S‖ := by
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hsplit n m]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)
    · simp only [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun m _ => norm_fourier_sub_prefChar _ _))
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
  calc _ ≤ _ := secondMoment_le_norm_sum resLaw b h N
    _ ≤ _ := hsum
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + C₁ * (N : ℝ) ^ 2 * W₁ N +
          C₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add (add_le_add hC hA) (h₂' N hN S hM)
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + |C₁| * (N : ℝ) ^ 2 * |W₁ N| +
          |C₂| * (N : ℝ) ^ 2 * |W₂ N| := by linarith [k C₁ (W₁ N), k C₂ (W₂ N)]
    _ ≤ _ := by
        have a1 := abs_nonneg C₁; have a2 := abs_nonneg C₂
        have b1 := abs_nonneg (W₁ N); have b2 := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) b2, mul_nonneg (mul_nonneg a2 hN2) b1,
          mul_nonneg (mul_nonneg a1 hN2) hr, mul_nonneg (mul_nonneg a2 hN2) hr,
          mul_nonneg hN2 b1, mul_nonneg hN2 b2]

/-! ## Known-false sibling: the same descent against base-2 obstacles -/

/-- The child `w ++ u` avoids every dyadic obstacle `B(p/2ⁿ, 2·2^{−n−36})` charged to the stage
with prefix `w` (`3^{|w|−10} ≤ 2ⁿ < 3^{|w|}`). -/
def Alive₂ (w u : List Bool) : Prop :=
  ∀ (n : ℕ) (p : ℤ), (3 : ℝ) ^ w.length ≤ (2 : ℝ) ^ n * 3 ^ 10 → (2 : ℝ) ^ n < 3 ^ w.length →
    ∀ y ∈ cyl (w ++ u), 2 / ((2 : ℝ) ^ n * 2 ^ 36) ≤ |y - p / 2 ^ n|

theorem sep_dyadic {p p' : ℤ} {n m : ℕ} (hne : (p : ℝ) / 2 ^ n ≠ p' / 2 ^ m) :
    1 / (2 : ℝ) ^ (max n m) ≤ |(p : ℝ) / 2 ^ n - p' / 2 ^ m| := by
  set M := max n m
  have hn : (2 : ℝ) ^ M = 2 ^ n * 2 ^ (M - n) := by rw [← pow_add]; congr 1; omega
  have hm : (2 : ℝ) ^ M = 2 ^ m * 2 ^ (M - m) := by rw [← pow_add]; congr 1; omega
  have heq : (p : ℝ) / 2 ^ n - p' / 2 ^ m = ((p * 2 ^ (M - n) - p' * 2 ^ (M - m) : ℤ) : ℝ) / 2 ^ M := by
    push_cast
    rw [sub_div, hn, mul_div_mul_right _ _ (by positivity), ← hn, hm,
      mul_div_mul_right _ _ (by positivity)]
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ M)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hz : p * 2 ^ (M - n) - p' * 2 ^ (M - m) ≠ 0 := by
    intro h; apply hne
    have : (p : ℝ) / 2 ^ n - p' / 2 ^ m = 0 := by rw [heq]; simp [h]
    linarith
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hz

open Classical in
/-- **Dead children against the dyadic obstacles: at most 4 of 1024.** -/
theorem card_dead₂_le (w : List Bool) :
    ((Finset.univ : Finset (Fin 10 → Bool)).filter fun f => ¬ Alive₂ w (List.ofFn f)).card ≤ 4 := by
  classical
  set D := (Finset.univ : Finset (Fin 10 → Bool)).filter fun f => ¬ Alive₂ w (List.ofFn f)
  have hdead : ∀ f : Fin 10 → Bool, ∃ np : ℕ × ℤ, f ∈ D → (
      (3 : ℝ) ^ w.length ≤ (2 : ℝ) ^ np.1 * 3 ^ 10 ∧ (2 : ℝ) ^ np.1 < 3 ^ w.length ∧
      ∃ y ∈ cyl (w ++ List.ofFn f), |y - np.2 / 2 ^ np.1| < 2 / ((2 : ℝ) ^ np.1 * 2 ^ 36)) := by
    intro f
    by_cases hf : f ∈ D
    · have := (Finset.mem_filter.1 hf).2
      unfold Alive₂ at this; push Not at this
      obtain ⟨n, p, h1, h2, y, hy, hlt⟩ := this
      exact ⟨(n, p), fun _ => ⟨h1, h2, y, hy, hlt⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hf⟩
  choose np hnp using hdead
  set L := w.length
  set a := cylLeft w
  set T : ℝ := (3 : ℝ) ^ L with hT
  have hTpos : 0 < T := by positivity
  set ℓ : ℝ := 1 / (T * 3 ^ 10) with hℓ
  set sp : ℝ := 1 / T with hsp
  have hℓpos : 0 < ℓ := by positivity
  have hsppos : 0 < sp := by positivity
  set v : (Fin 10 → Bool) → ℝ := fun f => ((np f).2 : ℝ) / 2 ^ (np f).1 with hv
  have hrad : ∀ f ∈ D, 2 / ((2 : ℝ) ^ (np f).1 * 2 ^ 36) ≤ ℓ / 6 := by
    intro f hf
    obtain ⟨h1, -, -⟩ := hnp f hf
    have h2n : (0 : ℝ) < 2 ^ (np f).1 := by positivity
    rw [hℓ, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hchild : ∀ f, cyl (w ++ List.ofFn f) = Set.Icc (a + (J f : ℝ) * ℓ) (a + (J f : ℝ) * ℓ + ℓ) := by
    intro f
    unfold cyl
    rw [cylLeft_child, List.length_append, List.length_ofFn, pow_add, ← hT]
  have hnear : ∀ f ∈ D, ∃ y ∈ Set.Icc (a + (J f : ℝ) * ℓ) (a + (J f : ℝ) * ℓ + ℓ),
      y ∈ Set.Icc (v f - ℓ / 6) (v f + ℓ / 6) := by
    intro f hf
    obtain ⟨-, -, y, hy, hlt⟩ := hnp f hf
    rw [hchild] at hy
    have := (hlt.trans_le (hrad f hf)).le
    rw [abs_le] at this
    exact ⟨y, hy, ⟨by simp only [hv]; linarith [this.1, this.2], by simp only [hv]; linarith [this.1, this.2]⟩⟩
  have hrange : ∀ f ∈ D, (v f - (a - ℓ / 6)) / sp < (2 : ℕ) := by
    intro f hf
    obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := hnear f hf
    have hJ : (J f : ℝ) + 1 ≤ 3 ^ 10 := by
      have := J_lt f; exact_mod_cast (by omega : J f + 1 ≤ 3 ^ 10)
    have hℓT : (3 : ℝ) ^ 10 * ℓ = 1 / T := by rw [hℓ]; field_simp
    have hup : v f - (a - ℓ / 6) ≤ 1 / T + ℓ / 3 := by
      have : (J f : ℝ) * ℓ + ℓ ≤ 3 ^ 10 * ℓ := by nlinarith
      linarith
    rw [div_lt_iff₀ hsppos]
    have : 1 / T + ℓ / 3 < 2 * sp := by
      rw [hℓ, hsp]; field_simp; norm_num
    push_cast; linarith
  have hsep : ∀ f ∈ D, ∀ g ∈ D, v f ≠ v g → sp ≤ |v f - v g| := by
    intro f hf g hg hne
    have h := sep_dyadic hne
    have hM : (2 : ℝ) ^ (max (np f).1 (np g).1) < T := by
      rcases le_total (np f).1 (np g).1 with hle | hle
      · rw [max_eq_right hle]; exact (hnp g hg).2.1
      · rw [max_eq_left hle]; exact (hnp f hf).2.1
    have : sp ≤ 1 / (2 : ℝ) ^ (max (np f).1 (np g).1) := by
      rw [hsp]; exact one_div_le_one_div_of_le (by positivity) hM.le
    simp only [hv]; linarith
  exact card_le_of_buckets a ℓ sp hℓpos hsppos 2 D v hnear hrange hsep

open Classical in
/-- Generic selector: keep an alive block, else some alive block. -/
noncomputable def selG (A : List Bool → List Bool → Prop) (R : ℕ) (w u : List Bool) : List Bool :=
  if A w u then u else if h : ∃ v : List Bool, v.length = R ∧ A w v then h.choose else u

/-- Generic descent prefix. -/
noncomputable def buildG (A : List Bool → List Bool → Prop) (R : ℕ) : ℕ → (ℕ → Bool) → List Bool
  | 0, _ => []
  | s + 1, ω => buildG A R s ω ++ selG A R (buildG A R s ω) (List.ofFn fun i : Fin R => ω (R * s + i))

/-- Generic descent selector sequence. -/
noncomputable def descentG (A : List Bool → List Bool → Prop) (R : ℕ) (ω : ℕ → Bool) (i : ℕ) : Bool :=
  (buildG A R (i + 1) ω).getD i false

theorem length_buildG (A : List Bool → List Bool → Prop) (R : ℕ) (ω : ℕ → Bool) (s : ℕ) :
    (buildG A R s ω).length = R * s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have : ∀ w u : List Bool, u.length = R → (selG A R w u).length = R := by
      intro w u hu; unfold selG; split_ifs with h1 h2
      · exact hu
      · exact h2.choose_spec.1
      · exact hu
    simp [buildG, ih, this, List.length_ofFn]; ring

theorem buildG_prefix (A : List Bool → List Bool → Prop) (R : ℕ) (ω : ℕ → Bool) {s t : ℕ}
    (h : s ≤ t) : buildG A R s ω <+: buildG A R t ω := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (List.prefix_append _ _)

theorem ofFn_descentG (A : List Bool → List Bool → Prop) {R : ℕ} (hR : 0 < R) (ω : ℕ → Bool) (s : ℕ) :
    (List.ofFn fun i : Fin (R * s) => descentG A R ω i) = buildG A R s ω := by
  have key : ∀ {i a b : ℕ}, a ≤ b → i < R * a →
      (buildG A R a ω).getD i false = (buildG A R b ω).getD i false := by
    intro i a b hab hia
    obtain ⟨l, hl⟩ := buildG_prefix A R ω hab
    rw [← hl, List.getD_append _ _ _ _ (by rw [length_buildG]; exact hia)]
  apply List.ext_getElem
  · simp [length_buildG]
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    have hi : i < R * s := by simpa using h1
    have h1' : i < R * (i + 1) := by nlinarith
    unfold descentG
    rw [key (le_max_left (i+1) s) h1', ← key (le_max_right (i+1) s) hi,
      List.getD_eq_getElem _ _ h2]

section MeasG
local instance : MeasurableSpace (List Bool) := ⊤
local instance : MeasurableSingletonClass (List Bool) := ⟨fun _ => trivial⟩

theorem measurable_descentG (A : List Bool → List Bool → Prop) (R : ℕ) : Measurable (descentG A R) := by
  have hb : ∀ s, Measurable (buildG A R s) := by
    intro s
    induction s with
    | zero => exact measurable_const
    | succ s ih =>
      have hb : Measurable fun ω : ℕ → Bool => (fun i : Fin R => ω (R * s + i)) :=
        measurable_pi_lambda _ fun i => measurable_pi_apply _
      have hg : Measurable fun x : List Bool × (Fin R → Bool) =>
          x.1 ++ selG A R x.1 (List.ofFn x.2) := measurable_of_countable _
      exact hg.comp (ih.prodMk hb)
  refine measurable_pi_lambda _ fun i => ?_
  exact (measurable_from_top (f := fun l : List Bool => l.getD i false)).comp (hb (i + 1))
end MeasG

theorem exists_alive₂ (w : List Bool) : ∃ u : List Bool, u.length = 10 ∧ Alive₂ w u := by
  classical
  by_contra hcon
  push Not at hcon
  have h := card_dead₂_le w
  rw [Finset.filter_true_of_mem fun f _ => hcon (List.ofFn f) (by simp)] at h
  simp at h

/-- **The sibling's points avoid every dyadic obstacle**: `2^{−36} < ‖2ⁿ x‖`. -/
theorem descent₂_dnear (ω : ℕ → Bool) (n : ℕ) :
    (2 : ℝ) ^ (-(36 : ℝ)) < UniformBad.dnear ((2 : ℝ) ^ n * cpt (descentG Alive₂ 10 ω)) := by
  set x := cpt (descentG Alive₂ 10 ω)
  set s := Nat.log 3 (2 ^ n) / 10
  have hne : 2 ^ n ≠ 0 := by positivity
  have hlo : 3 ^ (10 * s) ≤ 2 ^ n :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le _ _)) (Nat.pow_log_le_self 3 hne)
  have hhi : 2 ^ n < 3 ^ (10 * (s + 1)) :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmem := cpt_mem_cyl (descentG Alive₂ 10 ω) (10 * (s + 1 + 1))
  rw [ofFn_descentG Alive₂ (by norm_num)] at hmem
  -- the stage `s + 1` block is alive
  have hal : Alive₂ (buildG Alive₂ 10 (s + 1) ω)
      (selG Alive₂ 10 (buildG Alive₂ 10 (s + 1) ω)
        (List.ofFn fun i : Fin 10 => ω (10 * (s + 1) + i))) := by
    unfold selG; split_ifs with h1 h2
    · exact h1
    · exact h2.choose_spec.2
    · exact absurd (exists_alive₂ _) h2
  have hlen := length_buildG Alive₂ 10 ω (s + 1)
  set p : ℤ := round ((2 : ℝ) ^ n * x)
  have key := hal n p (by
      rw [hlen, show 10 * (s + 1) = 10 * s + 10 by ring, pow_add]
      gcongr; exact_mod_cast hlo)
    (by rw [hlen]; exact_mod_cast hhi) x hmem
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hd : UniformBad.dnear ((2 : ℝ) ^ n * x) = (2 : ℝ) ^ n * |x - p / 2 ^ n| := by
    unfold UniformBad.dnear
    rw [← abs_of_pos h2n, ← abs_mul, abs_of_pos h2n]
    congr 1; rw [mul_sub, mul_div_cancel₀ _ h2n.ne']
  rw [hd]
  have : (2 : ℝ) ^ (-(36 : ℝ)) = 1 / 2 ^ 36 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  rw [this]
  calc 1 / (2 : ℝ) ^ 36 < 2 / 2 ^ 36 := by norm_num
    _ = (2 : ℝ) ^ n * (2 / ((2 : ℝ) ^ n * 2 ^ 36)) := by field_simp
    _ ≤ _ := by gcongr


open Classical in
/-- **Refuted: per-stage dead counts do not give normality.**  The same descent run against the
dyadic obstacles `B(p/2ⁿ, 2·2^{−n−36})` kills at most 4 of the 1024 children at every stage
(fewer than `descentLaw`'s 488, `card_dead_le`), yet every point it produces lies in `K` and is
normal to the base 2, prime to 3, for no coin sequence.  So the crux `fourierPairRate_resLaw`
cannot follow from per-stage closeness to the product measure; it must use the arithmetic of
the centres `p/q`. -/
theorem perStage_deadCount_not_enough :
    (∀ w : List Bool, ((Finset.univ : Finset (Fin 10 → Bool)).filter
        fun f => ¬ Alive₂ w (List.ofFn f)).card ≤ 4) ∧
      ∀ ω, cpt (descentG Alive₂ 10 ω) ∈ cantorSet ∧ ¬ IsNormal 2 (cpt (descentG Alive₂ 10 ω)) :=
  ⟨card_dead₂_le, fun ω => ⟨cpt_mem_cantorSet _,
    UniformBad.not_isNormal_of_uniformBad (c := 36) le_rfl (fun n => descent₂_dnear ω n)⟩⟩

/-! ## Closed route: a `×3`-invariant measure on `K ∩ Bad`

Hochman–Shmerkin / Host (`EntropyProfiles.Literature.HochmanShmerkinTimesP`) would give
normality to every base `≁ 3` for a `×3`-ergodic measure of positive dimension.  Such a measure
gives `Bad` zero mass (`Literature.EFSTimesThreeNotBad`), so the route cannot reach `K ∩ Bad`:
the measure on `K ∩ Bad` must be non-invariant, as `descentLaw` is. -/

namespace Literature

/-- **Cited: Einsiedler–Fishman–Shapira**, *Diophantine approximations on fractals*, GAFA 21
(2011), arXiv 0908.2350.  The abstract states the case of the Cantor measure (almost every point
of `K` has every finite pattern in its continued fraction, so is not badly approximable); the
transcription here is the general `×3`-invariant ergodic positive-dimension form, which we
believe is in the paper's main theorem (confidence 75%; the theorem number is unchecked, and the
step needing an expert check is whether positive dimension, not the Cantor measure, suffices).
Faithful-or-weaker in the hypothesis: a Frostman bound replaces positive dimension. -/
def EFSTimesThreeNotBad : Prop :=
  ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Ico 0 1)ᶜ = 0 →
    Ergodic (EntropyProfiles.timesMap 3) μ →
    (∃ C δ : ℝ, 0 < δ ∧ ∀ x r : ℝ, 0 < r → μ (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r ^ δ)) →
      μ Bad = 0

end Literature

/-- **The `×3`-invariant route is closed.**  Proved from the cited EFS: no `×3`-ergodic
Frostman probability measure on `[0,1)` is carried by `Bad`. -/
theorem not_exists_timesThree_law_on_bad (hEFS : Literature.EFSTimesThreeNotBad) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Ico 0 1)ᶜ = 0 ∧
      Ergodic (EntropyProfiles.timesMap 3) μ ∧
      (∃ C δ : ℝ, 0 < δ ∧ ∀ x r : ℝ, 0 < r → μ (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r ^ δ)) ∧
      μ Badᶜ = 0 := by
  rintro ⟨μ, hP, h01, herg, hF, hB⟩
  have h0 := hEFS μ hP h01 herg hF
  have : μ (Bad ∪ Badᶜ) = 0 := le_antisymm ((measure_union_le _ _).trans (by simp [h0, hB])) bot_le
  simp at this

/-! ## The local route (lap 6): almost-sure normality from local dead biases

`midStages` asks for a Cassels *rate* for `resLaw`.  Every stage-by-stage bound of it multiplies
the dead correction at depth `10S'` by the Cantor-tail character `rhoProd ξ (S' + 1) S`, whose
modulus `tailProd ξ (10S' + 10) (10S)` (`norm_rhoProd`) lives on the ternary digits of
`ξ = h(bⁿ − bᵐ)` above position `10S'`: the middle and leading digits of `bⁿ`.  With a rate, that
needs quantitative equidistribution of `n log₃ b` (Baker-type input), on top of the arithmetic
decorrelation of the dead events.

The local route needs no rate.  Condition the `n`-th Weyl term on the stage prefix `C` ternary
digits above the scale of `bⁿ` (`stageOf`) and split
`e(hbⁿx) = (e(hbⁿx) − condChar) + localBias + contChar`.
* The first part is an approximate martingale-difference array: its partial sums have second
  moment `O(N)`, so its Cesàro means vanish almost surely (`ae_cesaro_condDiff`).
* `contChar` has modulus `|μ̂_K(h 3^{C + u_n})| ≤ Π_{k<C} |cos(2π h 3^{u_n + k})|`, where
  `u_n = 10 frac((n log₃ b − C)/10)`.  Weyl equidistribution of `n log₃ b / 10` and
  `∫₀¹ Π_{k<C} cos²(2π 3^k y) dy = 2^{−C}` make its Cesàro mean small for large `C`
  (`cesaro_contChar_small`).  Only irrationality of `log₃ b` is used.
* The middle part, `localBias`, is the dead correction.  By the uniformity of the resampled block
  (`buildU_succ_uniform`) only the dead children of the stages near the scale of `bⁿ` appear in
  it.  The crux is now that its Cesàro means vanish (`LocalDeadBias`, `localDeadBias_resLaw`). -/

/-- The conditioning stage of the `n`-th Weyl term: `C` ternary digits above the scale
`3^{⌊log₃ bⁿ⌋}` of `bⁿ`, rounded down to a whole stage. -/
def stageOf (b C n : ℕ) : ℕ := (Nat.log 3 (b ^ n) - C) / 10

/-- The conditional character of `resLaw` at frequency `ξ`, given the stage-`s` prefix `w`
(`0` on a null prefix). -/
noncomputable def condChar (ξ : ℝ) (s : ℕ) (w : List Bool) : ℂ :=
  (∫ ω in {ω | buildU s ω = w}, ee (ξ * cpt (descentU ω)) ∂coinMeasure) /
    ((coinMeasure.real {ω | buildU s ω = w} : ℝ) : ℂ)

/-- The character of the Cantor continuation of the prefix `w`:
`e(ξ cylLeft w) · μ̂_K(ξ / 3^{|w|})`. -/
noncomputable def contChar (ξ : ℝ) (w : List Bool) : ℂ :=
  ee (ξ * cylLeft w) * muK (ξ / 3 ^ w.length)

/-- The local dead bias of the `n`-th Weyl term: conditional character of `resLaw` minus that
of the Cantor continuation, given the prefix at `stageOf b C n`. -/
noncomputable def localBias (b C : ℕ) (h : ℤ) (n : ℕ) (ω : ℕ → Bool) : ℂ :=
  condChar (h * (b : ℝ) ^ n) (stageOf b C n) (buildU (stageOf b C n) ω) -
    contChar (h * (b : ℝ) ^ n) (buildU (stageOf b C n) ω)

/-- **Conjecture node: the local dead biases of `resLaw` average out.**  Believed 75% for
`3 ∤ b`.  For each nonzero `h` and conditioning depth `C`, the Cesàro means of
`localBias b C h n ω` vanish for almost every coin sequence.

What it says.  Given the prefix at `stageOf b C n`, the conditional character of `e(hbⁿx)` under
`resLaw` differs from the Cantor continuation's only through the dead children of the later
stages, each weighted `1/|A(w)|` (uniform resampling, `alive_avg`, `prefChar_succ`).  Stages far
above the scale of `bⁿ` contribute at most `2π|h|bⁿ3^{−10s}` (`norm_deadErr_le`), and those far
below it are damped by the Cantor tail.  So `localBias` is the excess character of the dead
children near the scale of `bⁿ`.  The dead children at depth `L` are the ones near rationals
`p/q` with `q² ≈ 3^L`, and their excess at `bⁿ ≈ 3^L` is about `e(hbⁿ p/q)`.  So the node is an
equidistribution statement for the phases `bⁿ p/q` of the obstacle rationals met along the path:
asymptotic independence of the `×b` orbit from the Farey (geodesic) structure near `K`.  Under an
arbitrary replacement rule the replacement's own character would enter `localBias`; that is how
`AdversarialReplacement` steers, and why the node is stated for `resLaw` only.

Strength.  With `ae_cesaro_condDiff` and `cesaro_contChar_small`, almost-sure normality of
`resLaw` in base `b` is equivalent to this node with `→ 0` weakened to `limsup ≤ ε(C)`,
`ε(C) → 0`.  So the node is the problem, isolated in local form, and carries no rate (unlike
`midStages`).  It fails for the dyadic sibling (`perStage_deadCount_not_enough`): there every
dead child sits on a binary zero run, so the excess has a coherent phase.

Evidence (`scripts/cantorbad_localbias.py`, 2026-10-06).  Along 6000 `resLaw` paths of 30
stages (depth 300), for each dead child `f` at stage `s ≥ 4` the probe records the excess
`Z_f = Σ_{n ∈ window} (⟨e(bⁿx)⟩_{wf} − ⟨e(bⁿx)⟩_w)`, window `3^L ≤ b^{n+2}`, `bⁿ < 3^{L+15}`,
`⟨·⟩_v` the Cantor-continuation average.  About 200,000 dead children per base:
`|mean Z| / mean |Z| ≤ 0.009` for `b = 2, 5, 7`, every mean within about `1σ` of `0`
(`σ ≈ 0.018, 0.012, 0.011`, against `mean |Z| ≈ 3.5, 2.3, 2.1`).  The past Weyl sum is not
inflated on dead stages: `E[|D| |A|²/n₀] / (E|D| · E[|A|²/n₀]) = 1.00 ± 0.01`, and `Re(Ā Z)` has
coherence below `0.008`.  The control (Cantor paths, same dead sets, no rejection) gives the
same.  Known-biased control (`dyad2`: kill the child containing a dyadic `p/2^m`,
`m = ⌊(L + 5) log₂ 3⌋`): `mean Z = 7.36 ± 0.01`, coherence `0.96`.  So the probe sees a
coherent dead bias when one is present, and sees none for `resLaw`. -/
def LocalDeadBias (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∀ᵐ ω ∂coinMeasure,
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, localBias b C h n ω) / (N : ℂ)) atTop (𝓝 0)


/-! ### The moment reduction of the local route

Every almost-sure Cesàro statement below comes from one generic lemma
(`ae_cesaro_of_secondMoment`): a bounded array whose partial sums have second moment
`O(N² W(N))`, with `W` summable along `sched`, has vanishing Cesàro means almost surely. -/

/-- **Second moment with a rate ⇒ almost-sure Cesàro convergence.**  Proved (DEL along `sched`;
the generic form of `ae_isNormal_of_secondMoment`). -/
theorem ae_cesaro_of_secondMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℂ) (hYm : ∀ n, Measurable (Y n))
    (hYb : ∀ n ω, ‖Y n ω‖ ≤ 1) (K : ℝ) (W : ℕ → ℝ) (hW : Summable fun j => W (sched j))
    (hmom : ∀ N : ℕ, 1 ≤ N → ∫ ω, ‖∑ k ∈ Finset.range N, Y k ω‖ ^ 2 ∂μ ≤ K * (N : ℝ) ^ 2 * W N) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, Y k ω) / (N : ℂ)) atTop (𝓝 0) := by
  set S : ℕ → Ω → ℂ := fun N ω => ∑ k ∈ Finset.range N, Y k ω with hSdef
  have hSm : ∀ N, Measurable (S N) := fun N => Finset.measurable_sum _ fun k _ => hYm k
  have hSb : ∀ N ω, ‖S N ω‖ ≤ N := fun N ω =>
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hYb k ω).trans (by simp))
  set f : ℕ → Ω → ℝ := fun j ω => ‖S (sched j) ω‖ ^ 2 / ((sched j : ℝ)) ^ 2 with hfdef
  have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by positivity
  have hfm : ∀ j, Measurable (f j) := fun j => (((hSm _).norm.pow_const 2).div_const _)
  have hfi : ∀ j, Integrable (f j) μ := fun j =>
    Integrable.of_bound (hfm j).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hf0 j ω)]
      have hpos' : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hSb _ ω) 2)
  have hfI : ∀ j, ∫ ω, f j ω ∂μ ≤ K * W (sched j) := by
    intro j
    have hpos' : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
    simp only [f, S]; rw [integral_div, div_le_iff₀ (by positivity)]
    calc _ ≤ _ := hmom (sched j) (one_le_sched j)
      _ = _ := by ring
  have hs : Summable fun j => ∫ ω, f j ω ∂μ :=
    (hW.mul_left K).of_nonneg_of_le (fun j => integral_nonneg (hf0 j)) hfI
  have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, ∫ ω, f j ω ∂μ)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hf0 j)) hs]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
  have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
    (hfm j).ennreal_ofReal.aemeasurable) hlin
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun j => ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun j => f j ω) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
  have h3 : Tendsto (fun j : ℕ => ‖S (sched j) ω‖ / (sched j : ℝ)) atTop (𝓝 0) := by
    have := h2.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun j => ?_
    simp only [hfdef]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)]
  exact tendsto_of_tendsto_sched (fun k => Y k ω) (fun k => hYb k ω) sched sched_strictMono
    sched_ratio h3

/-- The bounded form: summands of norm at most `B`. -/
theorem ae_cesaro_of_secondMoment_bdd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℂ) (hYm : ∀ n, Measurable (Y n)) {B : ℝ} (hB : 0 < B)
    (hYb : ∀ n ω, ‖Y n ω‖ ≤ B) (K : ℝ) (W : ℕ → ℝ) (hW : Summable fun j => W (sched j))
    (hmom : ∀ N : ℕ, 1 ≤ N → ∫ ω, ‖∑ k ∈ Finset.range N, Y k ω‖ ^ 2 ∂μ ≤ K * (N : ℝ) ^ 2 * W N) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, Y k ω) / (N : ℂ)) atTop (𝓝 0) := by
  have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have key := ae_cesaro_of_secondMoment μ (fun n ω => Y n ω / B)
    (fun n => (hYm n).div_const _) (fun n ω => by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hB.le, div_le_one hB]; exact hYb n ω)
    (K / B ^ 2) W hW (fun N hN => by
      have : ∀ ω, ‖∑ k ∈ Finset.range N, Y k ω / (B : ℂ)‖ ^ 2 =
          ‖∑ k ∈ Finset.range N, Y k ω‖ ^ 2 / B ^ 2 := by
        intro ω
        rw [← Finset.sum_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hB.le, div_pow]
      simp_rw [this]; rw [integral_div]
      calc _ ≤ K * (N : ℝ) ^ 2 * W N / B ^ 2 := by gcongr; exact hmom N hN
        _ = _ := by ring)
  filter_upwards [key] with ω hω
  have := hω.const_mul (B : ℂ)
  rw [mul_zero] at this
  refine this.congr fun N => ?_
  rw [← Finset.sum_div]; field_simp

theorem norm_contChar (ξ : ℝ) (w : List Bool) : ‖contChar ξ w‖ = ‖muK (ξ / 3 ^ w.length)‖ := by
  rw [contChar, norm_mul, norm_ee, one_mul]

theorem norm_muK_le (ξ : ℝ) : ‖muK ξ‖ ≤ 1 := by
  unfold muK
  simpa using norm_integral_le_of_norm_le_const (μ := coinMeasure)
    (Eventually.of_forall fun ω => (norm_ee (ξ * cpt ω)).le)

theorem norm_condChar_le (ξ : ℝ) (s : ℕ) (w : List Bool) : ‖condChar ξ s w‖ ≤ 1 := by
  unfold condChar
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := coinMeasure) (s := {ω | buildU s ω = w}))
    with h0 | hpos
  · rw [← h0, div_zero]; exact zero_le_one
  · rw [div_le_one hpos]
    simpa using norm_setIntegral_le_of_norm_le_const_ae (μ := coinMeasure)
      (s := {ω | buildU s ω = w}) (f := fun ω => ee (ξ * cpt (descentU ω))) (C := 1)
      (measure_lt_top _ _) (Eventually.of_forall fun ω => (norm_ee _).le)

theorem norm_localBias_le (b C : ℕ) (h : ℤ) (n : ℕ) (ω : ℕ → Bool) : ‖localBias b C h n ω‖ ≤ 2 := by
  unfold localBias
  refine (norm_sub_le _ _).trans ?_
  have := norm_condChar_le (h * (b : ℝ) ^ n) (stageOf b C n) (buildU (stageOf b C n) ω)
  rw [norm_contChar]
  have := norm_muK_le (h * (b : ℝ) ^ n / 3 ^ (buildU (stageOf b C n) ω).length)
  linarith

section MeasLB
local instance : MeasurableSpace (List Bool) := ⊤

theorem measurable_localBias (b C : ℕ) (h : ℤ) (n : ℕ) : Measurable (localBias b C h n) :=
  (measurable_from_top (f := fun w : List Bool => condChar (h * (b : ℝ) ^ n) (stageOf b C n) w -
    contChar (h * (b : ℝ) ^ n) w)).comp (measurable_buildU _)

theorem measurable_condDiff (b C : ℕ) (h : ℤ) (n : ℕ) : Measurable fun ω : ℕ → Bool =>
    ee (h * (b : ℝ) ^ n * cpt (descentU ω)) -
      condChar (h * (b : ℝ) ^ n) (stageOf b C n) (buildU (stageOf b C n) ω) :=
  (measurable_ee.comp ((measurable_cpt.comp measurable_descentU).const_mul _)).sub
    ((measurable_from_top (f := fun w : List Bool => condChar (h * (b : ℝ) ^ n) (stageOf b C n) w)).comp
      (measurable_buildU _))
end MeasLB

/-- **Moment node for the crux.**  The partial sums of the local biases have second moment
`O(N² W(N))` with `W` summable along `sched`.  Implies `LocalDeadBias b`
(`localDeadBias_of_rate`).  This is the only known mechanism for the a.s. node: expand
`Σ_{n,m} E[B_n conj B_m]`; the diagonal is `≤ 4N`, and for `n < m`,
`E[B_n conj B_m] = E[B_n conj E[B_m | w_{s_n}]]`, so the node follows from decay of the
conditional mean of the stage-`s_m` bias given an earlier prefix (mixing of the dead
configuration along the resampled path). -/
def LocalBiasRate (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N → ∫ ω, ‖∑ n ∈ Finset.range N, localBias b C h n ω‖ ^ 2 ∂coinMeasure ≤
      K * (N : ℝ) ^ 2 * W N

/-- **Moment node ⇒ a.s. node.**  Proved. -/
theorem localDeadBias_of_rate {b : ℕ} (hR : LocalBiasRate b) : LocalDeadBias b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hR h hh C
  exact ae_cesaro_of_secondMoment_bdd coinMeasure (fun n => localBias b C h n)
    (measurable_localBias b C h) (by norm_num) (norm_localBias_le b C h) K W hW hK

/-! ### The martingale part: orthogonality on the stage atoms -/

/-- The `n`-th approximate martingale difference. -/
noncomputable def condDiff (b C : ℕ) (h : ℤ) (n : ℕ) (ω : ℕ → Bool) : ℂ :=
  ee (h * (b : ℝ) ^ n * cpt (descentU ω)) -
    condChar (h * (b : ℝ) ^ n) (stageOf b C n) (buildU (stageOf b C n) ω)

theorem integrable_of_bdd {E : Type*} [NormedAddCommGroup E] {F : (ℕ → Bool) → E}
    (hm : AEStronglyMeasurable F coinMeasure) (B : ℝ) (hB : ∀ ω, ‖F ω‖ ≤ B) :
    Integrable F coinMeasure :=
  Integrable.of_bound hm B (Eventually.of_forall hB)

section MeasLB2
local instance : MeasurableSpace (List Bool) := ⊤

theorem measurable_comp_buildU (S : ℕ) (G : List Bool → ℂ) :
    Measurable fun ω => G (buildU S ω) :=
  (measurable_from_top (f := G)).comp (measurable_buildU S)
end MeasLB2

theorem measurable_ee_descentU (ξ : ℝ) : Measurable fun ω => ee (ξ * cpt (descentU ω)) :=
  measurable_ee.comp ((measurable_cpt.comp measurable_descentU).const_mul _)

theorem norm_comp_buildU_le (S : ℕ) (G : List Bool → ℂ) (ω : ℕ → Bool) :
    ‖G (buildU S ω)‖ ≤ ∑ w ∈ LS S, ‖G w‖ :=
  Finset.single_le_sum (f := fun w => ‖G w‖) (fun _ _ => norm_nonneg _) (buildU_mem_LS ω S)

theorem integral_eq_sum_atoms (S : ℕ) (F : (ℕ → Bool) → ℂ) (hF : Integrable F coinMeasure) :
    ∫ ω, F ω ∂coinMeasure = ∑ w ∈ LS S, ∫ ω in {ω | buildU S ω = w}, F ω ∂coinMeasure := by
  have hpt : F = fun ω => ∑ w ∈ LS S, {ω | buildU S ω = w}.indicator F ω := by
    funext ω
    rw [Finset.sum_eq_single (buildU S ω)]
    · simp [Set.indicator]
    · intro w _ hw; simp [Set.indicator, Ne.symm hw]
    · intro h; exact absurd (buildU_mem_LS ω S) h
  conv_lhs => rw [hpt]
  rw [integral_finset_sum _ fun w _ => hF.indicator (mset_buildU' S w)]
  exact Finset.sum_congr rfl fun w _ => integral_indicator (mset_buildU' S w)

theorem condChar_mul (ξ : ℝ) (s : ℕ) (w : List Bool) :
    (coinMeasure.real {ω | buildU s ω = w} : ℂ) * condChar ξ s w =
      ∫ ω in {ω | buildU s ω = w}, ee (ξ * cpt (descentU ω)) ∂coinMeasure := by
  unfold condChar
  rcases eq_or_ne (coinMeasure.real {ω | buildU s ω = w}) 0 with h0 | h0
  · rw [h0]
    have : coinMeasure {ω | buildU s ω = w} = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0
    rw [Measure.restrict_eq_zero.2 this, integral_zero_measure]; simp
  · have : ((coinMeasure.real {ω | buildU s ω = w} : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
    field_simp

/-- **Orthogonality**: the difference `e(ξx) − condChar` is orthogonal to every function of the
stage-`S` prefix. -/
theorem integral_orth (S : ℕ) (ξ : ℝ) (G : List Bool → ℂ) :
    ∫ ω, G (buildU S ω) * (starRingEnd ℂ) (ee (ξ * cpt (descentU ω)) -
      condChar ξ S (buildU S ω)) ∂coinMeasure = 0 := by
  have hie : Integrable (fun ω => ee (ξ * cpt (descentU ω))) coinMeasure :=
    integrable_of_bdd (measurable_ee_descentU ξ).aestronglyMeasurable 1 fun ω => (norm_ee _).le
  have hint : Integrable (fun ω => G (buildU S ω) * (starRingEnd ℂ) (ee (ξ * cpt (descentU ω)) -
      condChar ξ S (buildU S ω))) coinMeasure := by
    refine integrable_of_bdd (((measurable_comp_buildU S G).mul
      (Complex.continuous_conj.measurable.comp ((measurable_ee_descentU ξ).sub
        (measurable_comp_buildU S (condChar ξ S))))).aestronglyMeasurable)
      ((∑ w ∈ LS S, ‖G w‖) * 2) fun ω => ?_
    rw [norm_mul, Complex.norm_conj]
    gcongr
    · exact norm_comp_buildU_le S G ω
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_ee]; linarith [norm_condChar_le ξ S (buildU S ω)]
  rw [integral_eq_sum_atoms S _ hint]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [setIntegral_congr_fun (mset_buildU' S w)
    (g := fun ω => G w * (starRingEnd ℂ) (ee (ξ * cpt (descentU ω)) - condChar ξ S w))
    (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [hω])]
  rw [integral_const_mul, integral_conj, integral_sub hie.integrableOn (integrable_const _),
    setIntegral_const, ← condChar_mul]
  simp

theorem stageOf_mono (b C : ℕ) (hb : 1 ≤ b) {n m : ℕ} (h : n ≤ m) : stageOf b C n ≤ stageOf b C m := by
  unfold stageOf
  have : Nat.log 3 (b ^ n) ≤ Nat.log 3 (b ^ m) :=
    Nat.log_mono_right (Nat.pow_le_pow_right hb h)
  exact Nat.div_le_div_right (by omega)

theorem pow_le_stage (b C m : ℕ) (hb : 1 ≤ b) :
    (b : ℝ) ^ m ≤ 3 ^ (C + 10) * 3 ^ (10 * stageOf b C m) := by
  have hne : b ^ m ≠ 0 := by positivity
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) (b ^ m)
  have h2 : Nat.log 3 (b ^ m) + 1 ≤ C + 10 + 10 * stageOf b C m := by unfold stageOf; omega
  have : b ^ m ≤ 3 ^ (C + 10) * 3 ^ (10 * stageOf b C m) := by
    rw [← pow_add]; exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) h2)
  exact_mod_cast this

theorem norm_condDiff_le (b C : ℕ) (h : ℤ) (n : ℕ) (ω : ℕ → Bool) : ‖condDiff b C h n ω‖ ≤ 2 := by
  unfold condDiff
  refine (norm_sub_le _ _).trans ?_
  rw [norm_ee]; linarith [norm_condChar_le (h * (b : ℝ) ^ n) (stageOf b C n)
    (buildU (stageOf b C n) ω)]

theorem abs_cpt_sub_cylLeft (ω : ℕ → Bool) (S : ℕ) :
    |cpt (descentU ω) - cylLeft (buildU S ω)| ≤ 1 / 3 ^ (10 * S) := by
  have hmem := cpt_mem_cyl (descentU ω) (10 * S)
  rw [ofFn_descentU] at hmem
  have hl := length_buildU ω S
  unfold cyl at hmem
  rw [hl] at hmem
  rw [abs_le]; constructor <;> [skip; skip] <;> nlinarith [hmem.1, hmem.2,
    (by positivity : (0 : ℝ) < 1 / 3 ^ (10 * S))]

/-- **Cross terms decay geometrically.** -/
theorem norm_integral_cross {b : ℕ} (hb : 2 ≤ b) (h : ℤ) (C : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    ‖∫ ω, condDiff b C h n ω * (starRingEnd ℂ) (condDiff b C h m ω) ∂coinMeasure‖ ≤
      4 * Real.pi * |(h : ℝ)| * 3 ^ (C + 10) * ((b : ℝ) ^ n / (b : ℝ) ^ m) := by
  set s := stageOf b C m
  set sn := stageOf b C n
  set ξ : ℝ := h * (b : ℝ) ^ n
  have hs : sn ≤ s := stageOf_mono b C (by omega) hnm
  set G : List Bool → ℂ := fun w => ee (ξ * cylLeft w) - condChar ξ sn (w.take (10 * sn))
  set R : (ℕ → Bool) → ℂ := fun ω => ee (ξ * cpt (descentU ω)) - ee (ξ * cylLeft (buildU s ω))
  have htake : ∀ ω, (buildU s ω).take (10 * sn) = buildU sn ω := by
    intro ω
    have := List.prefix_iff_eq_take.1 (buildU_prefix ω hs)
    rw [length_buildU] at this; exact this.symm
  have hsplit : ∀ ω, condDiff b C h n ω = G (buildU s ω) + R ω := by
    intro ω; simp only [condDiff, G, R, htake, ξ, sn]; ring
  have hYm : ∀ k, Measurable (condDiff b C h k) := measurable_condDiff b C h
  have hRm : Measurable R := (measurable_ee_descentU ξ).sub
    (measurable_comp_buildU s fun w => ee (ξ * cylLeft w))
  have hcm : Measurable fun ω => (starRingEnd ℂ) (condDiff b C h m ω) :=
    Complex.continuous_conj.measurable.comp (hYm m)
  have hRb : ∀ ω, ‖R ω‖ ≤ 2 * Real.pi * |ξ| * (1 / 3 ^ (10 * s)) := by
    intro ω
    refine (norm_ee_sub_ee _ _).trans ?_
    rw [← mul_sub, abs_mul, ← mul_assoc]
    gcongr
    exact abs_cpt_sub_cylLeft ω s
  have hGi : Integrable (fun ω => G (buildU s ω) * (starRingEnd ℂ) (condDiff b C h m ω))
      coinMeasure :=
    integrable_of_bdd ((measurable_comp_buildU s G).mul hcm).aestronglyMeasurable
      ((∑ w ∈ LS s, ‖G w‖) * 2) fun ω => by
        rw [norm_mul, Complex.norm_conj]
        gcongr
        · exact norm_comp_buildU_le s G ω
        · exact norm_condDiff_le b C h m ω
  have hRi : Integrable (fun ω => R ω * (starRingEnd ℂ) (condDiff b C h m ω)) coinMeasure :=
    integrable_of_bdd (hRm.mul hcm).aestronglyMeasurable
      (2 * Real.pi * |ξ| * (1 / 3 ^ (10 * s)) * 2) fun ω => by
        rw [norm_mul, Complex.norm_conj]
        gcongr
        · exact hRb ω
        · exact norm_condDiff_le b C h m ω
  have hz : ∫ ω, G (buildU s ω) * (starRingEnd ℂ) (condDiff b C h m ω) ∂coinMeasure = 0 :=
    integral_orth s (h * (b : ℝ) ^ m) G
  simp_rw [hsplit, add_mul]
  rw [integral_add hGi hRi, hz, zero_add]
  have hB : ‖∫ ω, R ω * (starRingEnd ℂ) (condDiff b C h m ω) ∂coinMeasure‖ ≤
      2 * Real.pi * |ξ| * (1 / 3 ^ (10 * s)) * 2 := by
    simpa using norm_integral_le_of_norm_le_const (μ := coinMeasure)
      (Eventually.of_forall fun ω => (by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hRb ω) (norm_condDiff_le b C h m ω) (norm_nonneg _) (by positivity) :
        ‖R ω * (starRingEnd ℂ) (condDiff b C h m ω)‖ ≤ 2 * Real.pi * |ξ| * (1 / 3 ^ (10 * s)) * 2))
  refine hB.trans (le_of_eq_of_le rfl ?_)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  have hst := pow_le_stage b C m (by omega)
  have h3s : (0 : ℝ) < 3 ^ (10 * s) := by positivity
  have hξ : |ξ| = |(h : ℝ)| * (b : ℝ) ^ n := by
    simp only [ξ]; rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ n)]
  rw [hξ, div_eq_mul_inv, div_eq_mul_inv, one_mul]
  have hinv : ((3 : ℝ) ^ (10 * s))⁻¹ ≤ 3 ^ (C + 10) * ((b : ℝ) ^ m)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ h3s]
    calc (1 : ℝ) = (b : ℝ) ^ m * ((b : ℝ) ^ m)⁻¹ := (mul_inv_cancel₀ hbm.ne').symm
      _ ≤ 3 ^ (C + 10) * 3 ^ (10 * s) * ((b : ℝ) ^ m)⁻¹ := by gcongr
      _ = _ := by ring
  have hp : 0 ≤ 2 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ n) := by positivity
  calc 2 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ n) * ((3 : ℝ) ^ (10 * s))⁻¹ * 2
      ≤ 2 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ n) * (3 ^ (C + 10) * ((b : ℝ) ^ m)⁻¹) * 2 := by gcongr
    _ = _ := by ring

theorem geom_sum_le_pow {b : ℕ} (hb : 2 ≤ b) (N : ℕ) : ∑ n ∈ Finset.range N, (b : ℝ) ^ n ≤ (b : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [pow_pos (by linarith : (0 : ℝ) < b) N]

/-- **The martingale part, moment form.**  Proved (`norm_integral_cross`, induction on `N`).  The partial sums of
`e(hbⁿx) − condChar` have second moment `O(N)`.

English proof.  Write `Y_n = e(hbⁿx) − condChar(hbⁿ, s_n, w_{s_n})`, `s_n = stageOf b C n`
(monotone in `n`).  `|Y_n| ≤ 2`.  For `n < m`, `E[G(w_{s_m}) · conj Y_m] = 0` for every function
`G` of the stage-`s_m` prefix (definition of `condChar` on the atoms of `buildU s_m`,
`integral_buildU`), and `Y_n = G(w_{s_m}) + R` with `|R| ≤ 2π|h|bⁿ3^{−10 s_m}`
(`|x − cylLeft w_{s_m}| ≤ 3^{−10 s_m}`, `norm_ee_sub_ee`).  Since `10 s_m ≥ m log₃ b − C − 10`,
`Σ_{m>n} |E Y_n conj Y_m| ≤ 8π|h| 3^{C+10}/(b − 1)`, so `E|Σ_{n<N} Y_n|² ≤ K N`.  Then
Davenport–Erdős–LeVeque along `(j+1)²` (as in `DecayAeNormal.ae_tendsto_weyl`) and
`tendsto_of_tendsto_sched`. -/
theorem condDiff_secondMoment_le {b : ℕ} (hb : 2 ≤ b) (h : ℤ) (C : ℕ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → ∫ ω, ‖∑ n ∈ Finset.range N,
      (ee (h * (b : ℝ) ^ n * cpt (descentU ω)) -
        condChar (h * (b : ℝ) ^ n) (stageOf b C n) (buildU (stageOf b C n) ω))‖ ^ 2 ∂coinMeasure ≤
      K * N := by
  change ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → ∫ ω, ‖∑ n ∈ Finset.range N, condDiff b C h n ω‖ ^ 2
    ∂coinMeasure ≤ K * N
  set D : ℝ := 4 * Real.pi * |(h : ℝ)| * 3 ^ (C + 10) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨4 + 2 * D, fun N hN1 => ?_⟩
  clear hN1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set S : ℕ → (ℕ → Bool) → ℂ := fun N ω => ∑ n ∈ Finset.range N, condDiff b C h n ω
  have hYm := measurable_condDiff b C h
  have hSm : ∀ N, Measurable (S N) := fun N => Finset.measurable_sum _ fun n _ => hYm n
  have hSb : ∀ N ω, ‖S N ω‖ ≤ 2 * N := fun N ω =>
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => norm_condDiff_le b C h n ω).trans
      (by simp [mul_comm]))
  have hsq : ∀ N, Integrable (fun ω => ‖S N ω‖ ^ 2) coinMeasure := fun N =>
    integrable_of_bdd ((hSm N).norm.pow_const 2).aestronglyMeasurable ((2 * N) ^ 2) fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hSb N ω) 2
  induction N with
  | zero => simp
  | succ N ih =>
    have hY2 : Integrable (fun ω => ‖condDiff b C h N ω‖ ^ 2) coinMeasure :=
      integrable_of_bdd ((hYm N).norm.pow_const 2).aestronglyMeasurable (2 ^ 2) fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_condDiff_le b C h N ω) 2
    have hX : Integrable (fun ω => S N ω * (starRingEnd ℂ) (condDiff b C h N ω)) coinMeasure :=
      integrable_of_bdd ((hSm N).mul (Complex.continuous_conj.measurable.comp (hYm N))).aestronglyMeasurable
        (2 * N * 2) fun ω => by
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul (hSb N ω) (norm_condDiff_le b C h N ω) (norm_nonneg _) (by positivity)
    have hpt : ∀ ω, ‖S (N + 1) ω‖ ^ 2 = ‖S N ω‖ ^ 2 + ‖condDiff b C h N ω‖ ^ 2 +
        2 * (S N ω * (starRingEnd ℂ) (condDiff b C h N ω)).re := by
      intro ω
      rw [show S (N + 1) ω = S N ω + condDiff b C h N ω from Finset.sum_range_succ _ _]
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
    have ih' : ∫ ω, ‖S N ω‖ ^ 2 ∂coinMeasure ≤ (4 + 2 * D) * N := ih
    rw [show (∫ ω, ‖∑ n ∈ Finset.range (N + 1), condDiff b C h n ω‖ ^ 2 ∂coinMeasure) =
      ∫ ω, (‖S N ω‖ ^ 2 + ‖condDiff b C h N ω‖ ^ 2 +
        2 * (S N ω * (starRingEnd ℂ) (condDiff b C h N ω)).re) ∂coinMeasure from
      integral_congr_ae (Eventually.of_forall hpt)]
    rw [integral_add (show Integrable (fun ω => ‖S N ω‖ ^ 2 + ‖condDiff b C h N ω‖ ^ 2) coinMeasure
        from (hsq N).add hY2) (show Integrable (fun ω =>
        2 * (S N ω * (starRingEnd ℂ) (condDiff b C h N ω)).re) coinMeasure from hX.re.const_mul 2),
      integral_add (hsq N) hY2, integral_const_mul]
    have hre : ∫ ω, (S N ω * (starRingEnd ℂ) (condDiff b C h N ω)).re ∂coinMeasure =
        (∫ ω, S N ω * (starRingEnd ℂ) (condDiff b C h N ω) ∂coinMeasure).re := integral_re hX
    rw [hre]
    have h1 : ∫ ω, ‖condDiff b C h N ω‖ ^ 2 ∂coinMeasure ≤ 4 := by
      refine (le_abs_self _).trans ?_
      simpa using norm_integral_le_of_norm_le_const (μ := coinMeasure)
        (Eventually.of_forall fun ω => (by
          rw [Real.norm_of_nonneg (by positivity)]
          have := pow_le_pow_left₀ (norm_nonneg _) (norm_condDiff_le b C h N ω) 2
          norm_num at this ⊢; exact this : ‖‖condDiff b C h N ω‖ ^ 2‖ ≤ 4))
    have h2 : (∫ ω, S N ω * (starRingEnd ℂ) (condDiff b C h N ω) ∂coinMeasure).re ≤ D := by
      refine (Complex.re_le_norm _).trans ?_
      have hsplit : ∫ ω, S N ω * (starRingEnd ℂ) (condDiff b C h N ω) ∂coinMeasure =
          ∑ n ∈ Finset.range N, ∫ ω, condDiff b C h n ω * (starRingEnd ℂ) (condDiff b C h N ω)
            ∂coinMeasure := by
        simp only [S, Finset.sum_mul]
        refine integral_finset_sum _ fun n _ => ?_
        exact integrable_of_bdd ((hYm n).mul (Complex.continuous_conj.measurable.comp
          (hYm N))).aestronglyMeasurable (2 * 2) fun ω => by
            rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul (norm_condDiff_le b C h n ω) (norm_condDiff_le b C h N ω)
              (norm_nonneg _) (by norm_num)
      rw [hsplit]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun n hn => norm_integral_cross hb h C
        (le_of_lt (Finset.mem_range.1 hn))).trans ?_
      rw [← Finset.mul_sum, ← Finset.sum_div]
      have hbN : (0 : ℝ) < (b : ℝ) ^ N := by positivity
      calc D * ((∑ n ∈ Finset.range N, (b : ℝ) ^ n) / (b : ℝ) ^ N) ≤ D * 1 := by
            gcongr; rw [div_le_one hbN]; exact geom_sum_le_pow hb N
        _ = D := mul_one D
    push_cast
    linarith

/-- **The martingale part.**  Proved from the moment form `condDiff_secondMoment_le`. -/
theorem ae_cesaro_condDiff {b : ℕ} (hb : 2 ≤ b) (h : ℤ) (C : ℕ) :
    ∀ᵐ ω ∂coinMeasure, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (ee (h * (b : ℝ) ^ n * cpt (descentU ω)) -
        condChar (h * (b : ℝ) ^ n) (stageOf b C n) (buildU (stageOf b C n) ω))) / (N : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := condDiff_secondMoment_le hb h C
  refine ae_cesaro_of_secondMoment_bdd coinMeasure _ (measurable_condDiff b C h) (B := 2)
    (by norm_num) (fun n ω => ?_) K (fun N => (N : ℝ) ^ (-(1 : ℝ)))
    (summable_sched_rpow one_pos) (fun N hN => ?_)
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_ee]; linarith [norm_condChar_le (h * (b : ℝ) ^ n) (stageOf b C n)
      (buildU (stageOf b C n) ω)]
  · refine (hK N hN).trans (le_of_eq ?_)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.rpow_neg_one]; field_simp



/-! ### The Cantor-continuation part: Weyl along `n log₃ b` and a vanishing Cantor product -/

/-- Tripling the remainder `t − round t` when both remainders are below `1/10`. -/
theorem three_mul_rem {t : ℝ} (h1 : |t - round t| < 1 / 10) (h2 : |3 * t - round (3 * t)| < 1 / 10) :
    3 * t - round (3 * t) = 3 * (t - round t) := by
  have hint : (3 * t - round (3 * t)) - 3 * (t - round t) = ((3 * round t - round (3 * t) : ℤ) : ℝ) := by
    push_cast; ring
  have hlt : |((3 * round t - round (3 * t) : ℤ) : ℝ)| < 1 := by
    rw [← hint]
    calc _ ≤ |3 * t - round (3 * t)| + |3 * (t - round t)| := abs_sub _ _
      _ < 1 := by rw [abs_mul]; norm_num; linarith
  have : (3 * round t - round (3 * t) : ℤ) = 0 := by
    have := hlt; rw [← Int.cast_abs] at this
    have : |3 * round t - round (3 * t)| < 1 := by exact_mod_cast this
    rw [abs_lt] at this; omega
  rw [this, Int.cast_zero, sub_eq_zero] at hint
  exact hint

/-- If `3^k y` stays within `1/10` of an integer for all `k ≥ K`, then `3^K y` is an integer. -/
theorem int_of_close {y : ℝ} {K : ℕ}
    (h : ∀ k, K ≤ k → |3 ^ k * y - round (3 ^ k * y)| < 1 / 10) :
    3 ^ K * y = round (3 ^ K * y) := by
  set r : ℕ → ℝ := fun j => 3 ^ (K + j) * y - round (3 ^ (K + j) * y)
  have hr : ∀ j, r j = 3 ^ j * r 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (3 : ℝ) ^ (K + (j + 1)) * y = 3 * (3 ^ (K + j) * y) := by ring
      have := three_mul_rem (h (K + j) (by omega)) (by rw [← e]; exact h _ (by omega))
      simp only [r] at ih ⊢
      rw [e, this, ih]; ring
  have hb : ∀ j, |r 0| * 3 ^ j < 1 / 10 := by
    intro j
    have := h (K + j) (by omega)
    have e := hr j
    simp only [r] at e this
    rw [e, abs_mul, abs_of_pos (by positivity)] at this
    simpa [r, mul_comm] using this
  by_contra hne
  have hpos : 0 < |r 0| := by
    simp only [r, add_zero]; exact abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / 10 / |r 0|) (by norm_num : (1 : ℝ) < 3)
  have := hb j
  rw [div_lt_iff₀ hpos] at hj
  linarith

/-- A factor `|cos(2πx)|` above `cos(π/10)` forces `2x` within `1/10` of an integer. -/
theorem close_of_cos {x : ℝ} (h : Real.cos (Real.pi / 10) < |Real.cos (2 * Real.pi * x)|) :
    |2 * x - round (2 * x)| < 1 / 10 := by
  set t := 2 * x
  set r := t - round t
  have hr : |r| ≤ 1 / 2 := abs_sub_round t
  have hc : |Real.cos (2 * Real.pi * x)| = Real.cos (Real.pi * |r|) := by
    have : 2 * Real.pi * x = Real.pi * r + (round t : ℤ) * Real.pi := by simp only [r, t]; ring
    rw [this, Real.cos_add_int_mul_pi, abs_mul, show |((-1 : ℝ)) ^ round t| = 1 by simp, one_mul]
    rw [show Real.pi * |r| = |Real.pi * r| by rw [abs_mul, abs_of_pos Real.pi_pos], Real.cos_abs]
    refine abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
    · have := neg_abs_le r; nlinarith [Real.pi_pos]
    · have := le_abs_self r; nlinarith [Real.pi_pos]
  rw [hc] at h
  by_contra hge
  push Not at hge
  have := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 10) (y := Real.pi * |r|)
    (by positivity) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  linarith

/-- The Cantor product `Π_{k<C} |cos(2π h 3^k Y)|`. -/
noncomputable def GC (h : ℤ) (C : ℕ) (Y : ℝ) : ℝ := ∏ k ∈ Finset.range C, |Real.cos (2 * Real.pi * (h * 3 ^ k * Y))|

theorem GC_nonneg (h : ℤ) (C : ℕ) (Y : ℝ) : 0 ≤ GC h C Y := Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem GC_le_one (h : ℤ) (C : ℕ) (Y : ℝ) : GC h C Y ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _

theorem tendsto_GC {h : ℤ} {Y : ℝ} (hY : ∀ K : ℕ, (2 * h * 3 ^ K * Y : ℝ) ≠ round (2 * h * 3 ^ K * Y)) :
    Tendsto (fun C => GC h C Y) atTop (𝓝 0) := by
  set θ := Real.cos (Real.pi / 10)
  have hθ0 : 0 ≤ θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hθ1 : θ < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) (by positivity)
  -- infinitely many small factors
  have hbad : ∀ K : ℕ, ∃ k, K ≤ k ∧ |Real.cos (2 * Real.pi * (h * 3 ^ k * Y))| ≤ θ := by
    intro K
    by_contra hcon
    push Not at hcon
    apply hY K
    have := int_of_close (y := 2 * h * Y) (K := K) fun k hk => by
      have := close_of_cos (hcon k hk)
      rwa [show 2 * ((h : ℝ) * 3 ^ k * Y) = 3 ^ k * (2 * h * Y) by ring] at this
    rwa [show (3 : ℝ) ^ K * (2 * h * Y) = 2 * h * 3 ^ K * Y by ring] at this
  have hstep : ∀ j : ℕ, ∃ Cj, ∀ C, Cj ≤ C → GC h C Y ≤ θ ^ j := by
    intro j
    induction j with
    | zero => exact ⟨0, fun C _ => by simpa using GC_le_one h C Y⟩
    | succ j ih =>
      obtain ⟨Cj, hCj⟩ := ih
      obtain ⟨k, hk, hkθ⟩ := hbad Cj
      refine ⟨k + 1, fun C hC => ?_⟩
      have hsplit := Finset.prod_range_mul_prod_Ico
        (fun i => |Real.cos (2 * Real.pi * (h * 3 ^ i * Y))|) (show Cj ≤ C by omega)
      have hmem : k ∈ Finset.Ico Cj C := Finset.mem_Ico.2 ⟨hk, by omega⟩
      have hIco : ∏ i ∈ Finset.Ico Cj C, |Real.cos (2 * Real.pi * (h * 3 ^ i * Y))| ≤ θ := by
        rw [← Finset.mul_prod_erase _ _ hmem]
        have : ∏ i ∈ (Finset.Ico Cj C).erase k, |Real.cos (2 * Real.pi * (h * 3 ^ i * Y))| ≤ 1 :=
          Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _
        have h0 : 0 ≤ ∏ i ∈ (Finset.Ico Cj C).erase k, |Real.cos (2 * Real.pi * (h * 3 ^ i * Y))| :=
          Finset.prod_nonneg fun _ _ => abs_nonneg _
        nlinarith [abs_nonneg (Real.cos (2 * Real.pi * (h * 3 ^ k * Y)))]
      have hG : GC h C Y = GC h Cj Y * ∏ i ∈ Finset.Ico Cj C,
          |Real.cos (2 * Real.pi * (h * 3 ^ i * Y))| := by rw [GC, GC, hsplit]
      rw [hG, pow_succ]
      have h1 := hCj Cj le_rfl
      have h2 : 0 ≤ ∏ i ∈ Finset.Ico Cj C, |Real.cos (2 * Real.pi * (h * 3 ^ i * Y))| :=
        Finset.prod_nonneg fun _ _ => abs_nonneg _
      exact mul_le_mul h1 hIco h2 (pow_nonneg hθ0 _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε hθ1
  obtain ⟨Cj, hCj⟩ := hstep j
  refine ⟨Cj, fun C hC => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (GC_nonneg h C Y)]
  exact lt_of_le_of_lt (hCj C hC) hj


theorem continuous_GC (h : ℤ) (C : ℕ) : Continuous (GC h C) := by
  unfold GC; fun_prop

/-- The exceptional set is countable. -/
theorem countable_exc {h : ℤ} (hh : h ≠ 0) :
    {v : ℝ | ∃ K : ℕ, (2 * h * 3 ^ K * (3 : ℝ) ^ (10 * v) : ℝ) =
      round (2 * h * 3 ^ K * (3 : ℝ) ^ (10 * v))}.Countable := by
  have : {v : ℝ | ∃ K : ℕ, (2 * h * 3 ^ K * (3 : ℝ) ^ (10 * v) : ℝ) =
      round (2 * h * 3 ^ K * (3 : ℝ) ^ (10 * v))} ⊆
      ⋃ K : ℕ, ⋃ m : ℤ, {v : ℝ | (2 * h * 3 ^ K * (3 : ℝ) ^ (10 * v) : ℝ) = m} := by
    rintro v ⟨K, hK⟩
    exact Set.mem_iUnion.2 ⟨K, Set.mem_iUnion.2 ⟨_, hK⟩⟩
  refine Set.Countable.mono this (Set.countable_iUnion fun K => Set.countable_iUnion fun m => ?_)
  refine Set.Subsingleton.countable fun v₁ h₁ v₂ h₂ => ?_
  simp only [Set.mem_setOf_eq] at h₁ h₂
  have hc : (2 * h * 3 ^ K : ℝ) ≠ 0 := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have e : (3 : ℝ) ^ (10 * v₁) = (3 : ℝ) ^ (10 * v₂) := by
    have := h₁.trans h₂.symm
    rwa [mul_right_inj' hc] at this
  have := congrArg (Real.logb 3) e
  rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)] at this
  linarith

/-- The integral of the Cantor product over one period tends to zero. -/
theorem tendsto_integral_GC {h : ℤ} (hh : h ≠ 0) :
    Tendsto (fun C => ∫ v in (0 : ℝ)..1, GC h C ((3 : ℝ) ^ (10 * v))) atTop (𝓝 0) := by
  have hcont : ∀ C, Continuous fun v : ℝ => GC h C ((3 : ℝ) ^ (10 * v)) := fun C =>
    (continuous_GC h C).comp ((Real.continuous_const_rpow (by norm_num : (3:ℝ) ≠ 0)).comp
      (continuous_const.mul continuous_id))
  have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (l := atTop) (F := fun C v => GC h C ((3 : ℝ) ^ (10 * v))) (f := fun _ => 0)
    (fun _ => 1) (Eventually.of_forall fun C => (hcont C).aestronglyMeasurable)
    (Eventually.of_forall fun C => Eventually.of_forall fun v _ => by
      rw [Real.norm_of_nonneg (GC_nonneg _ _ _)]; exact GC_le_one _ _ _)
    intervalIntegrable_const ?_
  · simpa using this
  have hnull := (countable_exc hh).measure_zero volume
  rw [ae_iff]
  refine measure_mono_null (fun v hv => ?_) hnull
  simp only [Set.mem_setOf_eq] at hv ⊢
  by_contra hcon
  push Not at hcon
  exact hv fun _ => tendsto_GC hcon


theorem irrational_logb_three {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : Irrational (Real.logb 3 b) := by
  rintro ⟨q, hq⟩
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hpos : 0 < Real.logb 3 b := Real.logb_pos (by norm_num) hb1
  have hnum : 0 < q.num := Rat.num_pos.2 (by rw [← hq] at hpos; exact_mod_cast hpos)
  have hmul : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have key : (b : ℝ) ^ q.den = 3 ^ q.num.toNat := by
    have e1 : (b : ℝ) = (3 : ℝ) ^ (q : ℝ) := by
      rw [hq, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
    rw [e1, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hmul, ← Real.rpow_natCast]
    congr 1
    have : ((q.num.toNat : ℤ) : ℝ) = (q.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    rw [← this]; norm_cast
  have kn : b ^ q.den = 3 ^ q.num.toNat := by exact_mod_cast key
  have h3d : 3 ∣ b ^ q.den := by
    rw [kn]; exact dvd_pow_self 3 (by omega)
  exact h3 (Nat.prime_three.dvd_of_dvd_pow h3d)

theorem tendsto_fourierMean_linear {β : ℝ} (hβ : Irrational β) (c : ℝ) (k : ℤ) (hk : k ≠ 0) :
    Tendsto (NormalNumbers.fourierMean (fun n => n * β + c) k) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * β)
  set a : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * c)
  have hz1 : z ≠ 1 := by
    intro hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hz
    have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((k * β : ℝ) : ℂ) = (n : ℂ) := by
      have := hn; push_cast
      apply mul_left_cancel₀ hI
      linear_combination this
    have : (k : ℝ) * β = n := by exact_mod_cast this
    exact (hβ.intCast_mul hk).ne_int n this
  have hterm : ∀ n : ℕ, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (((n : ℝ) * β + c : ℝ) : ℂ))
      = a * z ^ n := by
    intro n
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  have hnz : ‖z‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hna : ‖a‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hbound : ∀ N : ℕ, ‖NormalNumbers.fourierMean (fun n => n * β + c) k N‖ ≤
      2 / ‖z - 1‖ * (1 / (N : ℝ)) := by
    intro N
    unfold NormalNumbers.fourierMean
    simp_rw [hterm]
    rw [← Finset.mul_sum, geom_sum_eq hz1, norm_div, norm_mul, hna, one_mul, norm_div,
      Complex.norm_natCast]
    have hn : ‖z ^ N - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_; rw [norm_pow, hnz]; norm_num
    have hz0 : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · simp [h0]
    · have : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_div, div_le_iff₀ (by positivity)]
      calc ‖z ^ N - 1‖ ≤ 2 := hn
        _ = _ := by field_simp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 / ‖z - 1‖)


theorem norm_muK_le_GC {b : ℕ} (hb : 2 ≤ b) (h : ℤ) (C n : ℕ) (hC : C ≤ Nat.log 3 (b ^ n)) :
    ‖muK (h * (b : ℝ) ^ n / 3 ^ (10 * stageOf b C n))‖ ≤
      GC h C ((3 : ℝ) ^ (10 * Int.fract (n * (Real.logb 3 b / 10) + -(C / 10 : ℝ)))) := by
  set L := Nat.log 3 (b ^ n)
  set s := stageOf b C n
  set x : ℝ := n * Real.logb 3 b
  set u : ℝ := n * (Real.logb 3 b / 10) + -(C / 10 : ℝ)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hxL : x = Real.logb 3 ((b ^ n : ℕ) : ℝ) := by
    simp only [x]; push_cast; rw [Real.logb_pow]
  have hL : (⌊x⌋₊ : ℕ) = L := by rw [hxL]; exact_mod_cast Real.natFloor_logb_natCast 3 (b ^ n)
  have hx0 : 0 ≤ x := by
    have : 0 ≤ Real.logb 3 b := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ b))
    positivity
  have hLx : (L : ℝ) ≤ x := by rw [← hL]; exact Nat.floor_le hx0
  have hxL1 : x < L + 1 := by rw [← hL]; exact Nat.lt_floor_add_one x
  have hs1 : 10 * s ≤ L - C := Nat.mul_div_le _ _
  have hs2 : L - C < 10 * s + 10 := by simp only [s, stageOf, L]; omega
  have hs1' : (10 * s : ℝ) + C ≤ L := by
    have : 10 * s + C ≤ L := by omega
    exact_mod_cast this
  have hs2' : (L : ℝ) + 1 ≤ 10 * s + 10 + C := by
    have : L + 1 ≤ 10 * s + 10 + C := by omega
    exact_mod_cast this
  have hux : u = (x - C) / 10 := by simp only [u, x]; ring
  have hfl : ⌊u⌋ = (s : ℤ) := by
    rw [Int.floor_eq_iff]; push_cast
    rw [hux]
    constructor <;> linarith
  have hfr : 10 * Int.fract u = x - C - 10 * s := by
    rw [Int.fract, hfl]; push_cast; simp only [u, x]; ring
  set Y : ℝ := (3 : ℝ) ^ (10 * Int.fract u)
  have hbn : (b : ℝ) ^ n = 3 ^ C * 3 ^ (10 * s) * Y := by
    have e1 : (b : ℝ) ^ n = (3 : ℝ) ^ x := by
      simp only [x]
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hb0,
        Real.rpow_natCast]
    rw [e1, show x = (C : ℝ) + (10 * s : ℕ) + 10 * Int.fract u by rw [hfr]; push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_natCast,
      Real.rpow_natCast]
  have hξ : (h : ℝ) * (b : ℝ) ^ n / 3 ^ (10 * s) = h * 3 ^ C * Y := by
    rw [hbn]; field_simp
  rw [hξ]
  have hc := NormalNumbers.CantorLiouville.charFun_real C (fun _ => true) (h * 3 ^ C * Y)
  rw [Finset.filter_true_of_mem (fun _ _ => rfl)] at hc
  refine le_of_le_of_eq hc ?_
  unfold GC
  rw [← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk := Finset.mem_range.1 hk
  congr 2
  have e : (3 : ℝ) ^ C = 3 ^ (C - 1 - k + 1) * 3 ^ k := by rw [← pow_add]; congr 1; omega
  rw [e]; field_simp

theorem GC_int (h : ℤ) (C m : ℕ) : GC h C ((3 : ℝ) ^ (10 * (m : ℝ))) = 1 := by
  unfold GC
  refine Finset.prod_eq_one fun k _ => ?_
  have e : (2 * Real.pi * ((h : ℝ) * 3 ^ k * (3 : ℝ) ^ (10 * (m : ℝ)))) =
      ((h * 3 ^ k * 3 ^ (10 * m) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [show (10 * (m : ℝ)) = ((10 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast; ring
  rw [e, Real.cos_int_mul_two_pi, abs_one]

theorem le_log_of_two_mul {b : ℕ} (hb : 2 ≤ b) {C n : ℕ} (hn : 2 * C ≤ n) : C ≤ Nat.log 3 (b ^ n) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  calc 3 ^ C ≤ 4 ^ C := Nat.pow_le_pow_left (by norm_num) C
    _ = 2 ^ (2 * C) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    _ ≤ b ^ n := Nat.pow_le_pow_left hb n

/-- The proof of `cesaro_contChar_small`. -/
theorem cesaro_contChar_small_aux {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ C : ℕ, ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, ‖muK (h * (b : ℝ) ^ n / 3 ^ (10 * stageOf b C n))‖) / (N : ℝ) ≤ ε := by
  obtain ⟨C, hC⟩ := ((tendsto_integral_GC hh).eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨C, ?_⟩
  set β : ℝ := Real.logb 3 b / 10
  set c : ℝ := -(C / 10 : ℝ)
  set u : ℕ → ℝ := fun n => n * β + c
  have hβ : Irrational β := by
    simpa using (irrational_logb_three hb h3).div_natCast (m := 10) (by norm_num)
  have hW : ∀ k : ℤ, k ≠ 0 → Tendsto (NormalNumbers.fourierMean u k) atTop (𝓝 0) :=
    fun k hk => tendsto_fourierMean_linear hβ c k hk
  set f : ℝ → ℝ := fun v => GC h C ((3 : ℝ) ^ (10 * v))
  have hfc : Continuous f := (continuous_GC h C).comp
    ((Real.continuous_const_rpow (by norm_num : (3:ℝ) ≠ 0)).comp (continuous_const.mul continuous_id))
  have hf01 : f 0 = f (0 + 1) := by
    simp only [f]
    have h0 := GC_int h C 0
    have h1 := GC_int h C 1
    push_cast at h0 h1
    rw [h0, zero_add, h1]
  let g : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨AddCircle.liftIco 1 0 f, AddCircle.liftIco_continuous hf01 hfc.continuousOn⟩
  have hg : ∀ y : ℝ, g (y : AddCircle (1 : ℝ)) = f (Int.fract y) := by
    intro y
    rw [← AddCircle.coe_fract]
    show AddCircle.liftIco 1 0 f _ = _
    rw [AddCircle.liftIco_coe_apply]
    exact ⟨Int.fract_nonneg y, by rw [zero_add]; exact Int.fract_lt_one y⟩
  have hint : ∫ x in (0 : ℝ)..1, g (x : AddCircle (1 : ℝ)) = ∫ x in (0 : ℝ)..1, f x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [hg]
    rcases eq_or_lt_of_le hx.2 with h1 | h1
    · rw [h1, Int.fract_one, hf01, zero_add]
    · rw [Int.fract_eq_self.2 ⟨hx.1, h1⟩]
  have hlim := NormalNumbers.cgood_real u hW g
  rw [hint] at hlim
  have hev := hlim.eventually (gt_mem_nhds hC)
  have hg0 : ∀ y, 0 ≤ g y := fun y => by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
    show 0 ≤ g ((t : ℝ) : AddCircle (1 : ℝ))
    rw [hg]; exact GC_nonneg _ _ _
  filter_upwards [hev, eventually_ge_atTop (max 1 ⌈4 * C / ε⌉₊)] with N hN hN2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_left hN2
  have hNC : 4 * C / ε ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN2)
  have hterm : ∀ n ∈ Finset.range N, ‖muK (h * (b : ℝ) ^ n / 3 ^ (10 * stageOf b C n))‖ ≤
      g ((u n : ℝ) : AddCircle (1 : ℝ)) + (if n < 2 * C then 1 else 0) := by
    intro n _
    split_ifs with hn
    · have := hg0 ((u n : ℝ) : AddCircle (1 : ℝ))
      linarith [norm_muK_le (h * (b : ℝ) ^ n / 3 ^ (10 * stageOf b C n))]
    · rw [add_zero, hg]
      exact norm_muK_le_GC hb h C n (le_log_of_two_mul hb (by omega))
  have hcnt : ∑ n ∈ Finset.range N, (if n < 2 * C then (1 : ℝ) else 0) ≤ 2 * C := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ((Finset.range N).filter (· < 2 * C)).card ≤ 2 * C := by
      calc _ ≤ (Finset.range (2 * C)).card := Finset.card_le_card fun n hn => by
            simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢; exact hn.2
        _ = 2 * C := Finset.card_range _
    exact_mod_cast this
  have hsum := (Finset.sum_le_sum hterm).trans_eq (Finset.sum_add_distrib)
  have hN0 : (0 : ℝ) < N := by linarith
  rw [div_le_iff₀ hN0]
  have h1 : (∑ k ∈ Finset.range N, g ((u k : ℝ) : AddCircle (1 : ℝ))) < ε / 2 * N := by
    have := hN; rwa [div_lt_iff₀ hN0] at this
  have h2 : (2 * C : ℝ) ≤ ε / 2 * N := by
    rw [div_le_iff₀ hε] at hNC; nlinarith
  linarith


/-- **The Cantor-continuation part is small on average** Proved (`cesaro_contChar_small_aux`).  For
every `ε > 0` some conditioning depth `C` makes the Cesàro means of `|μ̂_K(hbⁿ / 3^{10 s_n})|`
eventually at most `ε`.

English proof.  `‖muK η‖ ≤ Π_{p<M} |cos(2πη/3^{p+1})|` (`charFun_real`).  With
`η = hbⁿ/3^{10 s_n} = h 3^{C + u_n}`, `u_n = 10 frac((n log₃ b − C)/10)`, keep the factors
`p < C`: `‖muK η‖ ≤ g_C(frac v_n)`, `g_C(v) = Π_{k<C} |cos(2π h 3^{10v + k})|`, `v_n = n log₃ b/10 −
C/10`.  `g_C` is continuous on `[0,1]` with `g_C(0) = g_C(1) = 1`, so continuous on the circle,
and `log₃ b` is irrational for `3 ∤ b`, so `(1/N) Σ g_C(frac v_n) → ∫₀¹ g_C` (Weyl,
`WeylCriterion.cgood_all`).  Finally `∫₀¹ g_C ≤ (∫₀¹ g_C²)^{1/2}` and, substituting
`y = |h| 3^{10v}`, `∫₀¹ g_C² ≤ (3^{10}/(10 ln 3)) ∫₀¹ Π_{k<C} cos²(2π 3^k y) dy =
(3^{10}/(10 ln 3)) 2^{−C}` (induction on `C`: `Σ_{j<3} cos²(θ + 2πj/3) = 3/2`). -/
theorem cesaro_contChar_small {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ C : ℕ, ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, ‖muK (h * (b : ℝ) ^ n / 3 ^ (10 * stageOf b C n))‖) / (N : ℝ) ≤ ε := by
  exact cesaro_contChar_small_aux hb h3 h hh hε

/-! ### The crux, second split: conditional means of the local bias on earlier atoms

`E|Σ_{n<N} B_n|²` (`B_n = localBias b C h n`) expands into `E[B_n conj B_m]`.  Since `B_n` is a
function of the stage-`s_n` prefix, `E[B_n conj B_m] = E[B_n conj E[B_m | w_{s_n}]]`
(`integral_comp_mul_condMean`), so the moment node `LocalBiasRate` follows from decay of the
conditional means of later biases on earlier atoms (`LocalBiasMixing`). -/

/-- The conditional mean of `F` on the stage-`s` atom `w` (`0` on a null atom). -/
noncomputable def condMean (F : (ℕ → Bool) → ℂ) (s : ℕ) (w : List Bool) : ℂ :=
  (∫ ω in {ω | buildU s ω = w}, F ω ∂coinMeasure) /
    ((coinMeasure.real {ω | buildU s ω = w} : ℝ) : ℂ)

theorem condMean_mul (F : (ℕ → Bool) → ℂ) (s : ℕ) (w : List Bool) :
    (coinMeasure.real {ω | buildU s ω = w} : ℂ) * condMean F s w =
      ∫ ω in {ω | buildU s ω = w}, F ω ∂coinMeasure := by
  unfold condMean
  rcases eq_or_ne (coinMeasure.real {ω | buildU s ω = w}) 0 with h0 | h0
  · rw [h0]
    have : coinMeasure {ω | buildU s ω = w} = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0
    rw [Measure.restrict_eq_zero.2 this, integral_zero_measure]; simp
  · have : ((coinMeasure.real {ω | buildU s ω = w} : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
    field_simp

theorem norm_condMean_le {F : (ℕ → Bool) → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hFb : ∀ ω, ‖F ω‖ ≤ B)
    (s : ℕ) (w : List Bool) : ‖condMean F s w‖ ≤ B := by
  unfold condMean
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := coinMeasure) (s := {ω | buildU s ω = w}))
    with h0 | hpos
  · rw [← h0, div_zero]; exact hB0
  · rw [div_le_iff₀ hpos]
    exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top _ _)
      (Eventually.of_forall fun ω => hFb ω)

/-- **Tower property on the stage atoms.** -/
theorem integral_comp_mul_condMean (s : ℕ) (G : List Bool → ℂ) {F : (ℕ → Bool) → ℂ}
    (hFm : Measurable F) {B : ℝ} (hB0 : 0 ≤ B) (hFb : ∀ ω, ‖F ω‖ ≤ B) :
    ∫ ω, G (buildU s ω) * (starRingEnd ℂ) (F ω) ∂coinMeasure =
      ∫ ω, G (buildU s ω) * (starRingEnd ℂ) (condMean F s (buildU s ω)) ∂coinMeasure := by
  have hi1 : Integrable (fun ω => G (buildU s ω) * (starRingEnd ℂ) (F ω)) coinMeasure :=
    integrable_of_bdd ((measurable_comp_buildU s G).mul
      (Complex.continuous_conj.measurable.comp hFm)).aestronglyMeasurable
      ((∑ w ∈ LS s, ‖G w‖) * B) fun ω => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (norm_comp_buildU_le s G ω) (hFb ω) (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hi2 : Integrable (fun ω => G (buildU s ω) * (starRingEnd ℂ) (condMean F s (buildU s ω)))
      coinMeasure :=
    integrable_of_bdd ((measurable_comp_buildU s G).mul
      (Complex.continuous_conj.measurable.comp
        (measurable_comp_buildU s (condMean F s)))).aestronglyMeasurable
      ((∑ w ∈ LS s, ‖G w‖) * B) fun ω => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (norm_comp_buildU_le s G ω) (norm_condMean_le hB0 hFb s _) (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hFi : Integrable F coinMeasure := integrable_of_bdd hFm.aestronglyMeasurable B hFb
  rw [integral_eq_sum_atoms s _ hi1, integral_eq_sum_atoms s _ hi2]
  refine Finset.sum_congr rfl fun w _ => ?_
  have eL : ∫ ω in {ω | buildU s ω = w}, G (buildU s ω) * (starRingEnd ℂ) (F ω) ∂coinMeasure =
      G w * (starRingEnd ℂ) (∫ ω in {ω | buildU s ω = w}, F ω ∂coinMeasure) := by
    rw [setIntegral_congr_fun (mset_buildU' s w)
      (g := fun ω => G w * (starRingEnd ℂ) (F ω))
      (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [hω]),
      integral_const_mul, integral_conj]
  have eR : ∫ ω in {ω | buildU s ω = w}, G (buildU s ω) *
      (starRingEnd ℂ) (condMean F s (buildU s ω)) ∂coinMeasure =
      coinMeasure.real {ω | buildU s ω = w} • (G w * (starRingEnd ℂ) (condMean F s w)) := by
    rw [setIntegral_congr_fun (mset_buildU' s w)
      (g := fun _ => G w * (starRingEnd ℂ) (condMean F s w))
      (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [hω]), setIntegral_const]
  rw [eL, eR, ← condMean_mul]
  simp only [map_mul, Complex.conj_ofReal, Complex.real_smul]
  ring

theorem buildU_take {s S : ℕ} (hsS : s ≤ S) (ω : ℕ → Bool) :
    (buildU S ω).take (10 * s) = buildU s ω := by
  have := List.prefix_iff_eq_take.1 (buildU_prefix ω hsS)
  rw [length_buildU] at this; exact this.symm

/-- **Tower property across stages.**  For `s ≤ S`, the stage-`s` conditional mean of the
stage-`S` conditional mean is the stage-`s` conditional mean. -/
theorem condMean_condMean {s S : ℕ} (hsS : s ≤ S) {F : (ℕ → Bool) → ℂ} (hFm : Measurable F)
    {B : ℝ} (hB0 : 0 ≤ B) (hFb : ∀ ω, ‖F ω‖ ≤ B) (w : List Bool) :
    condMean (fun ω => condMean F S (buildU S ω)) s w = condMean F s w := by
  suffices h : ∫ ω in {ω | buildU s ω = w}, condMean F S (buildU S ω) ∂coinMeasure =
      ∫ ω in {ω | buildU s ω = w}, F ω ∂coinMeasure by
    rw [condMean, h, condMean]
  set ind : List Bool → ℂ := fun v => if v.take (10 * s) = w then 1 else 0
  have hind : ∀ ω, {ω | buildU s ω = w}.indicator (fun _ => (1 : ℂ)) ω = ind (buildU S ω) := by
    intro ω
    simp only [Set.indicator, Set.mem_setOf_eq, ind, buildU_take hsS]
  have hFi : Integrable F coinMeasure := integrable_of_bdd hFm.aestronglyMeasurable B hFb
  have hGm : Measurable fun ω => condMean F S (buildU S ω) := measurable_comp_buildU S _
  have hGi : Integrable (fun ω => condMean F S (buildU S ω)) coinMeasure :=
    integrable_of_bdd hGm.aestronglyMeasurable B fun ω => norm_condMean_le hB0 hFb S _
  rw [← integral_indicator (mset_buildU' s w), ← integral_indicator (mset_buildU' s w)]
  have e1 : ∀ X : (ℕ → Bool) → ℂ, {ω | buildU s ω = w}.indicator X =
      fun ω => ind (buildU S ω) * X ω := by
    intro X; funext ω
    rw [← hind]; simp only [Set.indicator]; split_ifs <;> simp
  rw [e1, e1]
  have hi1 : Integrable (fun ω => ind (buildU S ω) * condMean F S (buildU S ω)) coinMeasure :=
    hGi.bdd_mul (measurable_comp_buildU S ind).aestronglyMeasurable
      (Eventually.of_forall fun ω => (show ‖ind (buildU S ω)‖ ≤ 1 by
        simp only [ind]; split_ifs <;> simp))
  have hi2 : Integrable (fun ω => ind (buildU S ω) * F ω) coinMeasure :=
    hFi.bdd_mul (measurable_comp_buildU S ind).aestronglyMeasurable
      (Eventually.of_forall fun ω => (show ‖ind (buildU S ω)‖ ≤ 1 by
        simp only [ind]; split_ifs <;> simp))
  rw [integral_eq_sum_atoms S _ hi1, integral_eq_sum_atoms S _ hi2]
  refine Finset.sum_congr rfl fun v _ => ?_
  have eL : ∫ ω in {ω | buildU S ω = v}, ind (buildU S ω) * condMean F S (buildU S ω) ∂coinMeasure =
      coinMeasure.real {ω | buildU S ω = v} • (ind v * condMean F S v) := by
    rw [setIntegral_congr_fun (mset_buildU' S v) (g := fun _ => ind v * condMean F S v)
      (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [hω]), setIntegral_const]
  have eR : ∫ ω in {ω | buildU S ω = v}, ind (buildU S ω) * F ω ∂coinMeasure =
      ind v * ∫ ω in {ω | buildU S ω = v}, F ω ∂coinMeasure := by
    rw [setIntegral_congr_fun (mset_buildU' S v) (g := fun ω => ind v * F ω)
      (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [hω]), integral_const_mul]
  rw [eL, eR, ← condMean_mul, Complex.real_smul]
  ring


theorem condMean_sub {F G : (ℕ → Bool) → ℂ} (hF : Integrable F coinMeasure)
    (hG : Integrable G coinMeasure) (s : ℕ) (w : List Bool) :
    condMean (fun ω => F ω - G ω) s w = condMean F s w - condMean G s w := by
  unfold condMean
  rw [integral_sub hF.integrableOn hG.integrableOn, sub_div]

/-- **The conditional local bias on an earlier atom** is the difference, at `ξ = hbᵐ`, between the
conditional character of `resLaw` and the conditional mean of the Cantor-continued character at
stage `s_m`. -/
theorem condMean_localBias (b C : ℕ) (h : ℤ) (m : ℕ) {s : ℕ} (hs : s ≤ stageOf b C m)
    (w : List Bool) :
    condMean (localBias b C h m) s w = condChar (h * (b : ℝ) ^ m) s w -
      condMean (fun ω => contChar (h * (b : ℝ) ^ m) (buildU (stageOf b C m) ω)) s w := by
  set ξ : ℝ := h * (b : ℝ) ^ m
  set S := stageOf b C m
  have hE : Measurable fun ω => ee (ξ * cpt (descentU ω)) := measurable_ee_descentU ξ
  have hEb : ∀ ω, ‖ee (ξ * cpt (descentU ω))‖ ≤ 1 := fun ω => (norm_ee _).le
  have hc : condChar ξ S = condMean (fun ω => ee (ξ * cpt (descentU ω))) S := rfl
  have hc' : condChar ξ s = condMean (fun ω => ee (ξ * cpt (descentU ω))) s := rfl
  have hLB : localBias b C h m = fun ω =>
      condMean (fun ω => ee (ξ * cpt (descentU ω))) S (buildU S ω) - contChar ξ (buildU S ω) := by
    funext ω; simp only [localBias, hc, ξ, S]
  have hi1 : Integrable (fun ω => condMean (fun ω => ee (ξ * cpt (descentU ω))) S (buildU S ω))
      coinMeasure :=
    integrable_of_bdd (measurable_comp_buildU S _).aestronglyMeasurable 1
      fun ω => norm_condMean_le zero_le_one hEb S _
  have hi2 : Integrable (fun ω => contChar ξ (buildU S ω)) coinMeasure :=
    integrable_of_bdd (measurable_comp_buildU S _).aestronglyMeasurable 1 fun ω => by
      rw [norm_contChar]; exact norm_muK_le _
  rw [hLB, condMean_sub hi1 hi2, condMean_condMean hs hE zero_le_one hEb, hc']


/-- **One-digit self-similarity of `μ̂_K`.** -/
theorem muK_succ (ξ : ℝ) : muK ξ = (1 + ee (2 * ξ / 3)) / 2 * muK (ξ / 3) := by
  set g : (ℕ → Bool) → ℂ := fun ω => ee (ξ * cpt ω)
  have hgm : Measurable g := measurable_ee.comp (measurable_cpt.const_mul ξ)
  have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_ee _).le)
  have hc : ∀ c, ∫ ω, g (CantorSelfSimilar.consB c ω) ∂coinMeasure =
      ee (ξ * ((if c then 2 else 0) / 3)) * muK (ξ / 3) := by
    intro c
    unfold muK
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [g, cpt, pt_consB, ← ee_add, Bool.true_and]
    congr 1; ring
  have hsplit : ∫ ω, g ω ∂coinMeasure =
      2⁻¹ * ∫ ω, g (CantorSelfSimilar.consB true ω) ∂coinMeasure +
        2⁻¹ * ∫ ω, g (CantorSelfSimilar.consB false ω) ∂coinMeasure := by
    conv_lhs => rw [CantorSelfSimilar.coinMeasure_eq]
    rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
        ((hgi _ inferInstance).smul_measure (by simp)),
      integral_smul_measure, integral_smul_measure,
      integral_map (CantorSelfSimilar.measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
      integral_map (CantorSelfSimilar.measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
    simp [ENNReal.toReal_inv]
  change ∫ ω, g ω ∂coinMeasure = _
  rw [hsplit, hc, hc]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [show ξ * (0 / 3) = 0 by ring, show ξ * (2 / 3) = 2 * ξ / 3 by ring]
  simp [ee]; ring

theorem muK_iter (ξ : ℝ) (L k : ℕ) : muK (ξ / 3 ^ L) =
    (∏ i ∈ Finset.range k, (1 + ee (2 * ξ / 3 ^ (L + i + 1))) / 2) * muK (ξ / 3 ^ (L + k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, Finset.prod_range_succ, muK_succ (ξ / 3 ^ (L + k))]
    have e1 : 2 * (ξ / 3 ^ (L + k)) / 3 = 2 * ξ / 3 ^ (L + k + 1) := by
      rw [pow_succ]; field_simp
    have e2 : ξ / 3 ^ (L + k) / 3 = ξ / 3 ^ (L + (k + 1)) := by
      rw [← add_assoc, pow_succ]; field_simp
    rw [e1, e2]; ring

/-- **Stage self-similarity of `μ̂_K`.** -/
theorem muK_stage (ξ : ℝ) (L : ℕ) : muK (ξ / 3 ^ L) = rhoS ξ L * muK (ξ / 3 ^ (L + 10)) := by
  rw [muK_iter ξ L 10, rhoS_eq_prod, Fin.prod_univ_eq_prod_range
    (fun i => (1 + ee (2 * ξ / 3 ^ (L + i + 1))) / 2)]


open Classical in
/-- The child atoms of a stage-`S` atom: uniform on the alive children. -/
theorem real_child (S : ℕ) (w : List Bool) (hl : w.length = 10 * S) (f : Fin 10 → Bool) :
    coinMeasure.real {ω | buildU (S + 1) ω = w ++ List.ofFn f} =
      if f ∈ aliveSet w then coinMeasure.real {ω | buildU S ω = w} / (aliveSet w).card else 0 := by
  have hc : ((aliveSet w).card : ℝ) ≠ 0 := by exact_mod_cast (card_aliveSet_pos w).ne'
  split_ifs with hf
  · have h1 := buildU_succ_uniform S w (List.ofFn f) ⟨by simp, (Finset.mem_filter.1 hf).2⟩
    have h2 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2
    rw [eq_div_iff hc]; exact h2
  · have : {ω | buildU (S + 1) ω = w ++ List.ofFn f} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      change buildU S ω ++ selU (buildU S ω) ω S = w ++ List.ofFn f at h
      have h1 := (List.append_inj h (by rw [length_buildU, hl])).1
      rw [h1] at h
      have h2 := List.append_cancel_left h
      apply hf
      simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h2, ← h1]; exact (selU_alive _ ω S).2
    rw [this]; simp

theorem setIntegral_buildU_succ (S : ℕ) {w : List Bool} (hw : w ∈ LS S) (G : List Bool → ℂ) :
    ∫ ω in {ω | buildU S ω = w}, G (buildU (S + 1) ω) ∂coinMeasure =
      ∑ f : Fin 10 → Bool, coinMeasure.real {ω | buildU (S + 1) ω = w ++ List.ofFn f} •
        G (w ++ List.ofFn f) := by
  classical
  set H : List Bool → ℂ := fun v => if v.take (10 * S) = w then G v else 0
  have hind : {ω | buildU S ω = w}.indicator (fun ω => G (buildU (S + 1) ω)) =
      fun ω => H (buildU (S + 1) ω) := by
    funext ω
    simp only [Set.indicator, Set.mem_setOf_eq, H, buildU_take (Nat.le_succ S)]
  rw [← integral_indicator (mset_buildU' S w), hind, integral_buildU_succ S H]
  rw [Finset.sum_eq_single w]
  · refine Finset.sum_congr rfl fun f _ => ?_
    simp only [H]
    rw [List.take_left' (by rw [length_of_mem_LS hw])]; simp
  · intro w' hw' hne
    refine Finset.sum_eq_zero fun f _ => ?_
    simp only [H]
    rw [List.take_left' (by rw [length_of_mem_LS hw']), if_neg hne, smul_zero]
  · intro h; exact absurd hw h

/-- **One stage of the Cantor-continued character.**  On a stage-`S` atom, the next stage's
Cantor-continued character averages to the current one minus the dead correction. -/
theorem setIntegral_contChar_succ (ξ : ℝ) (S : ℕ) {w : List Bool} (hw : w ∈ LS S) :
    ∫ ω in {ω | buildU S ω = w}, contChar ξ (buildU (S + 1) ω) ∂coinMeasure =
      (coinMeasure.real {ω | buildU S ω = w} : ℂ) * (contChar ξ w -
        ee (ξ * cylLeft w) * deadErr ξ w * muK (ξ / 3 ^ (w.length + 10))) := by
  classical
  have hl := length_of_mem_LS hw
  rw [setIntegral_buildU_succ S hw]
  set m := coinMeasure.real {ω | buildU S ω = w}
  set c := (aliveSet w).card
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast (card_aliveSet_pos w).ne'
  have hch : ∀ f : Fin 10 → Bool, contChar ξ (w ++ List.ofFn f) =
      ee (ξ * cylLeft w) * ee (ξ * J f / 3 ^ (w.length + 10)) * muK (ξ / 3 ^ (w.length + 10)) := by
    intro f
    unfold contChar
    rw [cylLeft_child, ← ee_add, List.length_append, List.length_ofFn]
    congr 2; ring
  simp only [real_child S w (by rw [hl]) , hch, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  have avg := alive_avg ξ w
  have hsum : ∑ f ∈ aliveSet w, (m / c) • (ee (ξ * cylLeft w) * ee (ξ * J f / 3 ^ (w.length + 10)) *
      muK (ξ / 3 ^ (w.length + 10))) = (m : ℂ) * ee (ξ * cylLeft w) * muK (ξ / 3 ^ (w.length + 10)) *
        ((1 / (c : ℂ)) * ∑ f ∈ aliveSet w, ee (ξ * J f / 3 ^ (w.length + 10))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Complex.real_smul]; push_cast
    field_simp
  rw [hsum, avg]
  unfold contChar
  rw [muK_stage ξ w.length]
  ring

/-- The averaged conditional bias: `E ‖E[B_m | w_{s_n}]‖`. -/
noncomputable def biasMix (b C : ℕ) (h : ℤ) (n m : ℕ) : ℝ :=
  ∫ ω, ‖condMean (localBias b C h m) (stageOf b C n) (buildU (stageOf b C n) ω)‖ ∂coinMeasure

theorem norm_integral_bias_cross (b C : ℕ) (h : ℤ) (n m : ℕ) :
    ‖∫ ω, localBias b C h n ω * (starRingEnd ℂ) (localBias b C h m ω) ∂coinMeasure‖ ≤
      2 * biasMix b C h n m := by
  set s := stageOf b C n
  set G : List Bool → ℂ := fun w => condChar (h * (b : ℝ) ^ n) s w - contChar (h * (b : ℝ) ^ n) w
  have hG : ∀ ω, localBias b C h n ω = G (buildU s ω) := fun ω => rfl
  simp_rw [hG]
  rw [integral_comp_mul_condMean s G (measurable_localBias b C h m) (by norm_num)
    (norm_localBias_le b C h m)]
  have hGb : ∀ w, ‖G w‖ ≤ 2 := by
    intro w
    refine (norm_sub_le _ _).trans ?_
    rw [norm_contChar]
    linarith [norm_condChar_le (h * (b : ℝ) ^ n) s w,
      norm_muK_le (h * (b : ℝ) ^ n / 3 ^ w.length)]
  have hcm : Measurable fun ω => condMean (localBias b C h m) s (buildU s ω) :=
    measurable_comp_buildU s _
  refine (norm_integral_le_integral_norm _).trans ?_
  unfold biasMix
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (Eventually.of_forall fun ω => ?_)
  · exact (integrable_of_bdd hcm.norm.aestronglyMeasurable 2 fun ω => by
      rw [norm_norm]; exact norm_condMean_le (by norm_num) (norm_localBias_le b C h m) s _).const_mul 2
  · simp only
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hGb _) (norm_nonneg _)

/-- **Mixing node for the crux.**  The conditional means of the later local biases on earlier
stage atoms are small on average: `Σ_{n<m<N} E‖E[B_m | w_{s_n}]‖ = O(N² W(N))`, `W` summable
along `sched`.  Implies `LocalBiasRate b` (`localBiasRate_of_mixing`).

Content.  By the tower property `E[B_m | w_s]` (`s = s_n < s_m`) is the difference, at the
frequency `ξ = hbᵐ`, between the conditional character of `resLaw` given `w_s` and that of
"`resLaw` to stage `s_m`, then the Cantor continuation"; so only the dead corrections of the
stages near `s_m` enter, through the phases `e(ξ cylLeft w_t)` of the obstacle rationals
`p/q` (`q ≈ 3^{5 s_m}`) averaged over the resampled blocks between `s` and `s_m`.  Decay in
`s_m − s` is therefore equidistribution of the phases `e(hbᵐ p/q)` of the obstacles met in a
coarse cylinder, averaged over the uniformly resampled path.  Same guards as the crux: an
any-rule argument reduces to `DeadRateDecay` (believed false), and `b = 3` fails
(`not_casselsRate_three`). -/
def LocalBiasMixing (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m, biasMix b C h n m ≤ K * (N : ℝ) ^ 2 * W N

/-- **Mixing node ⇒ moment node.**  Proved (expansion of the second moment, tower property). -/
theorem localBiasRate_of_mixing {b : ℕ} (hM : LocalBiasMixing b) : LocalBiasRate b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hM h hh C
  set S : ℕ → (ℕ → Bool) → ℂ := fun N ω => ∑ n ∈ Finset.range N, localBias b C h n ω
  have hYm := measurable_localBias b C h
  have hYb := norm_localBias_le b C h
  have hSm : ∀ N, Measurable (S N) := fun N => Finset.measurable_sum _ fun n _ => hYm n
  have hSb : ∀ N ω, ‖S N ω‖ ≤ 2 * N := fun N ω =>
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => hYb n ω).trans (by simp [mul_comm]))
  have hsq : ∀ N, Integrable (fun ω => ‖S N ω‖ ^ 2) coinMeasure := fun N =>
    integrable_of_bdd ((hSm N).norm.pow_const 2).aestronglyMeasurable ((2 * N) ^ 2) fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hSb N ω) 2
  have key : ∀ N : ℕ, ∫ ω, ‖S N ω‖ ^ 2 ∂coinMeasure ≤
      4 * N + 4 * ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m, biasMix b C h n m := by
    intro N
    induction N with
    | zero => simp [S]
    | succ N ih =>
      have hY2 : Integrable (fun ω => ‖localBias b C h N ω‖ ^ 2) coinMeasure :=
        integrable_of_bdd ((hYm N).norm.pow_const 2).aestronglyMeasurable (2 ^ 2) fun ω => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hYb N ω) 2
      have hX : Integrable (fun ω => S N ω * (starRingEnd ℂ) (localBias b C h N ω)) coinMeasure :=
        integrable_of_bdd ((hSm N).mul (Complex.continuous_conj.measurable.comp
          (hYm N))).aestronglyMeasurable (2 * N * 2) fun ω => by
            rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul (hSb N ω) (hYb N ω) (norm_nonneg _) (by positivity)
      have hpt : ∀ ω, ‖S (N + 1) ω‖ ^ 2 = ‖S N ω‖ ^ 2 + ‖localBias b C h N ω‖ ^ 2 +
          2 * (S N ω * (starRingEnd ℂ) (localBias b C h N ω)).re := by
        intro ω
        rw [show S (N + 1) ω = S N ω + localBias b C h N ω from Finset.sum_range_succ _ _]
        rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
      rw [integral_congr_ae (Eventually.of_forall hpt)]
      rw [integral_add (show Integrable (fun ω => ‖S N ω‖ ^ 2 + ‖localBias b C h N ω‖ ^ 2)
          coinMeasure from (hsq N).add hY2) (show Integrable (fun ω =>
          2 * (S N ω * (starRingEnd ℂ) (localBias b C h N ω)).re) coinMeasure from
          hX.re.const_mul 2),
        integral_add (hsq N) hY2, integral_const_mul]
      have hre : ∫ ω, (S N ω * (starRingEnd ℂ) (localBias b C h N ω)).re ∂coinMeasure =
          (∫ ω, S N ω * (starRingEnd ℂ) (localBias b C h N ω) ∂coinMeasure).re := integral_re hX
      rw [hre]
      have h1 : ∫ ω, ‖localBias b C h N ω‖ ^ 2 ∂coinMeasure ≤ 4 := by
        refine (le_abs_self _).trans ?_
        simpa using norm_integral_le_of_norm_le_const (μ := coinMeasure)
          (Eventually.of_forall fun ω => (by
            rw [Real.norm_of_nonneg (by positivity)]
            have := pow_le_pow_left₀ (norm_nonneg _) (hYb N ω) 2
            norm_num at this ⊢; exact this : ‖‖localBias b C h N ω‖ ^ 2‖ ≤ 4))
      have h2 : (∫ ω, S N ω * (starRingEnd ℂ) (localBias b C h N ω) ∂coinMeasure).re ≤
          ∑ n ∈ Finset.range N, 2 * biasMix b C h n N := by
        refine (Complex.re_le_norm _).trans ?_
        have hsplit : ∫ ω, S N ω * (starRingEnd ℂ) (localBias b C h N ω) ∂coinMeasure =
            ∑ n ∈ Finset.range N, ∫ ω, localBias b C h n ω * (starRingEnd ℂ) (localBias b C h N ω)
              ∂coinMeasure := by
          simp only [S, Finset.sum_mul]
          refine integral_finset_sum _ fun n _ => ?_
          exact integrable_of_bdd ((hYm n).mul (Complex.continuous_conj.measurable.comp
            (hYm N))).aestronglyMeasurable (2 * 2) fun ω => by
              rw [norm_mul, Complex.norm_conj]
              exact mul_le_mul (hYb n ω) (hYb N ω) (norm_nonneg _) (by norm_num)
        rw [hsplit]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ =>
          norm_integral_bias_cross b C h n N)
      have ih' : ∫ ω, ‖S N ω‖ ^ 2 ∂coinMeasure ≤
          4 * N + 4 * ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m, biasMix b C h n m := ih
      rw [Finset.sum_range_succ (fun m => ∑ n ∈ Finset.range m, biasMix b C h n m), ← Finset.mul_sum] at *
      push_cast
      linarith
  refine ⟨1, fun N => 4 * (N : ℝ) ^ (-(1 : ℝ)) + 4 * K * W N,
    ((summable_sched_rpow one_pos).mul_left 4).add (hW.mul_left (4 * K)), fun N hN => ?_⟩
  refine (key N).trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have := hK N hN
  show _ ≤ 1 * (N : ℝ) ^ 2 * (4 * (N : ℝ) ^ (-(1 : ℝ)) + 4 * K * W N)
  rw [Real.rpow_neg_one]
  have e : (1 : ℝ) * N ^ 2 * (4 * (N : ℝ)⁻¹ + 4 * K * W N) = 4 * N + 4 * (K * N ^ 2 * W N) := by
    field_simp
  rw [e]; linarith

/-! ### Telescoping the conditional bias over stages

By the tower property and the one-stage identity `setIntegral_contChar_succ` (which is where the
uniformity of the resampled block enters), `E[B_m | w_s]` is minus the sum over stages
`t ≥ s_m` of the conditional means of the stage dead corrections `deadCorr`, up to the
truncation error `4π|ξ|3^{−10T}`. -/

/-- The stage dead correction of the Cantor-continued character:
`D(ξ, w) = e(ξ cylLeft w) · deadErr ξ w · μ̂_K(ξ / 3^{|w|+10})`. -/
noncomputable def deadCorr (ξ : ℝ) (w : List Bool) : ℂ :=
  ee (ξ * cylLeft w) * deadErr ξ w * muK (ξ / 3 ^ (w.length + 10))

theorem integrable_comp_buildU (S : ℕ) (G : List Bool → ℂ) :
    Integrable (fun ω => G (buildU S ω)) coinMeasure :=
  integrable_of_bdd (measurable_comp_buildU S G).aestronglyMeasurable _ (norm_comp_buildU_le S G)

/-- Equal integrals on every stage-`S` atom give equal integrals on every coarser atom. -/
theorem setIntegral_eq_of_atoms {s S : ℕ} (hsS : s ≤ S) {F G : (ℕ → Bool) → ℂ}
    (hF : Integrable F coinMeasure) (hG : Integrable G coinMeasure)
    (h : ∀ v ∈ LS S, ∫ ω in {ω | buildU S ω = v}, F ω ∂coinMeasure =
      ∫ ω in {ω | buildU S ω = v}, G ω ∂coinMeasure) (w : List Bool) :
    ∫ ω in {ω | buildU s ω = w}, F ω ∂coinMeasure =
      ∫ ω in {ω | buildU s ω = w}, G ω ∂coinMeasure := by
  set ind : List Bool → ℂ := fun v => if v.take (10 * s) = w then 1 else 0
  rw [← integral_indicator (mset_buildU' s w), ← integral_indicator (mset_buildU' s w)]
  have e1 : ∀ X : (ℕ → Bool) → ℂ, {ω | buildU s ω = w}.indicator X =
      fun ω => ind (buildU S ω) * X ω := by
    intro X; funext ω
    by_cases hb : buildU s ω = w <;> simp [Set.indicator, ind, buildU_take hsS, hb]
  have hind : ∀ ω, ‖ind (buildU S ω)‖ ≤ 1 := fun ω => by simp only [ind]; split_ifs <;> simp
  rw [e1, e1]
  have hi1 : Integrable (fun ω => ind (buildU S ω) * F ω) coinMeasure :=
    hF.bdd_mul (measurable_comp_buildU S ind).aestronglyMeasurable (Eventually.of_forall hind)
  have hi2 : Integrable (fun ω => ind (buildU S ω) * G ω) coinMeasure :=
    hG.bdd_mul (measurable_comp_buildU S ind).aestronglyMeasurable (Eventually.of_forall hind)
  rw [integral_eq_sum_atoms S _ hi1, integral_eq_sum_atoms S _ hi2]
  refine Finset.sum_congr rfl fun v hv => ?_
  have e : ∀ X : (ℕ → Bool) → ℂ, ∫ ω in {ω | buildU S ω = v}, ind (buildU S ω) * X ω ∂coinMeasure =
      ind v * ∫ ω in {ω | buildU S ω = v}, X ω ∂coinMeasure := by
    intro X
    rw [setIntegral_congr_fun (mset_buildU' S v) (g := fun ω => ind v * X ω)
      (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [hω]), integral_const_mul]
  rw [e, e, h v hv]

/-- **One stage of the conditional Cantor-continued character** (uses the uniformity of the
resampled block through `setIntegral_contChar_succ`). -/
theorem condMean_contChar_succ (ξ : ℝ) {s t : ℕ} (hst : s ≤ t) (w : List Bool) :
    condMean (fun ω => contChar ξ (buildU (t + 1) ω)) s w =
      condMean (fun ω => contChar ξ (buildU t ω)) s w -
        condMean (fun ω => deadCorr ξ (buildU t ω)) s w := by
  rw [← condMean_sub (integrable_comp_buildU _ _) (integrable_comp_buildU _ _)]
  unfold condMean
  congr 1
  refine setIntegral_eq_of_atoms (S := t) hst (integrable_comp_buildU (t + 1) _)
    ((integrable_comp_buildU t _).sub (integrable_comp_buildU t _)) (fun v hv => ?_) w
  rw [setIntegral_contChar_succ ξ t hv]
  rw [setIntegral_congr_fun (mset_buildU' t v) (g := fun _ => contChar ξ v - deadCorr ξ v)
    (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [Pi.sub_apply, hω]),
    setIntegral_const,
    Complex.real_smul]
  rfl

/-- **The stage telescope of the conditional Cantor-continued character.** -/
theorem condMean_contChar_telescope (ξ : ℝ) {s a : ℕ} (hsa : s ≤ a) (w : List Bool) (k : ℕ) :
    condMean (fun ω => contChar ξ (buildU (a + k) ω)) s w =
      condMean (fun ω => contChar ξ (buildU a ω)) s w -
        ∑ t ∈ Finset.Ico a (a + k), condMean (fun ω => deadCorr ξ (buildU t ω)) s w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + (k + 1) = a + k + 1 from rfl,
      condMean_contChar_succ ξ (hsa.trans (Nat.le_add_right a k)), ih,
      Finset.sum_Ico_succ_top (Nat.le_add_right a k)]
    ring

theorem norm_one_sub_muK (η : ℝ) : ‖1 - muK η‖ ≤ 2 * Real.pi * |η| := by
  unfold muK
  have hi : Integrable (fun ω => ee (η * cpt ω)) coinMeasure :=
    integrable_of_bdd (measurable_ee.comp (measurable_cpt.const_mul η)).aestronglyMeasurable 1
      (fun ω => (norm_ee _).le)
  have h1 : (1 : ℂ) = ∫ _ω, (1 : ℂ) ∂coinMeasure := by simp
  rw [h1, ← integral_sub (integrable_const _) hi]
  refine (norm_integral_le_of_norm_le_const (C := 2 * Real.pi * |η|)
    (Eventually.of_forall fun ω => ?_)).trans (by simp)
  have hc := cantorSet_subset_unitInterval (cpt_mem_cantorSet ω)
  have e : (1 : ℂ) = ee 0 := by simp [ee]
  rw [e]
  refine (norm_ee_sub_ee _ _).trans ?_
  rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg hc.1]
  have := mul_le_of_le_one_right (abs_nonneg η) hc.2
  have hp := Real.pi_pos
  nlinarith

theorem norm_ee_sub_contChar (ξ : ℝ) (ω : ℕ → Bool) (T : ℕ) :
    ‖ee (ξ * cpt (descentU ω)) - contChar ξ (buildU T ω)‖ ≤ 4 * Real.pi * |ξ| / 3 ^ (10 * T) := by
  unfold contChar
  rw [length_buildU]
  have e : ee (ξ * cpt (descentU ω)) - ee (ξ * cylLeft (buildU T ω)) * muK (ξ / 3 ^ (10 * T)) =
      (ee (ξ * cpt (descentU ω)) - ee (ξ * cylLeft (buildU T ω))) +
        ee (ξ * cylLeft (buildU T ω)) * (1 - muK (ξ / 3 ^ (10 * T))) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_ee, one_mul]
  have h1 := norm_ee_sub_ee (ξ * cpt (descentU ω)) (ξ * cylLeft (buildU T ω))
  have h2 := norm_one_sub_muK (ξ / 3 ^ (10 * T))
  have h3 := abs_cpt_sub_cylLeft ω T
  have hp : (0 : ℝ) < 3 ^ (10 * T) := by positivity
  rw [← mul_sub, abs_mul] at h1
  rw [abs_div, abs_of_pos hp] at h2
  have h4 : 2 * Real.pi * (|ξ| * |cpt (descentU ω) - cylLeft (buildU T ω)|) ≤
      2 * Real.pi * (|ξ| * (1 / 3 ^ (10 * T))) := by gcongr
  have a : 2 * Real.pi * (|ξ| * (1 / 3 ^ (10 * T))) = 2 * Real.pi * |ξ| / 3 ^ (10 * T) := by ring
  have b : 2 * Real.pi * (|ξ| / 3 ^ (10 * T)) = 2 * Real.pi * |ξ| / 3 ^ (10 * T) := by ring
  have c : 4 * Real.pi * |ξ| / 3 ^ (10 * T) = 2 * (2 * Real.pi * |ξ| / 3 ^ (10 * T)) := by ring
  linarith

/-- **The telescoped conditional bias.**  For `s ≤ s_m` and any truncation `T = s_m + k`,
`E[B_m | w_s] = −Σ_{t ∈ [s_m, T)} E[D_t | w_s] + O(4π|ξ| 3^{−10T})`, `ξ = hbᵐ`. -/
theorem norm_condMean_localBias_add_le (b C : ℕ) (h : ℤ) (m : ℕ) {s : ℕ}
    (hs : s ≤ stageOf b C m) (w : List Bool) (k : ℕ) :
    ‖condMean (localBias b C h m) s w + ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k),
        condMean (fun ω => deadCorr (h * (b : ℝ) ^ m) (buildU t ω)) s w‖ ≤
      4 * Real.pi * |h * (b : ℝ) ^ m| / 3 ^ (10 * (stageOf b C m + k)) := by
  set ξ : ℝ := h * (b : ℝ) ^ m
  set a := stageOf b C m
  rw [condMean_localBias b C h m hs w]
  have tel := condMean_contChar_telescope ξ hs w k
  have hie : Integrable (fun ω => ee (ξ * cpt (descentU ω))) coinMeasure :=
    integrable_of_bdd (measurable_ee_descentU ξ).aestronglyMeasurable 1 fun ω => (norm_ee _).le
  have key : condChar ξ s w - condMean (fun ω => contChar ξ (buildU a ω)) s w +
      ∑ t ∈ Finset.Ico a (a + k), condMean (fun ω => deadCorr ξ (buildU t ω)) s w =
      condMean (fun ω => ee (ξ * cpt (descentU ω)) - contChar ξ (buildU (a + k) ω)) s w := by
    rw [condMean_sub hie (integrable_comp_buildU _ _), tel]
    show condMean (fun ω => ee (ξ * cpt (descentU ω))) s w - _ + _ = _
    ring
  rw [key]
  exact norm_condMean_le (by positivity) (fun ω => norm_ee_sub_contChar ξ ω _) s w

/-- The averaged conditional dead correction: `E ‖E[D_t | w_{s_n}]‖` at `ξ = hbᵐ`. -/
noncomputable def deadMix (b C : ℕ) (h : ℤ) (n m t : ℕ) : ℝ :=
  ∫ ω, ‖condMean (fun ω' => deadCorr (h * (b : ℝ) ^ m) (buildU t ω')) (stageOf b C n)
    (buildU (stageOf b C n) ω)‖ ∂coinMeasure

/-- **Obstacle-phase mixing node.**  Believed 50% for `3 ∤ b`.  The conditional means, on the
stage-`s_n` atoms, of the stage dead corrections `D_t` at the frequency `hbᵐ`, summed over the
stages `t ≥ s_m` (any truncation) and over the pairs `n < m < N`, are `O(N² W(N))`, `W` summable
along `sched`.  Implies `LocalBiasMixing b` (`localBiasMixing_of_obstaclePhase`).

Content.  `D_t(ξ, w) = e(ξ cylLeft w) · deadErr ξ w · μ̂_K(ξ/3^{|w|+10})`; the factor
`deadErr` is supported on the dead children of `w`, which sit at the rationals `p/q`,
`q ≈ 3^{5t}`, within `c₀/q²` of `K`.  So `E[D_t | w_{s_n}]` averages the phases `e(hbᵐ p/q)` of the
obstacles met below the coarse cylinder `w_{s_n}`, along the uniformly resampled path.  The
stages `t ≥ s_m + R` cost `O(|h|3^{C+10−10R})` each (`norm_deadErr_le`), so only `O(1)` stages
near the scale of `bᵐ` matter.  The triangle inequality over `t` is taken inside the
expectation; the cancellation that is lost there is between different stages of one path.
Guards: the identity behind this reduction uses the uniformity of the resampled block
(`setIntegral_contChar_succ`); under an arbitrary rule the replacement's own character would
appear in place of `deadErr`.  `b = 3` fails (`not_casselsRate_three`). -/
def ObstaclePhaseMixing (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ k : ℕ,
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), deadMix b C h n m t ≤
          K * (N : ℝ) ^ 2 * W N

/-- Pairwise form of the telescope: `E‖E[B_m | w_{s_n}]‖ ≤ Σ_t E‖E[D_t | w_{s_n}]‖ + error`. -/
theorem biasMix_le_deadMix (b C : ℕ) (hb : 1 ≤ b) (h : ℤ) {n m : ℕ} (hnm : n ≤ m) (k : ℕ) :
    biasMix b C h n m ≤ ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), deadMix b C h n m t +
      4 * Real.pi * |h * (b : ℝ) ^ m| / 3 ^ (10 * (stageOf b C m + k)) := by
  set s := stageOf b C n
  set E := 4 * Real.pi * |h * (b : ℝ) ^ m| / 3 ^ (10 * (stageOf b C m + k))
  have hs : s ≤ stageOf b C m := stageOf_mono b C hb hnm
  set D : ℕ → List Bool → ℂ := fun t w =>
    condMean (fun ω' => deadCorr (h * (b : ℝ) ^ m) (buildU t ω')) s w
  have hpt : ∀ ω, ‖condMean (localBias b C h m) s (buildU s ω)‖ ≤
      ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), ‖D t (buildU s ω)‖ + E := by
    intro ω
    have h1 := norm_condMean_localBias_add_le b C h m hs (buildU s ω) k
    have h2 := norm_sum_le (Finset.Ico (stageOf b C m) (stageOf b C m + k))
      (fun t => D t (buildU s ω))
    have h3 := norm_sub_le (condMean (localBias b C h m) s (buildU s ω) +
      ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), D t (buildU s ω))
      (∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), D t (buildU s ω))
    rw [add_sub_cancel_right] at h3
    linarith
  have hint : ∀ t, Integrable (fun ω => ‖D t (buildU s ω)‖) coinMeasure := fun t =>
    (integrable_comp_buildU s (D t)).norm
  have hsum : Integrable (fun ω => ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k),
      ‖D t (buildU s ω)‖ + E) coinMeasure :=
    (integrable_finset_sum _ fun t _ => hint t).add (integrable_const E)
  unfold biasMix
  refine (integral_mono (integrable_comp_buildU s (condMean (localBias b C h m) s)).norm
    hsum hpt).trans (le_of_eq ?_)
  rw [integral_add (integrable_finset_sum _ fun t _ => hint t) (integrable_const E),
    integral_finset_sum _ fun t _ => hint t]
  simp [deadMix, D, s]

/-- **Obstacle-phase node ⇒ mixing node.**  Proved (telescope, then `k → ∞`). -/
theorem localBiasMixing_of_obstaclePhase {b : ℕ} (hb : 2 ≤ b) (hO : ObstaclePhaseMixing b) :
    LocalBiasMixing b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hO h hh C
  refine ⟨K, W, hW, fun N hN => ?_⟩
  set A : ℝ := (N : ℝ) ^ 2 * (4 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ N)) with hA
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hbound : ∀ k : ℕ, ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m, biasMix b C h n m ≤
      K * (N : ℝ) ^ 2 * W N + A * (1 / 3 ^ 10) ^ k := by
    intro k
    have herr : ∀ m ∈ Finset.range N, 4 * Real.pi * |h * (b : ℝ) ^ m| /
        3 ^ (10 * (stageOf b C m + k)) ≤ 4 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ N) * (1 / 3 ^ 10) ^ k := by
      intro m hm
      have hmN : m ≤ N := (Finset.mem_range.1 hm).le
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ m)]
      have hbm : (b : ℝ) ^ m ≤ (b : ℝ) ^ N := pow_le_pow_right₀ hb1 hmN
      have h3 : (3 : ℝ) ^ (10 * k) ≤ 3 ^ (10 * (stageOf b C m + k)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have e : (1 / (3 : ℝ) ^ 10) ^ k = 1 / 3 ^ (10 * k) := by rw [one_div_pow, ← pow_mul]
      rw [e, mul_one_div]
      have hp : (0 : ℝ) < 3 ^ (10 * k) := by positivity
      calc 4 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ m) / 3 ^ (10 * (stageOf b C m + k))
          ≤ 4 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ m) / 3 ^ (10 * k) :=
            div_le_div_of_nonneg_left (by positivity) hp h3
        _ ≤ 4 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ N) / 3 ^ (10 * k) := by gcongr
    set e := 4 * Real.pi * (|(h : ℝ)| * (b : ℝ) ^ N) * (1 / 3 ^ 10) ^ k
    have he0 : 0 ≤ e := by positivity
    calc ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m, biasMix b C h n m
        ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
            (∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), deadMix b C h n m t + e) := by
          refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => ?_
          exact (biasMix_le_deadMix b C (by omega) h (Finset.mem_range.1 hn).le k).trans
            (by linarith [herr m hm])
      _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
            ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), deadMix b C h n m t +
            ∑ m ∈ Finset.range N, (m : ℝ) * e := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ K * (N : ℝ) ^ 2 * W N + ∑ m ∈ Finset.range N, (N : ℝ) * e := by
          gcongr with m hm
          · exact hK N hN k
          · exact_mod_cast (Finset.mem_range.1 hm).le
      _ = K * (N : ℝ) ^ 2 * W N + A * (1 / 3 ^ 10) ^ k := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hA]; ring
  have ht : Tendsto (fun k : ℕ => K * (N : ℝ) ^ 2 * W N + A * (1 / 3 ^ 10) ^ k) atTop
      (𝓝 (K * (N : ℝ) ^ 2 * W N)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3 ^ 10)
      (by norm_num)).const_mul A
    simpa using this.const_add (K * (N : ℝ) ^ 2 * W N)
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

/-- **Stages above the scale of `bᵐ` are geometrically negligible.** -/
theorem deadMix_le (b C : ℕ) (hb : 1 ≤ b) (h : ℤ) (n m t : ℕ) (ht : stageOf b C m ≤ t) :
    deadMix b C h n m t ≤
      2048 * Real.pi * |(h : ℝ)| * 3 ^ (C + 10) * (1 / 3 ^ 10) ^ (t - stageOf b C m) := by
  set a := stageOf b C m
  set ξ : ℝ := h * (b : ℝ) ^ m
  have hp : (0 : ℝ) < 3 ^ (10 * t) := by positivity
  have hξ : |ξ| / 3 ^ (10 * t) ≤ |(h : ℝ)| * 3 ^ (C + 10) * (1 / 3 ^ 10) ^ (t - a) := by
    have h1 := pow_le_stage b C m hb
    have e : (1 / (3 : ℝ) ^ 10) ^ (t - a) = 3 ^ (10 * a) / 3 ^ (10 * t) := by
      rw [one_div_pow, ← pow_mul, eq_div_iff hp.ne', ← pow_sub_mul_pow 3 (by omega : 10 * a ≤ 10 * t)]
      rw [show 10 * t - 10 * a = 10 * (t - a) by omega]
      field_simp
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ m), div_le_iff₀ hp]
    rw [show |(h : ℝ)| * 3 ^ (C + 10) * (3 ^ (10 * a) / 3 ^ (10 * t)) * 3 ^ (10 * t) =
      |(h : ℝ)| * (3 ^ (C + 10) * 3 ^ (10 * a)) by field_simp]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hB : ∀ ω, ‖deadCorr ξ (buildU t ω)‖ ≤ 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * t)) := by
    intro ω
    unfold deadCorr
    rw [norm_mul, norm_mul, norm_ee, one_mul]
    have := norm_deadErr_le ξ (buildU t ω)
    rw [length_buildU] at this
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_muK_le _)).trans this
  unfold deadMix
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (integrable_const (1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * t))))
    (Eventually.of_forall fun ω => norm_condMean_le (by positivity) hB _ _)).trans ?_
  simp only [integral_const, probReal_univ, one_smul]
  have e2 : 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * t)) = 2048 * Real.pi * (|ξ| / 3 ^ (10 * t)) := by
    ring
  rw [e2]
  have := mul_le_mul_of_nonneg_left hξ (by positivity : (0 : ℝ) ≤ 2048 * Real.pi)
  linarith

/-- **Near-scale obstacle-phase node.**  `ObstaclePhaseMixing` restricted to the
`⌊log₃ N⌋ + 1` stages at and just above the scale of `bᵐ`; the higher stages are negligible
(`deadMix_le`).  Implies `ObstaclePhaseMixing b` (`obstaclePhaseMixing_of_near`).  Believed 50%
for `3 ∤ b`; same content and guards as `ObstaclePhaseMixing`. -/
def NearObstaclePhaseMixing (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)), deadMix b C h n m t ≤
          K * (N : ℝ) ^ 2 * W N

theorem deadMix_nonneg (b C : ℕ) (h : ℤ) (n m t : ℕ) : 0 ≤ deadMix b C h n m t :=
  integral_nonneg fun _ => norm_nonneg _

/-- **Near-scale node ⇒ obstacle-phase node.**  Proved (geometric tail). -/
theorem obstaclePhaseMixing_of_near {b : ℕ} (hb : 2 ≤ b) (hO : NearObstaclePhaseMixing b) :
    ObstaclePhaseMixing b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hO h hh C
  set c : ℝ := 2048 * Real.pi * |(h : ℝ)| * 3 ^ (C + 10) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨1, fun N => K * W N + 2 * c * (N : ℝ) ^ (-(1 : ℝ)),
    hW.mul_left K |>.add ((summable_sched_rpow one_pos).mul_left (2 * c)), fun N hN k => ?_⟩
  set R := Nat.log 3 N + 1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- geometric tail per pair
  have htail : ∀ m n, ∑ t ∈ Finset.Ico (stageOf b C m + R) (stageOf b C m + max k R),
      deadMix b C h n m t ≤ 2 * c / N := by
    intro m n
    set a := stageOf b C m
    have hR : (N : ℝ) < 3 ^ R := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
    calc ∑ t ∈ Finset.Ico (a + R) (a + max k R), deadMix b C h n m t
        ≤ ∑ t ∈ Finset.Ico (a + R) (a + max k R), c * (1 / 3 ^ 10) ^ (t - a) :=
          Finset.sum_le_sum fun t ht => (deadMix_le b C (by omega) h n m t
            (by have := (Finset.mem_Ico.1 ht).1; omega)).trans (le_of_eq (by rw [hc]))
      _ = ∑ j ∈ Finset.range (max k R - R), c * (1 / 3 ^ 10) ^ (R + j) := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr (by congr 1; omega) fun j _ => by congr 2; omega
      _ = c * (1 / 3 ^ 10) ^ R * ∑ j ∈ Finset.range (max k R - R), (1 / 3 ^ 10 : ℝ) ^ j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
      _ ≤ c * (1 / 3 ^ 10) ^ R * 2 := by
          gcongr
          rw [geom_sum_eq (by norm_num)]
          have : (0 : ℝ) ≤ (1 / 3 ^ 10) ^ (max k R - R) := by positivity
          rw [div_le_iff_of_neg (by norm_num)]
          nlinarith
      _ ≤ 2 * c / N := by
          have h1 : (1 / (3 : ℝ) ^ 10) ^ R ≤ 1 / 3 ^ R := by
            rw [one_div_pow, ← pow_mul]
            exact one_div_le_one_div_of_le (by positivity)
              (pow_le_pow_right₀ (by norm_num) (by nlinarith))
          have h2 : (1 : ℝ) / 3 ^ R ≤ 1 / N := one_div_le_one_div_of_le hN0 hR.le
          have := mul_le_mul_of_nonneg_left (h1.trans h2) hc0
          rw [show 2 * c / N = c * (1 / N) * 2 by ring]
          nlinarith
  have hsplit : ∀ m n, ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), deadMix b C h n m t ≤
      ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + R), deadMix b C h n m t + 2 * c / N := by
    intro m n
    set a := stageOf b C m
    have hsub : Finset.Ico a (a + k) ⊆ Finset.Ico a (a + max k R) :=
      Finset.Ico_subset_Ico le_rfl (by omega)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => deadMix_nonneg _ _ _ _ _ _).trans ?_
    rw [← Finset.sum_Ico_consecutive _ (by omega : a ≤ a + R) (by omega : a + R ≤ a + max k R)]
    linarith [htail m n]
  calc ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + k), deadMix b C h n m t
      ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        (∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + R), deadMix b C h n m t + 2 * c / N) :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => hsplit m n
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + R), deadMix b C h n m t +
        ∑ m ∈ Finset.range N, (m : ℝ) * (2 * c / N) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ K * (N : ℝ) ^ 2 * W N + ∑ m ∈ Finset.range N, (N : ℝ) * (2 * c / N) := by
        gcongr with m hm
        · exact hK N hN
        · exact_mod_cast (Finset.mem_range.1 hm).le
    _ = 1 * (N : ℝ) ^ 2 * (K * W N + 2 * c * (N : ℝ) ^ (-(1 : ℝ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.rpow_neg_one]
        field_simp

/-! ### Generic re-telescope against the uniform continuation

For any function `G` of the stage-`(s+k)` prefix, `E_res[G(w_{s+k}) | w_s]` is the uniform
(Cantor) continuation average `cExt G k (w_s)` minus the alive defects of the intermediate
stages.  Applied to `G = D_t` this splits the near-scale crux into a pure Cantor-measure term
and defect terms at the stages between `s_n` and `t`. -/

/-- Uniform average over the next block. -/
noncomputable def unifAvg (H : List Bool → ℂ) (w : List Bool) : ℂ :=
  (1 / 1024 : ℂ) * ∑ f : Fin 10 → Bool, H (w ++ List.ofFn f)

/-- Average over the alive next blocks (the `resLaw` transition). -/
noncomputable def aliveAvg (H : List Bool → ℂ) (w : List Bool) : ℂ :=
  (1 / ((aliveSet w).card : ℂ)) * ∑ f ∈ aliveSet w, H (w ++ List.ofFn f)

/-- The alive defect: uniform minus alive average of the next block. -/
noncomputable def aliveDefect (H : List Bool → ℂ) (w : List Bool) : ℂ :=
  unifAvg H w - aliveAvg H w

/-- The uniform continuation by `k` blocks. -/
noncomputable def cExt (G : List Bool → ℂ) : ℕ → List Bool → ℂ
  | 0 => G
  | k + 1 => cExt (unifAvg G) k

/-- **One `resLaw` transition** (uniform resampling: `real_child`). -/
theorem condMean_succ_alive (H : List Bool → ℂ) {s r : ℕ} (hsr : s ≤ r) (w : List Bool) :
    condMean (fun ω => H (buildU (r + 1) ω)) s w =
      condMean (fun ω => aliveAvg H (buildU r ω)) s w := by
  classical
  unfold condMean
  congr 1
  refine setIntegral_eq_of_atoms (S := r) hsr (integrable_comp_buildU (r + 1) _)
    (integrable_comp_buildU r _) (fun v hv => ?_) w
  rw [setIntegral_buildU_succ r hv]
  rw [setIntegral_congr_fun (mset_buildU' r v) (g := fun _ => aliveAvg H v)
    (fun ω hω => by simp only [Set.mem_setOf_eq] at hω; simp only [hω]), setIntegral_const]
  simp only [real_child r v (length_of_mem_LS hv), ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  unfold aliveAvg
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **The generic re-telescope.** -/
theorem condMean_cExt_telescope (s : ℕ) (w : List Bool) (k : ℕ) :
    ∀ G : List Bool → ℂ, condMean (fun ω => G (buildU (s + k) ω)) s w =
      condMean (fun ω => cExt G k (buildU s ω)) s w -
        ∑ j ∈ Finset.range k,
          condMean (fun ω => aliveDefect (cExt G j) (buildU (s + k - 1 - j) ω)) s w := by
  induction k with
  | zero => intro G; simp [cExt]
  | succ k ih =>
    intro G
    have hstep : condMean (fun ω => G (buildU (s + (k + 1)) ω)) s w =
        condMean (fun ω => unifAvg G (buildU (s + k) ω)) s w -
          condMean (fun ω => aliveDefect G (buildU (s + k) ω)) s w := by
      rw [show s + (k + 1) = s + k + 1 from rfl, condMean_succ_alive G (Nat.le_add_right s k),
        ← condMean_sub (integrable_comp_buildU _ _) (integrable_comp_buildU _ _)]
      congr 1; funext ω; simp [aliveDefect]
    rw [hstep, ih (unifAvg G), Finset.sum_range_succ']
    simp only [cExt]
    have e : ∀ j ∈ Finset.range k, condMean (fun ω => aliveDefect (cExt (unifAvg G) j)
        (buildU (s + k - 1 - j) ω)) s w = condMean (fun ω => aliveDefect (cExt (unifAvg G) j)
        (buildU (s + (k + 1) - 1 - (j + 1)) ω)) s w := fun j _ => by
      rw [show s + (k + 1) - 1 - (j + 1) = s + k - 1 - j by omega]
    rw [Finset.sum_congr rfl e, show s + (k + 1) - 1 - 0 = s + k by omega]
    ring

/-! ### The periodic obstacles: a Riesz-product sub-family

The periodic points `P/(3^ℓ−1)` of `K` (digits of `P` in `{0,2}`) lie on `K`, so they are
obstacles at every stage whose denominator range contains `3^ℓ − 1`.  Their phase sum at a
frequency `ξ` is a Riesz product (`periodic_phase_sum`), and for `ξ = h·3ᵐ` it does not depend on
`m` (`riesz_three_shift`): the obstacle phases of this family are coherent in base 3, consistent
with `not_casselsRate_three`.  The family has about `2^ℓ` members against about `4^ℓ` obstacles
at that scale, so it is lower order in the crux. -/

/-- The integer with ternary digits `2·d i` (`i < ℓ`, least significant first). -/
def perNum {ℓ : ℕ} (d : Fin ℓ → Bool) : ℕ := ∑ i : Fin ℓ, (if d i then 2 else 0) * 3 ^ (i : ℕ)

/-- The Riesz product `∏_{i<ℓ} (1 + e(2x3^i))`. -/
noncomputable def riesz (ℓ : ℕ) (x : ℝ) : ℂ := ∏ i ∈ Finset.range ℓ, (1 + ee (2 * x * 3 ^ i))

/-- **The periodic phase sum is a Riesz product.** -/
theorem periodic_phase_sum (ℓ : ℕ) (x : ℝ) :
    ∑ d : Fin ℓ → Bool, ee (x * perNum d) = riesz ℓ x := by
  unfold riesz perNum
  rw [← Fin.prod_univ_eq_prod_range (fun i => 1 + ee (2 * x * 3 ^ i))]
  have : ∀ d : Fin ℓ → Bool, ee (x * ((∑ i : Fin ℓ, (if d i then 2 else 0) * 3 ^ (i : ℕ) : ℕ) : ℝ)) =
      ∏ i : Fin ℓ, (if d i then ee (2 * x * 3 ^ (i : ℕ)) else 1) := by
    intro d
    push_cast
    rw [Finset.mul_sum]
    induction (Finset.univ : Finset (Fin ℓ)) using Finset.induction_on with
    | empty => simp [ee]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, ee_add, ih]
      congr 1
      split_ifs <;> simp [ee] <;> ring_nf
  simp_rw [this]
  rw [← Fintype.prod_sum (fun (i : Fin ℓ) (c : Bool) => if c then ee (2 * x * 3 ^ (i : ℕ)) else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [add_comm]

theorem ee_add_int (x : ℝ) (k : ℤ) : ee (x + k) = ee x := by
  rw [ee_add]
  have : ee (k : ℝ) = 1 := by
    have := ee_int_mul_fract k 1
    simpa [ee] using this.symm
  rw [this, mul_one]

/-- **Base-3 coherence of the periodic family**: at `x = a/(3^ℓ−1)` the Riesz product is invariant
under `x ↦ 3x`, so at the frequencies `h·3ᵐ` it does not decay in `m`. -/
theorem riesz_three_shift (ℓ : ℕ) (a : ℤ) :
    riesz ℓ (3 * (a / (3 ^ ℓ - 1))) = riesz ℓ (a / (3 ^ ℓ - 1)) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp [riesz]
  set x : ℝ := a / (3 ^ ℓ - 1)
  have hd : (3 : ℝ) ^ ℓ - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ 3 ^ ℓ := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hℓ
    linarith
  have hx : 2 * x * 3 ^ ℓ = 2 * x + ((2 * a : ℤ) : ℝ) := by
    have : x * (3 ^ ℓ - 1) = a := by unfold x; field_simp
    push_cast; linear_combination 2 * this
  unfold riesz
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  rw [Finset.prod_range_succ, Finset.prod_range_succ']
  have e1 : ∀ i ∈ Finset.range k, (1 + ee (2 * (3 * x) * 3 ^ i)) = (1 + ee (2 * x * 3 ^ (i + 1))) :=
    fun i _ => by congr 2; ring
  rw [Finset.prod_congr rfl e1, show 2 * (3 * x) * 3 ^ k = 2 * x * 3 ^ (k + 1) by ring, hx,
    ee_add_int]
  simp

/-- **Every obstacle phase family recurs in `m`.**  For any modulus `n > 0`, the phases
`e(a bᵐ / n)` (`a ∈ ℤ`) are eventually periodic in `m`.  Proved (pigeonhole on `bᵐ mod n`).

Use for `ObstaclePairCorrelation` (lap 10).  The `m`-scan (`L = 12`, `S = 4`, `b = 2`, `h = 1`,
`m ∈ [5, 200)`, `scripts/cantorbad_mscan.py`) has median ratio `.003` and outliers `m = 184, 185,
111` at `.128, .106, .080`, led by obstacles whose 3-free denominator is `244 = 3⁵+1`,
`364 = (3⁶−1)/2`, `730 = 3⁶+1`, `205 | 3⁸−1`, `1093 = (3⁷−1)/2` (at the typical `m = 60` no class
exceeds `.001`).  These are preperiodic `p/(q'3^j)`: their phase is fixed by `hbᵐ mod q'` (eventually
periodic in `m`, this lemma) and by the low ternary digits `hbᵐ mod 3^j`.  Purely periodic
obstacles of bounded period do not occur at large `L` (`q² ≥ 3^{L−5}`), so any recurrent coherence
must pass through the 3-adic factor, which is where `3 ∤ b` enters. -/
theorem pow_phase_recur (b n : ℕ) (hn : 0 < n) : ∃ m₀ T : ℕ, 0 < T ∧ ∀ m, m₀ ≤ m → ∀ a : ℤ,
    ee (a * (b : ℝ) ^ (m + T) / n) = ee (a * (b : ℝ) ^ m / n) := by
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (n + 1) => (⟨b ^ (i : ℕ) % n, Nat.mod_lt _ hn⟩ : Fin n)) (by simp)
  simp only [Fin.mk.injEq] at he
  have key : ∀ i j : ℕ, i < j → b ^ i % n = b ^ j % n → ∃ m₀ T : ℕ, 0 < T ∧ ∀ m, m₀ ≤ m →
      ∀ a : ℤ, ee (a * (b : ℝ) ^ (m + T) / n) = ee (a * (b : ℝ) ^ m / n) := by
    intro i j hij he
    refine ⟨i, j - i, by omega, fun m hm a => ?_⟩
    have hmod : ((b ^ (m + (j - i)) : ℕ) : ℤ) ≡ ((b ^ m : ℕ) : ℤ) [ZMOD n] := by
      have h1 : b ^ (m + (j - i)) = b ^ (m - i) * b ^ j := by
        rw [← pow_add]; congr 1; omega
      have h2 : b ^ m = b ^ (m - i) * b ^ i := by rw [← pow_add]; congr 1; omega
      rw [h1, h2]
      exact Int.natCast_modEq_iff.mpr
        (Nat.ModEq.mul_left (b ^ (m - i)) (show b ^ j ≡ b ^ i [MOD n] from he.symm))
    obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hmod.symm)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : a * (b : ℝ) ^ (m + (j - i)) / n = a * (b : ℝ) ^ m / n + ((a * k : ℤ) : ℝ) := by
      have hk' : ((b ^ (m + (j - i)) : ℕ) : ℝ) - ((b ^ m : ℕ) : ℝ) = n * k := by exact_mod_cast hk
      push_cast at hk' ⊢
      field_simp
      linear_combination a * hk'
    rw [this, ee_add_int]
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with h | h
  · exact key _ _ h he
  · exact key _ _ h he.symm

/-- **CRT split of an obstacle phase.**  For `q'` prime to 3 the phase of `p/(q'3^j)` factors as a
`q'`-part times a 3-adic part: `e(B p/(q'3^j)) = e(B a/q')·e(B c/3^j)`, with `a, c` independent of
`B`.  The `q'`-part is eventually periodic in `B = hbᵐ` (`pow_phase_recur`); the 3-adic part is a
character of the low ternary digits of `hbᵐ`, the factor that must supply the cancellation for the
preperiodic families (`PeriodicFamilyShare`).  Proved (Bézout). -/
theorem obstacle_phase_crt (p : ℤ) {q' : ℕ} (j : ℕ) (hq : Nat.Coprime q' 3) (hq0 : 0 < q') :
    ∃ a c : ℤ, ∀ B : ℝ, ee (B * (p / ((q' : ℝ) * 3 ^ j))) = ee (B * (a / q')) * ee (B * (c / 3 ^ j)) := by
  have hc : IsCoprime (q' : ℤ) ((3 : ℤ) ^ j) := by
    have : Nat.Coprime q' (3 ^ j) := Nat.Coprime.pow_right _ hq
    have h := Nat.isCoprime_iff_coprime.mpr this
    simpa using h
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨p * v, p * u, fun B => ?_⟩
  rw [← ee_add]
  congr 1
  have h1 : (u : ℝ) * q' + v * 3 ^ j = 1 := by exact_mod_cast huv
  have hq' : (q' : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  push_cast
  field_simp
  linear_combination (-(B * p)) * h1

/-- **Conjecture node: 3-adic window cancellation along `hbᵐ`.**  Believed 70% for `3 ∤ b`.  For
every depth `j` below the top of `hbᵐ`, the Riesz majorant of the `M = ⌊log₃ N⌋/2` ternary digits of
`hbᵐ` just below position `j` is small on average over `m < N`.  This is the 3-adic factor of
`obstacle_phase_crt` for the preperiodic obstacle families (`PeriodicFamilyShare`); a single-sum
analogue of `cassels_Bf`.  Fails for `b = 3` (`hbᵐ ≡ 0 mod 3^j` for `m ≥ j`, every factor is 1).
Shallow depths (`3^j ≤ N`, period of `b mod 3^j` at most `N`) reduce to exact equidistribution of
`bᵐ` in its subgroup mod `3^j`; deep `j` is an Erdős-ternary-type digit statement (open).
Literature route (lap 10, not yet read in full): the windows are Korobov-type sums
`Σ_{m<N} e(a bᵐ/3^k)`, `k ≤ j`; modulo a power of a fixed prime, Postnikov (1956) turns `bᵐ` into a
3-adic polynomial in `m` and Vinogradov's mean value theorem gives nontrivial bounds for `N` much
shorter than `3^k` (cf. arXiv:1606.07911, arXiv:1605.07553).  Whether the admissible range reaches
`k ≍ N log₃ b` (the depth of the obstacle families) is the question to check; it plausibly covers
only `k ≲ (log N)^{O(1)}`.
Evidence (`scripts/cantorbad_3adicwin.py`, `N = 3⁸`, `M = 4`, `h = 1`, `j = 4..64`): means `.13–.18`
for `b = 2, 5, 7`, matching the random-digit value `(2/π)⁴ ≈ .164` (a power saving `N^{−c}`); control
`b = 3`: `1.0` at every `j`. -/
def ThreeAdicWindowAvg (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N j : ℕ, 1 ≤ N → Nat.log 3 N / 2 ≤ j →
      ∑ m ∈ (Finset.range N).filter (fun m => j + 1 ≤ Nat.log 3 (b ^ m)),
        CantorLiouville.Bf (fun _ => true) (Nat.log 3 N / 2)
          (h * (b : ℝ) ^ m / 3 ^ (j - Nat.log 3 N / 2)) ≤ C * N * W N

/-- **Base-3 control for `ThreeAdicWindowAvg`.**  Refuted for `b = 3`: every window of `3ᵐ` below
its top is zero, so each Riesz factor is 1 and the sum is `≍ N`.  Proved. -/
theorem not_threeAdicWindowAvg_three : ¬ ThreeAdicWindowAvg 3 := by
  intro H
  obtain ⟨C, W, hW, hC⟩ := H 1 one_ne_zero
  have key : ∀ N : ℕ, 3 ≤ N → (1 : ℝ) / 3 ≤ C * W N := by
    intro N hN
    obtain ⟨M, hM⟩ : ∃ M, M = Nat.log 3 N / 2 := ⟨_, rfl⟩
    have h1 := hC N M (by omega) (by omega)
    rw [← hM] at h1
    simp only [Nat.cast_ofNat] at h1
    have hterm : ∀ m ∈ (Finset.range N).filter (fun m => M + 1 ≤ Nat.log 3 (3 ^ m)),
        CantorLiouville.Bf (fun _ => true) M (((1 : ℤ) : ℝ) * (3 : ℝ) ^ m / 3 ^ (M - M)) = 1 := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range, Nat.log_pow (by norm_num : 1 < 3)] at hm
      unfold CantorLiouville.Bf
      refine Finset.prod_eq_one fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hpm : p + 1 ≤ m := by omega
      have : 2 * Real.pi * (((1 : ℤ) : ℝ) * (3 : ℝ) ^ m / 3 ^ (M - M)) / 3 ^ (p + 1) =
          ((3 ^ (m - (p + 1)) : ℕ) : ℝ) * (2 * Real.pi) := by
        rw [Nat.sub_self, pow_zero, div_one, Int.cast_one, one_mul]
        have : (3 : ℝ) ^ m = 3 ^ (m - (p + 1)) * 3 ^ (p + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; push_cast; field_simp
      rw [this, Real.cos_nat_mul_two_pi, abs_one]
    have hfil : (Finset.range N).filter (fun m => M + 1 ≤ Nat.log 3 (3 ^ m)) =
        Finset.Ico (M + 1) N := by
      ext m; simp [Nat.log_pow (by norm_num : 1 < 3)]; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hfil, Nat.card_Ico, nsmul_eq_mul,
      mul_one] at h1
    have hl : Nat.log 3 N < N := Nat.log_lt_self 3 (by omega)
    have hc : (N : ℝ) / 3 ≤ ((N - (M + 1) : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]
      exact_mod_cast (show N ≤ (N - (M + 1)) * 3 by omega)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have : (N : ℝ) / 3 ≤ C * N * W N := hc.trans h1
    have : (N : ℝ) * (1 / 3) ≤ (N : ℝ) * (C * W N) := by linarith
    exact le_of_mul_le_mul_left this hN0
  have ht := (hW.mul_left C).tendsto_atTop_zero
  have hev : ∀ᶠ k in atTop, (1 : ℝ) / 3 ≤ C * W (sched k) := by
    filter_upwards [(CantorLiouville.sched_strictMono.tendsto_atTop).eventually_ge_atTop 3] with k hk
    exact key _ hk
  have := ge_of_tendsto ht hev
  norm_num at this

open Classical in
/-- The obstacle rationals charged to a prefix of length `L` (as in `Alive` with `r = 5`):
`p/q ∈ [0, 1]`, `3^L ≤ q²3⁵ < 3^{L+10}`, within `2c₀/q²` of `K`. -/
noncomputable def obst (L : ℕ) : Finset (ℤ × ℕ) :=
  ((Finset.Icc (0 : ℤ) (3 ^ (L + 10))) ×ˢ Finset.range (3 ^ (L + 10) + 1)).filter fun x =>
    0 < x.2 ∧ x.1 ≤ x.2 ∧ (3 : ℝ) ^ L ≤ (x.2 : ℝ) ^ 2 * 3 ^ 5 ∧
      (x.2 : ℝ) ^ 2 * 3 ^ 5 < 3 ^ (L + 10) ∧
      ∃ y ∈ cantorSet, |y - (x.1 : ℝ) / x.2| < 2 * c₀ / (x.2 : ℝ) ^ 2

/-- The value of an obstacle. -/
noncomputable def oval (x : ℤ × ℕ) : ℝ := (x.1 : ℝ) / x.2

open Classical in
/-- Pairs of distinct obstacles at length `L` within `3^{−S}` of each other. -/
noncomputable def obstPairs (L S : ℕ) : Finset ((ℤ × ℕ) × (ℤ × ℕ)) :=
  (obst L ×ˢ obst L).filter fun xy => oval xy.1 ≠ oval xy.2 ∧ |oval xy.1 - oval xy.2| ≤ 1 / 3 ^ S

/-- **Conjecture node: twisted pair correlation of the rationals near `K`.**  Believed 45% for
`3 ∤ b`.  At the frequency `ξ = hbᵐ` and the obstacle length `L = 10 s_m` (the scale of `bᵐ`),
the off-diagonal pair sum `Σ e(ξ(x − y))` over distinct obstacles within `3^{−S}` is `o` of the
number of such pairs as `L − S → ∞`, uniformly in `m`.

Role.  To first order (the `cExt` term of `condMean_cExt_telescope`, `1/|A| ≈ 1/1024`),
`E[D_t | w_s]` is a μ_K-weighted sum of `e(ξ p/q)` over the obstacles in the cylinder `w_s`
(each obstacle has radius below a third of a child width, so it kills at most two children);
Cauchy–Schwarz over the cylinders bounds `deadMix` by the diagonal plus this off-diagonal sum.
The implication to `NearObstaclePhaseMixing` is not proved: the second-order (two dead stages)
terms and the μ_K weights are not controlled.  Phase gaps are multiples of `ξ/(qq') ≳ 3^C`, so
this is Farey-scale pair correlation near a fractal; for all rationals in an interval it is known
(Boca–Cobeli–Zaharescu), near `K` it is open.  Base-3 control: the periodic points of `K` are a
sub-family whose phase sum is a Riesz product constant along `h·3ᵐ` (`riesz_three_shift`).

Evidence (`scripts/cantorbad_paircorr.py`, 2026-10-06).  `L = 12`, `C = 3`, all 7796 obstacles
(pruned Stern–Brocot enumeration), `h = 1`: ratio `|Σ|/#pairs` at `S = 4, 8, 12` is
`.002, .006, .061` (b = 2), `.000, .003, .053` (b = 5), `.000, .001, .020` (b = 7), i.e. square-root
size (`#pairs = 1.9·10⁶, 1.2·10⁵, 6274`).  Known-coherent control `b = 3`: `.163, .167, .134`, flat in
`S`.  So the probe separates the bases prime to 3 from base 3 by two orders of magnitude.
`L = 16` (43572 obstacles), `S = 8, 12, 16`: `.000, .005, .016` (b = 2), `.002, .013, .045` (b = 5),
`.002, .009, .087` (b = 7); control `b = 3`: `.167, .172, .160`.  Same picture one scale up.

Uniformity in `m` (lap 10): sporadic outliers (`m = 184`: `.128`) come from preperiodic
obstacles `p/(q'3^j)`, `q' | 3^ℓ ± 1` (`pow_phase_recur`); their pair share is large
(`PeriodicFamilyShare`, believed false), so the node needs their 3-adic phase to cancel. -/
def ObstaclePairCorrelation (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ m S : ℕ, S + G ≤ 10 * stageOf b C m →
    ‖∑ xy ∈ obstPairs (10 * stageOf b C m) S, ee (h * (b : ℝ) ^ m * (oval xy.1 - oval xy.2))‖ ≤
      ε * (obstPairs (10 * stageOf b C m) S).card

open Classical in
/-- The obstacle pairs at length `L`, window `S`, with an endpoint whose reduced denominator has
3-free part dividing `3^ℓ − 1` or `3^ℓ + 1` (the period-`ℓ` families of `pow_phase_recur`). -/
noncomputable def periodicPairs (ℓ L S : ℕ) : Finset ((ℤ × ℕ) × (ℤ × ℕ)) :=
  (obstPairs L S).filter fun xy => ∃ x ∈ ({xy.1, xy.2} : Finset (ℤ × ℕ)),
    let r : ℚ := (x.1 : ℚ) / x.2
    let d := r.den / 3 ^ padicValNat 3 r.den
    d ∣ 3 ^ ℓ - 1 ∨ d ∣ 3 ^ ℓ + 1

/-- **Conjecture node (believed false, 15%): the preperiodic families have vanishing pair share.**
For each `ℓ`, the share of `obstPairs L S` touching an obstacle whose 3-free denominator divides
`3^ℓ ± 1` tends to 0 as `L → ∞`.  Evidence against (`scripts/cantorbad_famshare.py`, lap 10):
`L = 12, S = 8` shares `.18, .24, .31, .35, .34, .51, .35, .56` for `ℓ = 1..8`.  So
`ObstaclePairCorrelation` cannot discard these families by counting; their cancellation must come
from the 3-adic phase factor `e(hbᵐ p / 3^j)` (a Riesz product over the low ternary digits of
`hbᵐ`), averaged over `m` — the Cassels mechanism, which fails for `b = 3`. -/
def PeriodicFamilyShare : Prop :=
  ∀ ℓ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L S : ℕ, L₀ ≤ L → S ≤ L →
    ((periodicPairs ℓ L S).card : ℝ) ≤ ε * (obstPairs L S).card

/-- First-order (uniform continuation) part of `deadMix`. -/
noncomputable def firstMix (b C : ℕ) (h : ℤ) (n m t : ℕ) : ℝ :=
  ∫ ω, ‖condMean (fun ω' => cExt (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n)
    (buildU (stageOf b C n) ω')) (stageOf b C n) (buildU (stageOf b C n) ω)‖ ∂coinMeasure

/-- Alive-defect part of `deadMix`: the defects of the stages between `s_n` and `t`. -/
noncomputable def defectMix (b C : ℕ) (h : ℤ) (n m t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (t - stageOf b C n),
    ∫ ω, ‖condMean (fun ω' => aliveDefect (cExt (deadCorr (h * (b : ℝ) ^ m)) j)
      (buildU (stageOf b C n + (t - stageOf b C n) - 1 - j) ω')) (stageOf b C n)
      (buildU (stageOf b C n) ω)‖ ∂coinMeasure

/-- **`deadMix` splits into first-order and defect parts.**  Proved (`condMean_cExt_telescope`). -/
theorem deadMix_le_first_add_defect (b C : ℕ) (h : ℤ) (n m t : ℕ) (ht : stageOf b C n ≤ t) :
    deadMix b C h n m t ≤ firstMix b C h n m t + defectMix b C h n m t := by
  set s := stageOf b C n
  set k := t - s
  set G := deadCorr (h * (b : ℝ) ^ m)
  have hk : s + k = t := by omega
  set A : List Bool → ℂ := fun w => condMean (fun ω' => cExt G k (buildU s ω')) s w
  set B : ℕ → List Bool → ℂ := fun j w =>
    condMean (fun ω' => aliveDefect (cExt G j) (buildU (s + k - 1 - j) ω')) s w
  have hpt : ∀ ω, ‖condMean (fun ω' => G (buildU t ω')) s (buildU s ω)‖ ≤
      ‖A (buildU s ω)‖ + ∑ j ∈ Finset.range k, ‖B j (buildU s ω)‖ := by
    intro ω
    have tel := condMean_cExt_telescope s (buildU s ω) k G
    rw [← hk, tel]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have hA : Integrable (fun ω => ‖A (buildU s ω)‖) coinMeasure := (integrable_comp_buildU s A).norm
  have hB : ∀ j, Integrable (fun ω => ‖B j (buildU s ω)‖) coinMeasure := fun j =>
    (integrable_comp_buildU s (B j)).norm
  have hsum : Integrable (fun ω => ‖A (buildU s ω)‖ + ∑ j ∈ Finset.range k, ‖B j (buildU s ω)‖)
      coinMeasure := hA.add (integrable_finset_sum _ fun j _ => hB j)
  unfold deadMix
  refine (integral_mono (integrable_comp_buildU s _).norm hsum hpt).trans (le_of_eq ?_)
  rw [integral_add hA (integrable_finset_sum _ fun j _ => hB j),
    integral_finset_sum _ fun j _ => hB j]
  rfl

/-- **First-order obstacle node.**  Believed 50% for `3 ∤ b`.  The uniform-continuation part:
a μ_K average over the cylinder `w_{s_n}` of the phased dead corrections at stage `t`, i.e. (to
first order) a weighted sum of `e(hbᵐ p/q)` over the obstacles in the cylinder; see
`ObstaclePairCorrelation` for the pair-correlation form and its evidence. -/
def FirstOrderObstacleMix (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)), firstMix b C h n m t ≤
          K * (N : ℝ) ^ 2 * W N

/-- **Alive-defect node.**  Believed 45% for `3 ∤ b`.  The defect part: each term is localized at a
stage between `s_n` and `t` that has dead children, applied to the uniform continuation of the
stage-`t` dead correction.  Second order in the dead density, but with no decay in `N` proved.

Lap 9 analysis (not a theorem).  The norm-inside bound (`norm_aliveDefect_le` + `AvgDeadDensity`)
cannot prove this node: the `j = 0` term is then `≈ E[#dead_{t−1}·#dead_t]/1024²` per triple
`(n, m, t)`, with no decay in `m − n`, so the triple sum is `≍ N² log N`, not `O(N² W(N))`.  The
defect terms need phase cancellation in the conditional mean given `w_{s_n}`, exactly as the
first-order term does: each `gMix (aliveDefect (cExt G j)) (t−1−j) s_n` has the same shape as
`deadMix` and re-telescopes by `gMix_le` into its own first-order cylinder average plus deeper
defects.  So the natural route is one uniform cylinder-cancellation statement for the whole family
of phased stage functions generated by `aliveDefect` and `cExt` from `deadCorr`. -/
def DefectObstacleMix (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)), defectMix b C h n m t ≤
          K * (N : ℝ) ^ 2 * W N

/-- **First-order and defect nodes ⇒ near-scale node.**  Proved. -/
theorem nearObstaclePhaseMixing_of_split {b : ℕ} (hb : 1 ≤ b) (h1 : FirstOrderObstacleMix b)
    (h2 : DefectObstacleMix b) : NearObstaclePhaseMixing b := by
  intro h hh C
  obtain ⟨K₁, W₁, hW₁, hK₁⟩ := h1 h hh C
  obtain ⟨K₂, W₂, hW₂, hK₂⟩ := h2 h hh C
  refine ⟨1, fun N => K₁ * W₁ N + K₂ * W₂ N, (hW₁.mul_left K₁).add (hW₂.mul_left K₂),
    fun N hN => ?_⟩
  have hle : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range m,
      ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)), deadMix b C h n m t ≤
      ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
        (firstMix b C h n m t + defectMix b C h n m t) := fun m hm n hn =>
    Finset.sum_le_sum fun t ht => deadMix_le_first_add_defect b C h n m t
      ((stageOf_mono b C hb (Finset.mem_range.1 hn).le).trans (Finset.mem_Ico.1 ht).1)
  calc _ ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          (firstMix b C h n m t + defectMix b C h n m t) :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hle m hm n hn
    _ = _ + _ := by simp only [Finset.sum_add_distrib]
    _ ≤ K₁ * (N : ℝ) ^ 2 * W₁ N + K₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add (hK₁ N hN) (hK₂ N hN)
    _ = _ := by ring

/-- **The alive defect is bounded by the dead fraction.**  If every child value is at most `M`,
`|aliveDefect H w| ≤ 2·(#dead/1024)·M`.  Proved.  (So the defect part of the crux carries the
dead density as a factor; the bootstrap must average it, since `#dead ≤ 488` in the worst case.) -/
theorem norm_aliveDefect_le (H : List Bool → ℂ) (w : List Bool) {M : ℝ}
    (hM : ∀ f : Fin 10 → Bool, ‖H (w ++ List.ofFn f)‖ ≤ M) :
    ‖aliveDefect H w‖ ≤ 2 * ((1024 - (aliveSet w).card : ℕ) / 1024 : ℝ) * M := by
  classical
  set A := aliveSet w
  set c := A.card
  have hc0 : (0 : ℝ) < c := by exact_mod_cast card_aliveSet_pos w
  have hc1 : c ≤ 1024 := card_aliveSet_le w
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM fun _ => false)
  set e : (Fin 10 → Bool) → ℂ := fun f => H (w ++ List.ofFn f)
  have hsplit := Finset.sum_sdiff (f := e) (Finset.subset_univ A)
  have hD : (Finset.univ \ A).card = 1024 - c := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; simp [c]
  have key : aliveDefect H w = (1 / 1024 : ℂ) * ∑ f ∈ Finset.univ \ A, e f -
      (((1024 - c : ℕ) : ℂ) / (1024 * c)) * ∑ f ∈ A, e f := by
    unfold aliveDefect unifAvg aliveAvg
    change (1 / 1024 : ℂ) * ∑ f, e f - (1 / (c : ℂ)) * ∑ f ∈ A, e f = _
    rw [← hsplit, Nat.cast_sub hc1]
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    field_simp
    ring
  rw [key]
  have b1 : ‖∑ f ∈ Finset.univ \ A, e f‖ ≤ (1024 - c : ℕ) * M := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ f ∈ Finset.univ \ A, ‖e f‖ ≤ ∑ f ∈ Finset.univ \ A, M := Finset.sum_le_sum fun f _ => hM f
      _ = _ := by rw [Finset.sum_const, hD, nsmul_eq_mul]
  have b2 : ‖∑ f ∈ A, e f‖ ≤ c * M := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ f ∈ A, ‖e f‖ ≤ ∑ f ∈ A, M := Finset.sum_le_sum fun f _ => hM f
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have n1 : ‖(1 / 1024 : ℂ)‖ = 1 / 1024 := by norm_num
  have n2 : ‖(((1024 - c : ℕ) : ℂ) / (1024 * c))‖ = ((1024 - c : ℕ) : ℝ) / (1024 * c) := by
    rw [norm_div, Complex.norm_natCast, norm_mul, Complex.norm_natCast]; norm_num
  rw [n1, n2]
  have hd0 : (0 : ℝ) ≤ ((1024 - c : ℕ) : ℝ) := Nat.cast_nonneg _
  calc 1 / 1024 * ‖∑ f ∈ Finset.univ \ A, e f‖ + ((1024 - c : ℕ) : ℝ) / (1024 * c) * ‖∑ f ∈ A, e f‖
      ≤ 1 / 1024 * ((1024 - c : ℕ) * M) + ((1024 - c : ℕ) : ℝ) / (1024 * c) * (c * M) := by
        gcongr
    _ = 2 * (((1024 - c : ℕ) : ℝ) / 1024) * M := by field_simp; ring

/-- The averaged conditional mean of a stage-`t` function given the stage-`s` prefix. -/
noncomputable def gMix (G : List Bool → ℂ) (t s : ℕ) : ℝ :=
  ∫ ω, ‖condMean (fun ω' => G (buildU t ω')) s (buildU s ω)‖ ∂coinMeasure

/-- **The bootstrap recursion.**  For any stage function `G`, the resLaw mix splits into the
uniform-continuation term plus the mixes of the defect functions `aliveDefect (cExt G j)` at the
earlier stages `t − 1 − j`.  Iterating it expands `gMix` over chains of dead stages, each link
weighted by a dead fraction (`norm_aliveDefect_le`); the expansion converges only with an
averaged dead density (worst case `2·488/1024` per link).  Proved. -/
theorem gMix_le (G : List Bool → ℂ) {s t : ℕ} (ht : s ≤ t) :
    gMix G t s ≤ ∫ ω, ‖condMean (fun ω' => cExt G (t - s) (buildU s ω')) s (buildU s ω)‖ ∂coinMeasure +
      ∑ j ∈ Finset.range (t - s), gMix (aliveDefect (cExt G j)) (t - 1 - j) s := by
  set k := t - s
  have hk : s + k = t := by omega
  set A : List Bool → ℂ := fun w => condMean (fun ω' => cExt G k (buildU s ω')) s w
  set B : ℕ → List Bool → ℂ := fun j w =>
    condMean (fun ω' => aliveDefect (cExt G j) (buildU (s + k - 1 - j) ω')) s w
  have hpt : ∀ ω, ‖condMean (fun ω' => G (buildU t ω')) s (buildU s ω)‖ ≤
      ‖A (buildU s ω)‖ + ∑ j ∈ Finset.range k, ‖B j (buildU s ω)‖ := by
    intro ω
    have tel := condMean_cExt_telescope s (buildU s ω) k G
    rw [← hk, tel]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have hA : Integrable (fun ω => ‖A (buildU s ω)‖) coinMeasure := (integrable_comp_buildU s A).norm
  have hB : ∀ j, Integrable (fun ω => ‖B j (buildU s ω)‖) coinMeasure := fun j =>
    (integrable_comp_buildU s (B j)).norm
  have hsum : Integrable (fun ω => ‖A (buildU s ω)‖ + ∑ j ∈ Finset.range k, ‖B j (buildU s ω)‖)
      coinMeasure := hA.add (integrable_finset_sum _ fun j _ => hB j)
  unfold gMix
  refine (integral_mono (integrable_comp_buildU s _).norm hsum hpt).trans (le_of_eq ?_)
  rw [integral_add hA (integrable_finset_sum _ fun j _ => hB j),
    integral_finset_sum _ fun j _ => hB j]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  simp only [B, show s + k - 1 - j = t - 1 - j by omega]

/-- **Conjecture node: averaged dead density.**  Believed 70%.  After a fixed number `R` of
stages, the conditional expected number of dead children under `resLaw` is at most `κ`, uniformly in
the conditioning prefix.  This is input (ii) of the bootstrap (`gMix_le`, `norm_aliveDefect_le`):
with it, each link of the defect expansion costs about `2κ/1024` on average instead of the worst
case `2·488/1024`.  (The bootstrap also needs this weighted by the iterated first-order factors;
that weighted form is not stated yet.)  Evidence: the lap-6 probe saw about 200,000 dead children in
about 156,000 `resLaw` stages (s ≥ 4; bases 2, 5, 7), i.e. roughly 1.3 per stage on average.  `scripts/cantorbad_deadcount.py` (1500 paths × 25 stages):
stage 0 has 22 dead children (small denominators), stage 1 averages 3.55, stages 2–24 average
1.21–1.33 each; the largest count seen after stage 0 is 9 (once in 36000).  So `R = 2`, `κ ≈ 1.3`
on average; the uniform-in-`w` form is the unverified part.  Heuristic: obstacles at
length `L` within a cylinder of length `L_s ≪ L` number about `c₀·3^{(L−L_s)·log₃2}` children's worth,
and distinct obstacles are separated by `≥ 1/(qq') ≈ 3^{−L}`, so no prefix keeps a large dead count. -/
def AvgDeadDensity : Prop :=
  ∃ (R : ℕ) (κ : ℝ), κ ≤ 8 ∧ ∀ s r : ℕ, s + R ≤ r → ∀ w : List Bool,
    (condMean (fun ω => ((1024 - (aliveSet (buildU r ω)).card : ℕ) : ℂ)) s w).re ≤ κ

/-- Append `k` blocks to `w`. -/
def catB (w : List Bool) : (k : ℕ) → (Fin k → (Fin 10 → Bool)) → List Bool
  | 0, _ => w
  | k + 1, F => catB (w ++ List.ofFn (F 0)) k (fun i => F i.succ)

theorem cExt_unifAvg (k : ℕ) : ∀ G : List Bool → ℂ, cExt (unifAvg G) k = unifAvg (cExt G k) := by
  induction k with
  | zero => intro G; rfl
  | succ k ih => intro G; show cExt (unifAvg (unifAvg G)) k = _; rw [ih]; rfl

/-- **The uniform continuation is the uniform average over the `k`-block completions.** -/
theorem cExt_eq_sum (G : List Bool → ℂ) (k : ℕ) : ∀ w : List Bool,
    cExt G k w = (1 / 1024 ^ k : ℂ) * ∑ F : Fin k → (Fin 10 → Bool), G (catB w k F) := by
  induction k with
  | zero => intro w; simp [cExt, catB]
  | succ k ih =>
    intro w
    rw [show cExt G (k + 1) = cExt (unifAvg G) k from rfl, cExt_unifAvg, unifAvg]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 10 → Bool)).sum_comp
      (fun F => G (catB w (k + 1) F)), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, catB, Fin.cons_zero, Fin.cons_succ]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [pow_succ]; ring

open Classical in
/-- The `resLaw` path weight of `k` blocks after `w`: `∏ 1_{alive}/|A|` along the path. -/
noncomputable def pathW (w : List Bool) : (k : ℕ) → (Fin k → (Fin 10 → Bool)) → ℝ
  | 0, _ => 1
  | k + 1, F => (if F 0 ∈ aliveSet w then 1 / ((aliveSet w).card : ℝ) else 0) *
      pathW (w ++ List.ofFn (F 0)) k (fun i => F i.succ)

/-- **The `resLaw` likelihood of a path**: the atom of `catB w k F` has mass
`mass(w) · pathW w k F`.  Against the uniform (Cantor) law, whose weight is `1024^{−k}`, the
likelihood ratio is `∏ 1_{alive}·1024/|A|`.  Proved (iterated `real_child`). -/
theorem real_buildU_catB (k : ℕ) : ∀ (s : ℕ) (w : List Bool) (F : Fin k → (Fin 10 → Bool)),
    w.length = 10 * s →
    coinMeasure.real {ω | buildU (s + k) ω = catB w k F} =
      coinMeasure.real {ω | buildU s ω = w} * pathW w k F := by
  classical
  induction k with
  | zero => intro s w F _; simp [catB, pathW]
  | succ k ih =>
    intro s w F hl
    have hl' : (w ++ List.ofFn (F 0)).length = 10 * (s + 1) := by
      rw [List.length_append, List.length_ofFn, hl]; ring
    simp only [catB, pathW]
    rw [show s + (k + 1) = s + 1 + k by ring, ih (s + 1) _ _ hl', real_child s w hl]
    split_ifs <;> ring


/-! ### The first-order term as an obstacle sum -/

/-- The normalized Cantor character of the cylinder `v`: `e(ξ cylLeft v) μ̂_K(ξ/3^{|v|})`
(the `μ_K`-average of `e(ξx)` over the cylinder). -/
noncomputable def cylChar (ξ : ℝ) (v : List Bool) : ℂ :=
  ee (ξ * cylLeft v) * muK (ξ / 3 ^ v.length)

/-- **The dead correction is a sum over the dead children.**  Each dead child `f` contributes
its cylinder character minus the parent's: `D(ξ, v) = |A(v)|⁻¹ Σ_{f dead} (χ(vf) − χ(v))`.
Proved (`muK_stage`). -/
theorem deadCorr_eq_cylChar (ξ : ℝ) (v : List Bool) :
    deadCorr ξ v = (1 / ((aliveSet v).card : ℂ)) *
      ∑ f ∈ Finset.univ \ aliveSet v, (cylChar ξ (v ++ List.ofFn f) - cylChar ξ v) := by
  have hpar : cylChar ξ v = ee (ξ * cylLeft v) * rhoS ξ v.length *
      muK (ξ / 3 ^ (v.length + 10)) := by
    rw [cylChar, muK_stage]; ring
  have hch : ∀ f : Fin 10 → Bool, cylChar ξ (v ++ List.ofFn f) =
      ee (ξ * cylLeft v) * ee (ξ * J f / 3 ^ (v.length + 10)) * muK (ξ / 3 ^ (v.length + 10)) := by
    intro f
    rw [cylChar, cylLeft_child, ← ee_add, List.length_append, List.length_ofFn]
    congr 2; ring
  unfold deadCorr deadErr
  simp only [hch, hpar]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- The conditional mean of a stage-`s` function on a stage-`s` atom is at most its value. -/
theorem norm_condMean_self_le (s : ℕ) (G : List Bool → ℂ) (w : List Bool) :
    ‖condMean (fun ω => G (buildU s ω)) s w‖ ≤ ‖G w‖ := by
  have hI : ∫ ω in {ω | buildU s ω = w}, G (buildU s ω) ∂coinMeasure =
      ∫ ω in {ω | buildU s ω = w}, G w ∂coinMeasure :=
    setIntegral_congr_fun (mset_buildU' s w) fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω; simp only [hω]
  unfold condMean
  rw [hI, setIntegral_const, norm_div, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := coinMeasure) (s := {ω | buildU s ω = w}))
    with h0 | hpos
  · rw [← h0, div_zero]; exact norm_nonneg _
  · rw [norm_smul, Real.norm_of_nonneg hpos.le, mul_div_cancel_left₀ _ hpos.ne']

/-- The cylinder-local obstacle sum at the completion `v`: `|A(v)|⁻¹ Σ_{f dead} (χ(vf) − χ(v))`
(`= deadCorr`, `deadCorr_eq_cylChar`). -/
noncomputable def obstLocal (ξ : ℝ) (v : List Bool) : ℂ :=
  (1 / ((aliveSet v).card : ℂ)) *
    ∑ f ∈ Finset.univ \ aliveSet v, (cylChar ξ (v ++ List.ofFn f) - cylChar ξ v)

/-- The `μ_K`-averaged obstacle phase sum below the prefix `w`, `k` blocks down. -/
noncomputable def obstSum (ξ : ℝ) (k : ℕ) (w : List Bool) : ℂ :=
  (1 / 1024 ^ k : ℂ) * ∑ F : Fin k → (Fin 10 → Bool), obstLocal ξ (catB w k F)

/-- The `resLaw` expectation of `‖obstSum‖` over the stage-`s_n` prefix. -/
noncomputable def obstMix (b C : ℕ) (h : ℤ) (n m t : ℕ) : ℝ :=
  ∫ ω, ‖obstSum (h * (b : ℝ) ^ m) (t - stageOf b C n) (buildU (stageOf b C n) ω)‖ ∂coinMeasure

/-- **The first-order mix is an explicit obstacle sum.**  `firstMix ≤ obstMix`: the `resLaw`
expectation over the coarse prefix `w = w_{s_n}` of the norm of the uniform (Cantor) average,
over the `k = t − s_n` block completions `v` of `w`, of `|A(v)|⁻¹ Σ_{f dead at v} (χ(vf) − χ(v))`.
The dead children at `v` sit at the obstacles `p/q` charged to `v`, and `χ(vf) ≈ e(ξ p/q)`.
The weights are exact (`1/|A(v)|`, not `1/1024`), so no second-order error arises here.  Proved. -/
theorem firstMix_le_obstMix (b C : ℕ) (h : ℤ) (n m t : ℕ) :
    firstMix b C h n m t ≤ obstMix b C h n m t := by
  unfold firstMix obstMix
  refine integral_mono (integrable_comp_buildU _ _).norm
    (integrable_comp_buildU (stageOf b C n) (obstSum (h * (b : ℝ) ^ m) _)).norm fun ω => ?_
  refine (norm_condMean_self_le _ _ _).trans (le_of_eq ?_)
  simp only [cExt_eq_sum, deadCorr_eq_cylChar, obstSum, obstLocal]


/-- **Cauchy–Schwarz on a stage function.**  `(E‖G(w_s)‖)² ≤ E‖G(w_s)‖²` under `resLaw`.  Proved. -/
theorem sq_integral_norm_comp_buildU_le (s : ℕ) (G : List Bool → ℂ) :
    (∫ ω, ‖G (buildU s ω)‖ ∂coinMeasure) ^ 2 ≤ ∫ ω, ‖G (buildU s ω)‖ ^ 2 ∂coinMeasure := by
  set g : (ℕ → Bool) → ℝ := fun ω => ‖G (buildU s ω)‖
  have hg : Integrable g coinMeasure := (integrable_comp_buildU s G).norm
  have hg2 : Integrable (fun ω => g ω ^ 2) coinMeasure := by
    refine ((integrable_comp_buildU s (fun w => G w * G w)).norm).congr
      (Eventually.of_forall fun ω => ?_)
    simp [g, norm_mul, sq]
  set c := ∫ ω, g ω ∂coinMeasure
  have h0 : 0 ≤ ∫ ω, (g ω - c) ^ 2 ∂coinMeasure := integral_nonneg fun ω => sq_nonneg _
  have hexp : ∀ ω, (g ω - c) ^ 2 = g ω ^ 2 + ((-2 * c) * g ω + c ^ 2) := fun ω => by ring
  simp_rw [hexp] at h0
  have hlin : Integrable (fun ω => (-2 * c) * g ω + c ^ 2) coinMeasure :=
    (hg.const_mul _).add (integrable_const _)
  rw [integral_add hg2 hlin, integral_add (hg.const_mul _) (integrable_const _),
    integral_const_mul, integral_const] at h0
  simp only [probReal_univ, smul_eq_mul, one_mul] at h0
  nlinarith

/-- **`obstMix` is controlled by the second moment of the cylinder obstacle sum**, the first step
from `CylObstacleCancellation` toward a pair-correlation statement.  Proved. -/
theorem obstMix_sq_le (b C : ℕ) (h : ℤ) (n m t : ℕ) :
    obstMix b C h n m t ^ 2 ≤ ∫ ω, ‖obstSum (h * (b : ℝ) ^ m) (t - stageOf b C n)
      (buildU (stageOf b C n) ω)‖ ^ 2 ∂coinMeasure :=
  sq_integral_norm_comp_buildU_le _ _

/-- **Pair expansion of the cylinder obstacle sum.**  `‖obstSum‖²` is the `1024^{−2k}`-weighted sum,
over pairs of completions `(v, v')` of `w`, of `obstLocal v · conj (obstLocal v')`; the diagonal
`v = v'` is the obstacle count, the off-diagonal pairs are the same-cylinder obstacle pairs.  Proved. -/
theorem norm_obstSum_sq (ξ : ℝ) (k : ℕ) (w : List Bool) :
    (‖obstSum ξ k w‖ ^ 2 : ℂ) = (1 / 1024 ^ k : ℂ) ^ 2 *
      ∑ F : Fin k → (Fin 10 → Bool), ∑ F' : Fin k → (Fin 10 → Bool),
        obstLocal ξ (catB w k F) * (starRingEnd ℂ) (obstLocal ξ (catB w k F')) := by
  rw [← Complex.mul_conj', obstSum, map_mul, map_sum]
  have hc : (starRingEnd ℂ) (1 / 1024 ^ k : ℂ) = 1 / 1024 ^ k := by
    simp only [one_div, map_inv₀, map_pow]; rw [show (starRingEnd ℂ) 1024 = 1024 from Complex.conj_ofNat 1024]
  rw [hc, mul_mul_mul_comm, ← sq, Finset.sum_mul_sum]
/-- **Cylinder-local obstacle cancellation node.**  Believed 50% for `3 ∤ b`.  The near-scale sum
of `obstMix` over `n < m < N` is `O(N² W(N))`.  Implies `FirstOrderObstacleMix b`
(`firstOrderObstacleMix_of_cyl`).  This is the honest form of the first-order crux: the
cancellation needed is among the obstacles inside one coarse cylinder `w_{s_n}`, `μ_K`-weighted
along the uniform completions, with the exact weights `1/|A(v)|`.  `ObstaclePairCorrelation` is a
global, unweighted pair statement; passing from it to this node needs Cauchy–Schwarz over the
cylinders, a smoothing of the cylinder boundaries (pairs within `3^{−S}` that straddle two
cylinders), and the passage from the `resLaw` law of `w_{s_n}` to `μ_K` (`PairCorrToCylinder`).

Probe (`scripts/cantorbad_deadmix.py`, law `first` = resLaw prefix + uniform continuation, i.e.
`obstMix / E|D_t|`; 300 × 200, `t = 8`, lag `g = t − s`): `R = .087, .081, .077` (b = 2) against the
full `deadMix` ratio `.092, .080, .082`; the control `b = 3` gives `.090, .080, .078`.  All are at the
Monte Carlo floor `.071`, and the `b = 3` control does not separate at these lags, so the probe
is inconclusive (no working control): it neither supports nor refutes this node, and it does not
decide whether the defect part is lower order (first and full differ by less than the noise). -/
def CylObstacleCancellation (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)), obstMix b C h n m t ≤
          K * (N : ℝ) ^ 2 * W N

/-- **Cylinder-local cancellation ⇒ first-order node.**  Proved. -/
theorem firstOrderObstacleMix_of_cyl {b : ℕ} (hO : CylObstacleCancellation b) :
    FirstOrderObstacleMix b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hO h hh C
  refine ⟨K, W, hW, fun N hN => le_trans ?_ (hK N hN)⟩
  exact Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
    Finset.sum_le_sum fun t _ => firstMix_le_obstMix b C h n m t



theorem norm_cylChar_le (ξ : ℝ) (v : List Bool) : ‖cylChar ξ v‖ ≤ 1 := by
  rw [cylChar, norm_mul, norm_ee, one_mul]; exact norm_muK_le _

/-- **The local obstacle term is bounded by the dead count.**  `‖obstLocal ξ v‖ ≤ 2·#dead/|A|`.
So the diagonal of `secondMoment_obstSum_eq` is `1024^{−k}` times an averaged squared dead
ratio: it decays geometrically in `k = t − s_n`, and only the off-diagonal pairs carry the crux.
Proved. -/
theorem norm_obstLocal_le (ξ : ℝ) (v : List Bool) :
    ‖obstLocal ξ v‖ ≤ 2 * ((1024 - (aliveSet v).card : ℕ) : ℝ) / (aliveSet v).card := by
  classical
  have hc0 : (0 : ℝ) < (aliveSet v).card := by exact_mod_cast card_aliveSet_pos v
  have hD : (Finset.univ \ aliveSet v).card = 1024 - (aliveSet v).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; simp
  rw [obstLocal, norm_mul]
  have hs : ‖∑ f ∈ Finset.univ \ aliveSet v, (cylChar ξ (v ++ List.ofFn f) - cylChar ξ v)‖ ≤
      ((1024 - (aliveSet v).card : ℕ) : ℝ) * 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ f ∈ Finset.univ \ aliveSet v, (2 : ℝ) := Finset.sum_le_sum fun f _ =>
          (norm_sub_le _ _).trans (add_le_add (norm_cylChar_le _ _) (norm_cylChar_le _ _) |>.trans
            (by norm_num))
      _ = _ := by rw [Finset.sum_const, hD, nsmul_eq_mul]
  have hn : ‖(1 / ((aliveSet v).card : ℂ))‖ = 1 / (aliveSet v).card := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hn]
  calc 1 / ((aliveSet v).card : ℝ) * _ ≤ 1 / (aliveSet v).card * (((1024 - (aliveSet v).card : ℕ) : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The off-diagonal (distinct completions) part of `‖obstSum‖²`: same-cylinder obstacle pairs. -/
noncomputable def obstOff (ξ : ℝ) (k : ℕ) (w : List Bool) : ℂ :=
  (1 / 1024 ^ k : ℂ) ^ 2 * ∑ F : Fin k → (Fin 10 → Bool),
    ∑ F' ∈ Finset.univ.erase F, obstLocal ξ (catB w k F) * (starRingEnd ℂ) (obstLocal ξ (catB w k F'))

/-- **Diagonal + off-diagonal split of `‖obstSum‖²`.**  Proved. -/
theorem norm_obstSum_sq_split (ξ : ℝ) (k : ℕ) (w : List Bool) :
    (‖obstSum ξ k w‖ ^ 2 : ℂ) = (1 / 1024 ^ k : ℂ) ^ 2 *
      ∑ F : Fin k → (Fin 10 → Bool), (‖obstLocal ξ (catB w k F)‖ ^ 2 : ℂ) + obstOff ξ k w := by
  rw [norm_obstSum_sq, obstOff, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ F), Complex.mul_conj']

theorem norm_obstLocal_le_const (ξ : ℝ) (v : List Bool) : ‖obstLocal ξ v‖ ≤ 2048 := by
  refine (norm_obstLocal_le ξ v).trans ?_
  have hc : (1 : ℝ) ≤ (aliveSet v).card := by exact_mod_cast card_aliveSet_pos v
  rw [div_le_iff₀ (by linarith)]
  have : ((1024 - (aliveSet v).card : ℕ) : ℝ) ≤ 1024 := by exact_mod_cast Nat.sub_le _ _
  nlinarith

/-- **Pointwise second-moment bound: geometric diagonal + off-diagonal.**
`‖obstSum‖² ≤ 2048²·1024^{−k} + ‖obstOff‖`.  Proved (crude constant). -/
theorem norm_obstSum_sq_le (ξ : ℝ) (k : ℕ) (w : List Bool) :
    ‖obstSum ξ k w‖ ^ 2 ≤ 2048 ^ 2 / 1024 ^ k + ‖obstOff ξ k w‖ := by
  have h := congrArg norm (norm_obstSum_sq_split ξ k w)
  rw [show ‖(‖obstSum ξ k w‖ ^ 2 : ℂ)‖ = ‖obstSum ξ k w‖ ^ 2 by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]] at h
  rw [h]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  rw [norm_mul, norm_pow, norm_div, norm_one, norm_pow, Complex.norm_ofNat]
  have hs : ‖∑ F : Fin k → (Fin 10 → Bool), (‖obstLocal ξ (catB w k F)‖ ^ 2 : ℂ)‖ ≤
      (1024 : ℝ) ^ k * 2048 ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _F : Fin k → (Fin 10 → Bool), (2048 : ℝ) ^ 2 := Finset.sum_le_sum fun F _ => by
          rw [show ‖(‖obstLocal ξ (catB w k F)‖ ^ 2 : ℂ)‖ = ‖obstLocal ξ (catB w k F)‖ ^ 2 by
            rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_obstLocal_le_const _ _) 2
      _ = _ := by simp [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hp : (0 : ℝ) < 1024 ^ k := by positivity
  calc (1 / 1024 ^ k) ^ 2 * _ ≤ (1 / (1024 : ℝ) ^ k) ^ 2 * ((1024 : ℝ) ^ k * 2048 ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp
/-- **The `resLaw` second moment as an explicit pair sum.**  `E‖obstSum‖²` is the sum over stage-`s`
prefixes `w`, weighted by their `resLaw` mass, of the same-cylinder pair sums of
`norm_obstSum_sq`.  Proved. -/
theorem secondMoment_obstSum_eq (ξ : ℝ) (k s : ℕ) :
    ((∫ ω, ‖obstSum ξ k (buildU s ω)‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ w ∈ LS s, coinMeasure.real {ω | buildU s ω = w} • ((1 / 1024 ^ k : ℂ) ^ 2 *
        ∑ F : Fin k → (Fin 10 → Bool), ∑ F' : Fin k → (Fin 10 → Bool),
          obstLocal ξ (catB w k F) * (starRingEnd ℂ) (obstLocal ξ (catB w k F'))) := by
  rw [← integral_complex_ofReal]
  push_cast
  rw [integral_buildU s (fun w => (‖obstSum ξ k w‖ ^ 2 : ℂ))]
  exact Finset.sum_congr rfl fun w _ => by rw [norm_obstSum_sq]
/-- **Conjecture node (resLaw-native second moment).**  Believed 45% for `3 ∤ b`.  The near-scale
sum of the `resLaw` root-mean-squares `√E‖obstSum‖²` is `O(N² W(N))`.  Implies
`CylObstacleCancellation b` (`cylObstacleCancellation_of_secondMoment`, via `obstMix_sq_le`).  Stated natively under `resLaw` because the
change of measure to `μ_K` is expected to fail: the likelihood ratio of `w_s` is
`∏ 1_alive·1024/|A|` (`real_buildU_catB`), a mean-one `μ_K`-martingale whose second moment is
`∏ E[1024/|A|] ≈ (1 + 1.3/1024)^s` (`AvgDeadDensity` evidence), exponential in `s = s_n`; so
Hölder transfer from a `μ_K` pair statement such as `ObstaclePairCorrelation` loses `e^{c s_n}`.
(Heuristic, 70%; not a theorem.) -/
def ResLawObstSecondMoment (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          Real.sqrt (∫ ω, ‖obstSum (h * (b : ℝ) ^ m) (t - stageOf b C n)
            (buildU (stageOf b C n) ω)‖ ^ 2 ∂coinMeasure) ≤ K * (N : ℝ) ^ 2 * W N

/-- **Second-moment node ⇒ cylinder-local cancellation.**  Proved. -/
theorem cylObstacleCancellation_of_secondMoment {b : ℕ} (hO : ResLawObstSecondMoment b) :
    CylObstacleCancellation b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hO h hh C
  refine ⟨K, W, hW, fun N hN => le_trans ?_ (hK N hN)⟩
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
    Finset.sum_le_sum fun t _ => ?_
  exact Real.le_sqrt_of_sq_le (obstMix_sq_le b C h n m t)

/-- **Open implication node: global pair correlation ⇒ cylinder-local cancellation.**  Believed
40% as stated (the global unweighted pair sum need not control the cylinder-restricted, `resLaw`-
weighted second moment; the missing pieces are listed at `CylObstacleCancellation`). -/
def PairCorrToCylinder (b : ℕ) : Prop :=
  ObstaclePairCorrelation b → CylObstacleCancellation b



/-- Stages grow linearly: `s_m + C ≥ s_n + (m − n)/20`. -/
theorem stageOf_gap {b : ℕ} (hb : 2 ≤ b) (C : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    stageOf b C n + (m - n) / 20 ≤ stageOf b C m + C := by
  unfold stageOf
  have hb0 : 0 < b := by omega
  have hlog : Nat.log 3 (b ^ n) + (m - n) / 2 ≤ Nat.log 3 (b ^ m) := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    rw [pow_add, show m = n + (m - n) by omega, pow_add]
    refine Nat.mul_le_mul (Nat.pow_log_le_self 3 (pow_pos hb0 n).ne') ?_
    rw [show n + (m - n) - n = m - n by omega]
    exact (Nat.pow_le_pow_right (by norm_num) (le_log_of_two_mul hb (Nat.mul_div_le _ _))).trans
      (Nat.pow_log_le_self 3 (pow_pos hb0 _).ne')
  omega
/-- **Off-diagonal node.**  Believed 45% for `3 ∤ b`.  The `resLaw`-averaged same-cylinder obstacle
pair sums `E‖obstOff‖` have near-scale root sum `O(N² W(N))`.  This is the irreducible core of the
first-order crux: a pair correlation of the obstacle phases `e(hbᵐ(p/q − p'/q'))` over pairs in one
coarse cylinder, under `resLaw`.

Base 3.  The first-order probe (`scripts/cantorbad_deadmix.py first`, `t = 12`, 200 × 400, lags
1–5) gives `R = .067 → .056` for b = 2, `.069 → .057` for b = 5, and `.066 → .059` for b = 3, all
near the floor `.05`.  That configuration had no working control; the controlled probe is
recorded at `AliveOffMix` (b = 3 near the floor there too).  The base-3 failure of the headline may live in the
Cantor main term (`cesaro_contChar_small` uses `3 ∤ b`) rather than here; undecided.  The Riesz sub-family (`riesz_three_shift`) is coherent
along `h·3ᵐ` but has about `2^ℓ` of the `4^ℓ` obstacles, so it is lower order. -/
def ResLawObstOff (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          Real.sqrt (∫ ω, ‖obstOff (h * (b : ℝ) ^ m) (t - stageOf b C n)
            (buildU (stageOf b C n) ω)‖ ∂coinMeasure) ≤ K * (N : ℝ) ^ 2 * W N

/-- **Diagonal leaf.**  The geometric diagonal has near-scale root sum `O(N² W(N))`.  Proved
(`s_m ≥ s_n + (m − n)/20 − C`, `stageOf_gap`, so the sum is `O(N)`; `W(N) = 1/N` is summable along `sched`)
(`diagSmall_of_two_le`). -/
def DiagSmall (b : ℕ) : Prop :=
  ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          Real.sqrt (2048 ^ 2 / 1024 ^ (t - stageOf b C n)) ≤ K * (N : ℝ) ^ 2 * W N

theorem sqrt_diag_eq (k : ℕ) : Real.sqrt (2048 ^ 2 / 1024 ^ k) = 2048 * (1 / 32 : ℝ) ^ k := by
  rw [show (2048 : ℝ) ^ 2 / 1024 ^ k = (2048 * (1 / 32 : ℝ) ^ k) ^ 2 by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; norm_num [one_div, inv_pow, div_eq_mul_inv]; ring_nf; simp [one_div]]
  exact Real.sqrt_sq (by positivity)

theorem inv_pow_div20_le {c : ℝ} (hc : 2 ≤ c) (j : ℕ) :
    (1 / c) ^ (j / 20) ≤ c * (31 / 32 : ℝ) ^ j := by
  have hc0 : 0 < c := by linarith
  have hj : j ≤ 20 * (j / 20 + 1) := by omega
  have h1 : (31 / 32 : ℝ) ^ (20 * (j / 20 + 1)) ≤ (31 / 32 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have hb : 1 / c ≤ (31 / 32 : ℝ) ^ 20 := by
    rw [div_le_iff₀ hc0]; nlinarith [show (1 : ℝ) / 2 ≤ (31 / 32 : ℝ) ^ 20 by norm_num]
  have h2 : (1 / c) ^ (j / 20 + 1) ≤ (31 / 32 : ℝ) ^ (20 * (j / 20 + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hb _
  have h3 := h2.trans h1
  rw [pow_succ] at h3
  have e : (1 / c) ^ (j / 20) = ((1 / c) ^ (j / 20) * (1 / c)) * c := by field_simp
  rw [e]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / c by positivity) (j / 20)]

theorem diag_term_le {b : ℕ} (hb : 2 ≤ b) (C : ℕ) {c : ℝ} (hc : 2 ≤ c) {n m t : ℕ} (hnm : n < m)
    (ht : stageOf b C m ≤ t) :
    (1 / c) ^ (t - stageOf b C n) ≤
      c ^ C * c * (1 / c) ^ (t - stageOf b C m) * (31 / 32 : ℝ) ^ (m - 1 - n) := by
  have hc0 : 0 < c := by linarith
  have hr1 : 1 / c ≤ 1 := by rw [div_le_one hc0]; linarith
  have hr0 : 0 ≤ 1 / c := by positivity
  have hg := stageOf_gap hb C hnm.le
  have hmo := stageOf_mono b C (by omega) hnm.le
  set a := (m - n) / 20
  have hexp : t - stageOf b C m + (a - C) ≤ t - stageOf b C n := by omega
  have r1 : (1 / c) ^ (t - stageOf b C n) ≤ (1 / c) ^ (t - stageOf b C m + (a - C)) :=
    pow_le_pow_of_le_one hr0 hr1 hexp
  have r2 : (1 / c) ^ (a - C) ≤ c ^ C * (1 / c) ^ a := by
    have : (1 / c) ^ a ≥ (1 / c) ^ (a - C + C) := pow_le_pow_of_le_one hr0 hr1 (by omega)
    rw [pow_add] at this
    have e : c ^ C * (1 / c) ^ C = 1 := by rw [← mul_pow]; field_simp; simp
    nlinarith [pow_nonneg hr0 (a - C), pow_nonneg hc0.le C]
  have r3 : (1 / c) ^ a ≤ c * (31 / 32 : ℝ) ^ (m - 1 - n) :=
    (inv_pow_div20_le hc _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hc0.le)
  rw [pow_add] at r1
  have p0 : (0 : ℝ) ≤ (1 / c) ^ (t - stageOf b C m) := pow_nonneg hr0 _
  calc _ ≤ _ := r1
    _ ≤ (1 / c) ^ (t - stageOf b C m) * (c ^ C * (c * (31 / 32 : ℝ) ^ (m - 1 - n))) :=
        mul_le_mul_of_nonneg_left (r2.trans (mul_le_mul_of_nonneg_left r3 (by positivity))) p0
    _ = _ := by ring

/-- **Geometric near-scale sums are `O(N)`.**  For `c ≥ 2`, the near-scale sum of
`(1/c)^{t − s_n}` is at most `K N`.  Proved. -/
theorem geomNear_le {b : ℕ} (hb : 2 ≤ b) (C : ℕ) {c : ℝ} (hc : 2 ≤ c) (N : ℕ) :
    ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
      ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)), (1 / c) ^ (t - stageOf b C n) ≤
        c ^ C * c * 2 * 32 * N := by
  have hc0 : 0 < c := by linarith
  have inner : ∀ m n, n < m → ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
      (1 / c) ^ (t - stageOf b C n) ≤ c ^ C * c * 2 * (31 / 32 : ℝ) ^ (m - 1 - n) := by
    intro m n hnm
    calc _ ≤ ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          (c ^ C * c * (31 / 32 : ℝ) ^ (m - 1 - n)) * (1 / c) ^ (t - stageOf b C m) :=
          Finset.sum_le_sum fun t ht => by
            have := diag_term_le hb C hc hnm (Finset.mem_Ico.1 ht).1
            linarith
      _ = (c ^ C * c * (31 / 32 : ℝ) ^ (m - 1 - n)) *
          ∑ i ∈ Finset.Ico 0 (Nat.log 3 N + 1), (1 / c) ^ i := by
          rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
          simp
      _ ≤ (c ^ C * c * (31 / 32 : ℝ) ^ (m - 1 - n)) * 2 := by
          refine mul_le_mul_of_nonneg_left ((geom_sum_Ico_le_of_lt_one (by positivity)
            (by rw [div_lt_one hc0]; linarith)).trans ?_) (by positivity)
          rw [pow_zero, div_le_iff₀ (by rw [sub_pos, div_lt_one hc0]; linarith)]
          have : 1 / c ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hc
          linarith
      _ = _ := by ring
  have mid : ∀ m, ∑ n ∈ Finset.range m, (31 / 32 : ℝ) ^ (m - 1 - n) ≤ 32 := by
    intro m
    rw [Finset.sum_range_reflect (fun i => (31 / 32 : ℝ) ^ i) m]
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) (x := (31 / 32 : ℝ)) (by norm_num) (by norm_num)
    rw [← Finset.range_eq_Ico] at h
    exact h.trans (by norm_num)
  calc _ ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        c ^ C * c * 2 * (31 / 32 : ℝ) ^ (m - 1 - n) :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n hn =>
          inner m n (Finset.mem_range.1 hn)
    _ ≤ ∑ m ∈ Finset.range N, (c ^ C * c * 2 * 32 : ℝ) := Finset.sum_le_sum fun m _ => by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (mid m) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **The diagonal leaf.**  Proved: the near-scale diagonal sum is `O(N)`. -/
theorem diagSmall_of_two_le {b : ℕ} (hb : 2 ≤ b) : DiagSmall b := by
  intro C
  refine ⟨2048 * ((32 : ℝ) ^ C * 32 * 2 * 32), fun N => (N : ℝ) ^ (-(1 : ℝ)),
    summable_sched_rpow one_pos, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp_rw [sqrt_diag_eq, ← Finset.mul_sum]
  calc _ ≤ 2048 * ((32 : ℝ) ^ C * 32 * 2 * 32 * N) :=
        mul_le_mul_of_nonneg_left (geomNear_le hb C (c := 32) (by norm_num) N) (by norm_num)
    _ = _ := by simp only [Real.rpow_neg_one]; field_simp

theorem sqrt_secondMoment_le (ξ : ℝ) (k s : ℕ) :
    Real.sqrt (∫ ω, ‖obstSum ξ k (buildU s ω)‖ ^ 2 ∂coinMeasure) ≤
      Real.sqrt (2048 ^ 2 / 1024 ^ k) + Real.sqrt (∫ ω, ‖obstOff ξ k (buildU s ω)‖ ∂coinMeasure) := by
  have hO : Integrable (fun ω => ‖obstOff ξ k (buildU s ω)‖) coinMeasure :=
    (integrable_comp_buildU s _).norm
  have hle : ∫ ω, ‖obstSum ξ k (buildU s ω)‖ ^ 2 ∂coinMeasure ≤
      2048 ^ 2 / 1024 ^ k + ∫ ω, ‖obstOff ξ k (buildU s ω)‖ ∂coinMeasure := by
    have hc := integral_mono_of_nonneg (μ := coinMeasure)
      (Eventually.of_forall fun ω => sq_nonneg ‖obstSum ξ k (buildU s ω)‖)
      ((integrable_const (2048 ^ 2 / 1024 ^ k : ℝ)).add hO)
      (Eventually.of_forall fun ω => norm_obstSum_sq_le ξ k (buildU s ω))
    refine hc.trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    rw [integral_add (integrable_const _) hO, integral_const, probReal_univ, one_smul]
  calc _ ≤ Real.sqrt (2048 ^ 2 / 1024 ^ k + ∫ ω, ‖obstOff ξ k (buildU s ω)‖ ∂coinMeasure) :=
        Real.sqrt_le_sqrt hle
    _ ≤ _ := by
      have ha : (0 : ℝ) ≤ 2048 ^ 2 / 1024 ^ k := by positivity
      have hb : (0 : ℝ) ≤ ∫ ω, ‖obstOff ξ k (buildU s ω)‖ ∂coinMeasure :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg (2048 ^ 2 / 1024 ^ k : ℝ),
        Real.sqrt_nonneg (∫ ω, ‖obstOff ξ k (buildU s ω)‖ ∂coinMeasure)]

/-- **Off-diagonal node + diagonal leaf ⇒ second-moment node.**  Proved. -/
theorem resLawObstSecondMoment_of_off {b : ℕ} (hD : DiagSmall b) (hO : ResLawObstOff b) :
    ResLawObstSecondMoment b := by
  intro h hh C
  obtain ⟨K₁, W₁, hW₁, hK₁⟩ := hD C
  obtain ⟨K₂, W₂, hW₂, hK₂⟩ := hO h hh C
  refine ⟨1, fun N => K₁ * W₁ N + K₂ * W₂ N, (hW₁.mul_left K₁).add (hW₂.mul_left K₂),
    fun N hN => ?_⟩
  calc _ ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          (Real.sqrt (2048 ^ 2 / 1024 ^ (t - stageOf b C n)) +
            Real.sqrt (∫ ω, ‖obstOff (h * (b : ℝ) ^ m) (t - stageOf b C n)
              (buildU (stageOf b C n) ω)‖ ∂coinMeasure)) :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
          Finset.sum_le_sum fun t _ => sqrt_secondMoment_le _ _ _
    _ = _ + _ := by simp only [Finset.sum_add_distrib]
    _ ≤ K₁ * (N : ℝ) ^ 2 * W₁ N + K₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add (hK₁ N hN) (hK₂ N hN)
    _ = _ := by ring

theorem unifAvg_sub (H₁ H₂ : List Bool → ℂ) : unifAvg (H₁ - H₂) = unifAvg H₁ - unifAvg H₂ := by
  funext w; simp only [unifAvg, Pi.sub_apply, Finset.sum_sub_distrib]; ring

theorem cExt_sub (k : ℕ) : ∀ H₁ H₂ : List Bool → ℂ, cExt (H₁ - H₂) k = cExt H₁ k - cExt H₂ k := by
  induction k with
  | zero => intro H₁ H₂; rfl
  | succ k ih => intro H₁ H₂; show cExt (unifAvg (H₁ - H₂)) k = _; rw [unifAvg_sub, ih]; rfl

/-- **The uniform continuation of a defect.**  `cExt (aliveDefect H) k = cExt H (k+1) − cExt (aliveAvg H) k`:
the first-order part of each defect term is a difference of two cylinder averages, one of the
uniform and one of the alive next-block average of `H`.  Proved. -/
theorem cExt_aliveDefect (H : List Bool → ℂ) (k : ℕ) :
    cExt (aliveDefect H) k = cExt H (k + 1) - cExt (aliveAvg H) k := by
  rw [show aliveDefect H = unifAvg H - aliveAvg H from rfl, cExt_sub]; rfl

/-! ### The `resLaw`-native route (no defect split) -/

/-- The `resLaw` continuation by `k` blocks: iterated alive averages. -/
noncomputable def aliveExt (G : List Bool → ℂ) : ℕ → List Bool → ℂ
  | 0 => G
  | k + 1 => aliveExt (aliveAvg G) k

/-- **The `resLaw` conditional mean is the alive continuation.**  Proved (`condMean_succ_alive`). -/
theorem condMean_aliveExt (s : ℕ) (w : List Bool) (k : ℕ) :
    ∀ G : List Bool → ℂ, condMean (fun ω => G (buildU (s + k) ω)) s w =
      condMean (fun ω => aliveExt G k (buildU s ω)) s w := by
  induction k with
  | zero => intro G; rfl
  | succ k ih =>
    intro G
    rw [show s + (k + 1) = s + k + 1 from rfl, condMean_succ_alive G (Nat.le_add_right s k), ih]
    rfl


theorem aliveExt_succ' (k : ℕ) : ∀ G : List Bool → ℂ, aliveExt G (k + 1) = aliveAvg (aliveExt G k) := by
  induction k with
  | zero => intro G; rfl
  | succ k ih => intro G; show aliveExt (aliveAvg G) (k + 1) = _; rw [ih]; rfl

open Classical in
/-- **The `resLaw` continuation as a path-weighted sum.**  Proved. -/
theorem aliveExt_eq_sum (G : List Bool → ℂ) (k : ℕ) : ∀ w : List Bool,
    aliveExt G k w = ∑ F : Fin k → (Fin 10 → Bool), (pathW w k F : ℂ) * G (catB w k F) := by
  induction k with
  | zero => intro w; simp [aliveExt, catB, pathW]
  | succ k ih =>
    intro w
    rw [aliveExt_succ', aliveAvg]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 10 → Bool)).sum_comp
      (fun F => (pathW w (k + 1) F : ℂ) * G (catB w (k + 1) F)), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, catB, pathW, Fin.cons_zero, Fin.cons_succ]
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ aliveSet w)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun f => f ∉ aliveSet w) (fun f hf => by
      simp only [Finset.mem_filter] at hf
      simp [hf.2]), add_zero]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    simp only [hf, if_true]
    push_cast; ring

open Classical in
theorem card_aliveSet_ge (w : List Bool) : 536 ≤ (aliveSet w).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 10 → Bool))) (fun f => Alive 5 c₀ w (List.ofFn f))
  have hd := card_dead_le w
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have : (aliveSet w).card =
      ((Finset.univ : Finset (Fin 10 → Bool)).filter fun f => Alive 5 c₀ w (List.ofFn f)).card := by
    unfold aliveSet; congr
  rw [show (2 : ℕ) ^ 10 = 1024 from rfl] at h
  omega

open Classical in
theorem pathW_nonneg (k : ℕ) : ∀ (w : List Bool) (F : Fin k → (Fin 10 → Bool)), 0 ≤ pathW w k F := by
  induction k with
  | zero => intro w F; simp [pathW]
  | succ k ih =>
    intro w F; simp only [pathW]
    exact mul_nonneg (by split_ifs <;> positivity) (ih _ _)

open Classical in
theorem pathW_le (k : ℕ) : ∀ (w : List Bool) (F : Fin k → (Fin 10 → Bool)),
    pathW w k F ≤ (1 / 536 : ℝ) ^ k := by
  induction k with
  | zero => intro w F; simp [pathW]
  | succ k ih =>
    intro w F; simp only [pathW, pow_succ']
    have h536 : (536 : ℝ) ≤ (aliveSet w).card := by exact_mod_cast card_aliveSet_ge w
    have hfac : (if F 0 ∈ aliveSet w then 1 / ((aliveSet w).card : ℝ) else 0) ≤ 1 / 536 := by
      split_ifs
      · exact one_div_le_one_div_of_le (by norm_num) h536
      · norm_num
    exact mul_le_mul hfac (ih _ _) (pathW_nonneg _ _ _) (by norm_num)

open Classical in
theorem sum_pathW (k : ℕ) : ∀ w : List Bool, ∑ F : Fin k → (Fin 10 → Bool), pathW w k F = 1 := by
  induction k with
  | zero => intro w; simp [pathW]
  | succ k ih =>
    intro w
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 10 → Bool)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathW, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have : (0 : ℝ) < (aliveSet w).card := by exact_mod_cast card_aliveSet_pos w
    field_simp
/-- The `resLaw`-native mix: `E‖aliveExt D_t (t − s_n) (w_{s_n})‖`. -/
noncomputable def aliveMix (b C : ℕ) (h : ℤ) (n m t : ℕ) : ℝ :=
  ∫ ω, ‖aliveExt (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n) (buildU (stageOf b C n) ω)‖
    ∂coinMeasure

/-- **`deadMix ≤ aliveMix`**, with no first-order/defect split.  Proved. -/
theorem deadMix_le_aliveMix (b C : ℕ) (h : ℤ) (n m t : ℕ) (ht : stageOf b C n ≤ t) :
    deadMix b C h n m t ≤ aliveMix b C h n m t := by
  unfold deadMix aliveMix
  refine integral_mono (integrable_comp_buildU _ _).norm (integrable_comp_buildU _ _).norm
    fun ω => ?_
  have e := condMean_aliveExt (stageOf b C n) (buildU (stageOf b C n) ω) (t - stageOf b C n)
    (deadCorr (h * (b : ℝ) ^ m))
  rw [show stageOf b C n + (t - stageOf b C n) = t by omega] at e
  rw [e]
  exact norm_condMean_self_le _ _ _

/-- **`resLaw`-native node.**  Believed 45% for `3 ∤ b`.  Implies `NearObstaclePhaseMixing b`
(`nearObstaclePhaseMixing_of_alive`) directly, with no defect part: the `resLaw` continuation
weights `pathW` already contain the alive defects. -/
def AliveObstacleMix (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)), aliveMix b C h n m t ≤
          K * (N : ℝ) ^ 2 * W N

/-- **`resLaw`-native node ⇒ near-scale node.**  Proved. -/
theorem nearObstaclePhaseMixing_of_alive {b : ℕ} (hb : 1 ≤ b) (hA : AliveObstacleMix b) :
    NearObstaclePhaseMixing b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hA h hh C
  refine ⟨K, W, hW, fun N hN => le_trans ?_ (hK N hN)⟩
  exact Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn =>
    Finset.sum_le_sum fun t ht => deadMix_le_aliveMix b C h n m t
      ((stageOf_mono b C hb (Finset.mem_range.1 hn).le).trans (Finset.mem_Ico.1 ht).1)

theorem norm_deadCorr_le_const (ξ : ℝ) (v : List Bool) : ‖deadCorr ξ v‖ ≤ 2048 := by
  rw [deadCorr_eq_cylChar]; exact norm_obstLocal_le_const ξ v

open Classical in
/-- The off-diagonal part of `‖aliveExt‖²`: pairs of distinct `resLaw` completions. -/
noncomputable def aliveOff (G : List Bool → ℂ) (k : ℕ) (w : List Bool) : ℂ :=
  ∑ F : Fin k → (Fin 10 → Bool), ∑ F' ∈ Finset.univ.erase F,
    ((pathW w k F : ℂ) * G (catB w k F)) * (starRingEnd ℂ) ((pathW w k F' : ℂ) * G (catB w k F'))

open Classical in
/-- **Pointwise: geometric diagonal + off-diagonal**, for `resLaw` continuations of a function
bounded by `2048`.  Proved (`pathW_le`, `sum_pathW`). -/
theorem norm_aliveExt_sq_le (G : List Bool → ℂ) (hG : ∀ v, ‖G v‖ ≤ 2048) (k : ℕ) (w : List Bool) :
    ‖aliveExt G k w‖ ^ 2 ≤ 2048 ^ 2 * (1 / 536 : ℝ) ^ k + ‖aliveOff G k w‖ := by
  set a : (Fin k → (Fin 10 → Bool)) → ℂ := fun F => (pathW w k F : ℂ) * G (catB w k F)
  have hsq : (‖aliveExt G k w‖ ^ 2 : ℂ) = ∑ F, (‖a F‖ ^ 2 : ℂ) + aliveOff G k w := by
    rw [← Complex.mul_conj', aliveExt_eq_sum, map_sum, Finset.sum_mul_sum, aliveOff,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ F), Complex.mul_conj']
  have h := congrArg norm hsq
  rw [show ‖(‖aliveExt G k w‖ ^ 2 : ℂ)‖ = ‖aliveExt G k w‖ ^ 2 by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]] at h
  rw [h]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ F, ‖(‖a F‖ ^ 2 : ℂ)‖ ≤ 2048 ^ 2 * (1 / 536 : ℝ) ^ k * pathW w k F := by
    intro F
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    have hp := pathW_nonneg k w F
    have hpl := pathW_le k w F
    have ha : ‖a F‖ = pathW w k F * ‖G (catB w k F)‖ := by
      simp only [a, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    rw [ha, mul_pow]
    have hg := hG (catB w k F)
    have hg2 : ‖G (catB w k F)‖ ^ 2 ≤ 2048 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
    have hp2 : pathW w k F ^ 2 ≤ (1 / 536 : ℝ) ^ k * pathW w k F := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hpl hp
    calc pathW w k F ^ 2 * ‖G (catB w k F)‖ ^ 2 ≤ ((1 / 536 : ℝ) ^ k * pathW w k F) * 2048 ^ 2 :=
          mul_le_mul hp2 hg2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  calc _ ≤ ∑ F, 2048 ^ 2 * (1 / 536 : ℝ) ^ k * pathW w k F := Finset.sum_le_sum fun F _ => hterm F
    _ = _ := by rw [← Finset.mul_sum, sum_pathW, mul_one]


/-- The sibling (one-step off-diagonal) correlation of `X` among the alive children of `w`. -/
noncomputable def sibCorr (X : List Bool → ℂ) (w : List Bool) : ℂ :=
  (1 / ((aliveSet w).card : ℂ)) ^ 2 * ∑ f ∈ aliveSet w, ∑ f' ∈ (aliveSet w).erase f,
    X (w ++ List.ofFn f) * (starRingEnd ℂ) (X (w ++ List.ofFn f'))

/-- **One-step divergence decomposition.**  `‖aliveAvg X w‖²` is the alive average of `‖X‖²`
scaled by `1/|A|`, plus the sibling correlation.  Iterating it along `aliveExt_succ'` splits
`‖aliveExt D k‖²` by the depth at which two completions diverge.  Proved. -/
theorem norm_aliveAvg_sq (X : List Bool → ℂ) (w : List Bool) :
    (‖aliveAvg X w‖ ^ 2 : ℂ) = (1 / ((aliveSet w).card : ℂ)) *
      aliveAvg (fun v => (‖X v‖ ^ 2 : ℂ)) w + sibCorr X w := by
  have hc : (starRingEnd ℂ) (1 / ((aliveSet w).card : ℂ)) = 1 / ((aliveSet w).card : ℂ) := by
    simp [map_div₀]
  rw [← Complex.mul_conj', aliveAvg, sibCorr, map_mul, map_sum, hc, mul_mul_mul_comm,
    Finset.sum_mul_sum, aliveAvg]
  have e : ∀ f ∈ aliveSet w, ∑ f' ∈ aliveSet w, X (w ++ List.ofFn f) *
      (starRingEnd ℂ) (X (w ++ List.ofFn f')) = (‖X (w ++ List.ofFn f)‖ ^ 2 : ℂ) +
      ∑ f' ∈ (aliveSet w).erase f, X (w ++ List.ofFn f) * (starRingEnd ℂ) (X (w ++ List.ofFn f')) :=
    fun f hf => by rw [← Finset.add_sum_erase _ _ hf, Complex.mul_conj']
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
  ring

/-- Real alive average. -/
noncomputable def rAvg (Y : List Bool → ℝ) (w : List Bool) : ℝ :=
  (1 / ((aliveSet w).card : ℝ)) * ∑ f ∈ aliveSet w, Y (w ++ List.ofFn f)

/-- The depth-weighted sibling sum: the sibling correlations at every divergence depth, each
damped by `1/|A|` per level above it. -/
noncomputable def sibSum (G : List Bool → ℂ) : ℕ → List Bool → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun w => (1 / ((aliveSet w).card : ℝ)) * rAvg (sibSum G k) w +
      ‖sibCorr (aliveExt G k) w‖

theorem rAvg_mono {Y Z : List Bool → ℝ} (h : ∀ v, Y v ≤ Z v) (w : List Bool) : rAvg Y w ≤ rAvg Z w :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => h _) (by positivity)

theorem rAvg_const_add (c : ℝ) (Y : List Bool → ℝ) (w : List Bool) :
    rAvg (fun v => c + Y v) w = c + rAvg Y w := by
  have : (0 : ℝ) < (aliveSet w).card := by exact_mod_cast card_aliveSet_pos w
  unfold rAvg; rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; field_simp

/-- **Divergence-depth expansion.**  `‖aliveExt G k w‖² ≤ 2048²·536^{−k} + sibSum G k w`.  Proved. -/
theorem norm_aliveExt_sq_le_sib (G : List Bool → ℂ) (hG : ∀ v, ‖G v‖ ≤ 2048) (k : ℕ) :
    ∀ w, ‖aliveExt G k w‖ ^ 2 ≤ 2048 ^ 2 * (1 / 536 : ℝ) ^ k + sibSum G k w := by
  induction k with
  | zero => intro w; simp only [aliveExt, sibSum, pow_zero, mul_one, add_zero]
            exact pow_le_pow_left₀ (norm_nonneg _) (hG w) 2
  | succ k ih =>
    intro w
    have hA : (0 : ℝ) < (aliveSet w).card := by exact_mod_cast card_aliveSet_pos w
    have hA5 : (536 : ℝ) ≤ (aliveSet w).card := by exact_mod_cast card_aliveSet_ge w
    have key := norm_aliveAvg_sq (aliveExt G k) w
    rw [← aliveExt_succ'] at key
    have hre := congrArg Complex.re key
    have h1 : (‖aliveExt G (k + 1) w‖ ^ 2 : ℂ).re = ‖aliveExt G (k + 1) w‖ ^ 2 := by
      norm_cast
    have h2 : ((1 / ((aliveSet w).card : ℂ)) * aliveAvg (fun v => (‖aliveExt G k v‖ ^ 2 : ℂ)) w).re
        = (1 / ((aliveSet w).card : ℝ)) * rAvg (fun v => ‖aliveExt G k v‖ ^ 2) w := by
      unfold aliveAvg rAvg
      rw [show (1 / ((aliveSet w).card : ℂ)) = ((1 / ((aliveSet w).card : ℝ) : ℝ) : ℂ) by push_cast; rfl]
      rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_sum]
      congr 2
      refine Finset.sum_congr rfl fun f _ => ?_
      norm_cast
    rw [h1, Complex.add_re, h2] at hre
    have h3 : (sibCorr (aliveExt G k) w).re ≤ ‖sibCorr (aliveExt G k) w‖ := Complex.re_le_norm _
    have h4 : rAvg (fun v => ‖aliveExt G k v‖ ^ 2) w ≤
        2048 ^ 2 * (1 / 536 : ℝ) ^ k + rAvg (sibSum G k) w := by
      rw [← rAvg_const_add]; exact rAvg_mono ih w
    have h5 : 1 / ((aliveSet w).card : ℝ) ≤ 1 / 536 := one_div_le_one_div_of_le (by norm_num) hA5
    have hS0 : 0 ≤ 2048 ^ 2 * (1 / 536 : ℝ) ^ k := by positivity
    have hp : (0 : ℝ) ≤ 1 / ((aliveSet w).card : ℝ) := by positivity
    have e1 := mul_le_mul_of_nonneg_left h4 hp
    have e2 := mul_le_mul_of_nonneg_right h5 hS0
    simp only [sibSum]
    calc ‖aliveExt G (k + 1) w‖ ^ 2 = _ := hre
      _ ≤ 1 / ((aliveSet w).card : ℝ) * (2048 ^ 2 * (1 / 536 : ℝ) ^ k + rAvg (sibSum G k) w) +
          ‖sibCorr (aliveExt G k) w‖ := by linarith
      _ = 1 / ((aliveSet w).card : ℝ) * (2048 ^ 2 * (1 / 536 : ℝ) ^ k) +
          (1 / ((aliveSet w).card : ℝ) * rAvg (sibSum G k) w + ‖sibCorr (aliveExt G k) w‖) := by ring
      _ ≤ 1 / 536 * (2048 ^ 2 * (1 / 536 : ℝ) ^ k) +
          (1 / ((aliveSet w).card : ℝ) * rAvg (sibSum G k) w + ‖sibCorr (aliveExt G k) w‖) := by
          linarith
      _ = _ := by ring
/-- **`resLaw`-native off-diagonal node** (single crux).  Believed 45% for `3 ∤ b`.  The near-scale
root sums of `E‖aliveOff D_t‖` are `O(N² W(N))`.  This pair correlation is over pairs of distinct
`resLaw` completions of the coarse prefix, weighted by their path probabilities, so the alive
defects are built in and there is no separate defect node.  Implies `AliveObstacleMix b`
(`aliveObstacleMix_of_off`), hence `NearObstaclePhaseMixing b`.

Probe with a working control (lap 9, `scripts/cantorbad_deadmix.py LAW b 7 150 300 10 8`, i.e.
t = 10 and `ξ = bᵐ ≥ 3^{L_t+8}`; ratio `R = E|E[D_t | w_s]| / E|D_t|`, floor `.058`, lags 1–5):
known-coherent dyadic sibling `dyad2`: `R = .977` flat (control detects coherence);
`resLaw` b = 2: `.076, .066, .064, .067, .065`; b = 3: `.073, .066, .063, .069, .069`.  So b = 2 sits
near the floor, consistent with this node.  b = 3 is also near the floor, so at this single-pair
level the base-3 barrier does not show; it may bind only the Cantor main term.  (With
`ξ ≥ 3^{L_t+3}` the dyadic control was at the floor, because its obstacles `p/2^m` had
`2^m > ξ`; that earlier configuration is not evidence.) -/
def AliveOffMix (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          Real.sqrt (∫ ω, ‖aliveOff (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n)
            (buildU (stageOf b C n) ω)‖ ∂coinMeasure) ≤ K * (N : ℝ) ^ 2 * W N

theorem sqrt_aliveSecond_le (G : List Bool → ℂ) (hG : ∀ v, ‖G v‖ ≤ 2048) (k s : ℕ) :
    ∫ ω, ‖aliveExt G k (buildU s ω)‖ ∂coinMeasure ≤
      2048 * (1 / 16 : ℝ) ^ k + Real.sqrt (∫ ω, ‖aliveOff G k (buildU s ω)‖ ∂coinMeasure) := by
  have hO : Integrable (fun ω => ‖aliveOff G k (buildU s ω)‖) coinMeasure :=
    (integrable_comp_buildU s _).norm
  have hle : ∫ ω, ‖aliveExt G k (buildU s ω)‖ ^ 2 ∂coinMeasure ≤
      2048 ^ 2 * (1 / 536 : ℝ) ^ k + ∫ ω, ‖aliveOff G k (buildU s ω)‖ ∂coinMeasure := by
    have hc := integral_mono_of_nonneg (μ := coinMeasure)
      (Eventually.of_forall fun ω => sq_nonneg ‖aliveExt G k (buildU s ω)‖)
      ((integrable_const (2048 ^ 2 * (1 / 536 : ℝ) ^ k)).add hO)
      (Eventually.of_forall fun ω => norm_aliveExt_sq_le G hG k (buildU s ω))
    refine hc.trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    rw [integral_add (integrable_const _) hO, integral_const, probReal_univ, one_smul]
  have h536 : 2048 ^ 2 * (1 / 536 : ℝ) ^ k ≤ (2048 * (1 / 16 : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) k) (by norm_num)
  have hb : (0 : ℝ) ≤ ∫ ω, ‖aliveOff G k (buildU s ω)‖ ∂coinMeasure :=
    integral_nonneg fun _ => norm_nonneg _
  have hX : (0 : ℝ) ≤ 2048 * (1 / 16 : ℝ) ^ k := by positivity
  have hcs := sq_integral_norm_comp_buildU_le s (aliveExt G k)
  have hI : (0 : ℝ) ≤ ∫ ω, ‖aliveExt G k (buildU s ω)‖ ∂coinMeasure :=
    integral_nonneg fun _ => norm_nonneg _
  have hsq := Real.sq_sqrt hb
  have hsn := Real.sqrt_nonneg (∫ ω, ‖aliveOff G k (buildU s ω)‖ ∂coinMeasure)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Off-diagonal node ⇒ `resLaw`-native node.**  Proved (diagonal by `geomNear_le`). -/
theorem aliveObstacleMix_of_off {b : ℕ} (hb : 2 ≤ b) (hO : AliveOffMix b) : AliveObstacleMix b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hO h hh C
  refine ⟨1, fun N => 2048 * ((16 : ℝ) ^ C * 16 * 2 * 32) * (N : ℝ) ^ (-(1 : ℝ)) + K * W N,
    ((summable_sched_rpow one_pos).mul_left _).add (hW.mul_left K), fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc _ ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          (2048 * (1 / 16 : ℝ) ^ (t - stageOf b C n) +
            Real.sqrt (∫ ω, ‖aliveOff (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n)
              (buildU (stageOf b C n) ω)‖ ∂coinMeasure)) :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
          Finset.sum_le_sum fun t _ => sqrt_aliveSecond_le _ (norm_deadCorr_le_const _) _ _
    _ = 2048 * (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
          ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
            (1 / 16 : ℝ) ^ (t - stageOf b C n)) +
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
          ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
            Real.sqrt (∫ ω, ‖aliveOff (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n)
              (buildU (stageOf b C n) ω)‖ ∂coinMeasure) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2048 * ((16 : ℝ) ^ C * 16 * 2 * 32 * N) + K * (N : ℝ) ^ 2 * W N :=
        add_le_add (mul_le_mul_of_nonneg_left (geomNear_le hb C (c := 16) (by norm_num) N)
          (by norm_num)) (hK N hN)
    _ = _ := by simp only [Real.rpow_neg_one]; field_simp

theorem sqrt_aliveSib_le (G : List Bool → ℂ) (hG : ∀ v, ‖G v‖ ≤ 2048) (k s : ℕ) :
    ∫ ω, ‖aliveExt G k (buildU s ω)‖ ∂coinMeasure ≤
      2048 * (1 / 16 : ℝ) ^ k +
        Real.sqrt (∫ ω, ‖((sibSum G k (buildU s ω) : ℝ) : ℂ)‖ ∂coinMeasure) := by
  have hO : Integrable (fun ω => ‖((sibSum G k (buildU s ω) : ℝ) : ℂ)‖) coinMeasure :=
    (integrable_comp_buildU s (fun w => ((sibSum G k w : ℝ) : ℂ))).norm
  have hpt : ∀ ω, ‖aliveExt G k (buildU s ω)‖ ^ 2 ≤
      2048 ^ 2 * (1 / 536 : ℝ) ^ k + ‖((sibSum G k (buildU s ω) : ℝ) : ℂ)‖ := fun ω => by
    refine (norm_aliveExt_sq_le_sib G hG k _).trans (add_le_add le_rfl ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  have hle : ∫ ω, ‖aliveExt G k (buildU s ω)‖ ^ 2 ∂coinMeasure ≤
      2048 ^ 2 * (1 / 536 : ℝ) ^ k + ∫ ω, ‖((sibSum G k (buildU s ω) : ℝ) : ℂ)‖ ∂coinMeasure := by
    have hc := integral_mono_of_nonneg (μ := coinMeasure)
      (Eventually.of_forall fun ω => sq_nonneg ‖aliveExt G k (buildU s ω)‖)
      ((integrable_const (2048 ^ 2 * (1 / 536 : ℝ) ^ k)).add hO) (Eventually.of_forall hpt)
    refine hc.trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    rw [integral_add (integrable_const _) hO, integral_const, probReal_univ, one_smul]
  have h536 : 2048 ^ 2 * (1 / 536 : ℝ) ^ k ≤ (2048 * (1 / 16 : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) k) (by norm_num)
  have hb : (0 : ℝ) ≤ ∫ ω, ‖((sibSum G k (buildU s ω) : ℝ) : ℂ)‖ ∂coinMeasure :=
    integral_nonneg fun _ => norm_nonneg _
  have hX : (0 : ℝ) ≤ 2048 * (1 / 16 : ℝ) ^ k := by positivity
  have hcs := sq_integral_norm_comp_buildU_le s (aliveExt G k)
  have hI : (0 : ℝ) ≤ ∫ ω, ‖aliveExt G k (buildU s ω)‖ ∂coinMeasure :=
    integral_nonneg fun _ => norm_nonneg _
  have hsq := Real.sq_sqrt hb
  have hsn := Real.sqrt_nonneg (∫ ω, ‖((sibSum G k (buildU s ω) : ℝ) : ℂ)‖ ∂coinMeasure)
  nlinarith

/-- **Sibling node** (refines `AliveOffMix`).  Believed 45% for `3 ∤ b`.  The near-scale root sums of
the `resLaw` expectation of the depth-weighted sibling correlations `sibSum` of the stage dead
corrections are `O(N² W(N))`.  Each sibling term compares the continuations below two distinct alive
children of one node, so this is a one-step decorrelation statement, applied at every depth between
`s_n` and `t`.  Implies `AliveObstacleMix b` (`aliveObstacleMix_of_sib`). -/
def AliveSibMix (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ C : ℕ, ∃ (K : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          Real.sqrt (∫ ω, ‖((sibSum (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n)
            (buildU (stageOf b C n) ω) : ℝ) : ℂ)‖ ∂coinMeasure) ≤ K * (N : ℝ) ^ 2 * W N

set_option maxHeartbeats 1000000 in
/-- **Sibling node ⇒ `resLaw`-native node.**  Proved. -/
theorem aliveObstacleMix_of_sib {b : ℕ} (hb : 2 ≤ b) (hO : AliveSibMix b) : AliveObstacleMix b := by
  intro h hh C
  obtain ⟨K, W, hW, hK⟩ := hO h hh C
  refine ⟨1, fun N => 2048 * ((16 : ℝ) ^ C * 16 * 2 * 32) * (N : ℝ) ^ (-(1 : ℝ)) + K * W N,
    ((summable_sched_rpow one_pos).mul_left _).add (hW.mul_left K), fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc _ ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
        ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
          (2048 * (1 / 16 : ℝ) ^ (t - stageOf b C n) +
            Real.sqrt (∫ ω, ‖((sibSum (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n)
              (buildU (stageOf b C n) ω) : ℝ) : ℂ)‖ ∂coinMeasure)) :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
          Finset.sum_le_sum fun t _ => sqrt_aliveSib_le _ (norm_deadCorr_le_const _) _ _
    _ = 2048 * (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
          ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
            (1 / 16 : ℝ) ^ (t - stageOf b C n)) +
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m,
          ∑ t ∈ Finset.Ico (stageOf b C m) (stageOf b C m + (Nat.log 3 N + 1)),
            Real.sqrt (∫ ω, ‖((sibSum (deadCorr (h * (b : ℝ) ^ m)) (t - stageOf b C n)
              (buildU (stageOf b C n) ω) : ℝ) : ℂ)‖ ∂coinMeasure) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2048 * ((16 : ℝ) ^ C * 16 * 2 * 32 * N) + K * (N : ℝ) ^ 2 * W N :=
        add_le_add (mul_le_mul_of_nonneg_left (geomNear_le hb C (c := 16) (by norm_num) N)
          (by norm_num)) (hK N hN)
    _ = _ := by simp only [Real.rpow_neg_one]; field_simp
/-- **The crux** (open; believed 45%).  `resLaw` satisfies `AliveOffMix`: the path-weighted pair
correlation of the stage dead corrections over distinct `resLaw` completions of the coarse prefix.
This single node replaces the former first-order (`ResLawObstOff`) and defect
(`DefectObstacleMix`) nodes of the split route (`nearObstaclePhaseMixing_of_split`, whose proved
reductions are kept above): the `resLaw` path weights already contain the alive defects.  Whether the
base-3 barrier binds this node or only the Cantor main term is undecided; the controlled probe at
`AliveOffMix` shows no base-3 coherence at the single-pair level. -/
theorem aliveOffMix_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    AliveOffMix b := by
  sorry

/-- The near-scale node for `resLaw` (from the single crux, by the `resLaw`-native route). -/
theorem nearObstaclePhaseMixing_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    NearObstaclePhaseMixing b :=
  nearObstaclePhaseMixing_of_alive (by omega) (aliveObstacleMix_of_off hb (aliveOffMix_resLaw hb h3))

/-- The obstacle-phase node for `resLaw` (proved from the near-scale crux). -/
theorem obstaclePhaseMixing_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    ObstaclePhaseMixing b :=
  obstaclePhaseMixing_of_near hb (nearObstaclePhaseMixing_resLaw hb h3)

/-- **The crux, mixing form** (proved from `obstaclePhaseMixing_resLaw`; believed 60%).
`resLaw` satisfies `LocalBiasMixing` in every base `b ≥ 2` prime to 3. -/
theorem localBiasMixing_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : LocalBiasMixing b :=
  localBiasMixing_of_obstaclePhase hb (obstaclePhaseMixing_resLaw hb h3)

/-- **The moment form of the crux** (proved from `localBiasMixing_resLaw`; believed 65%: stronger than `LocalDeadBias`, which it
implies via `localDeadBias_of_rate`).  `resLaw` satisfies `LocalBiasRate` in every base `b ≥ 2`
prime to 3.  Same guards as `localDeadBias_resLaw`: a proof must use the uniformity of the
resampled block and `3 ∤ b`. -/
theorem localBiasRate_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : LocalBiasRate b :=
  localBiasRate_of_mixing (localBiasMixing_resLaw hb h3)

/-- **The local form of the crux** (believed 75%; proved from the moment form `localBiasRate_resLaw`).  `resLaw` satisfies `LocalDeadBias` in every
base `b ≥ 2` prime to 3.  See `LocalDeadBias` for the content, the evidence and the controls.
A proof must use the uniformity of the resampled block (any-rule arguments reduce to
`DeadRateDecay`, believed false) and `3 ∤ b` (`not_casselsRate_three`). -/
theorem localDeadBias_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : LocalDeadBias b :=
  localDeadBias_of_rate (localBiasRate_resLaw hb h3)

/-- Weyl's criterion along the orbit `bᵏ x`.  Proved (the closing step of
`CantorLiouvilleAll.ae_isNormal_of_secondMoment`). -/
theorem isNormal_of_weylMeans {b : ℕ} (hb : 2 ≤ b) (x : ℝ)
    (hx : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * x)) / (N : ℂ)) atTop (𝓝 0)) :
    IsNormal b x := by
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  refine (hx h hh).congr fun N => ?_
  rw [LevinSparse.fourierMean_orbit]

/-- **The local reduction.**  Proved from `ae_cesaro_condDiff`, `cesaro_contChar_small` and
Weyl's criterion: `LocalDeadBias` gives almost-sure normality of `resLaw`, with no rate. -/
theorem ae_isNormal_resLaw_of_localDeadBias {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b)
    (hL : LocalDeadBias b) : ∀ᵐ ω ∂coinMeasure, IsNormal b (cpt (descentU ω)) := by
  have key : ∀ h : ℤ, h ≠ 0 → ∀ᵐ ω ∂coinMeasure, Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (descentU ω))) / (N : ℂ))
      atTop (𝓝 0) := by
    intro h hh
    have hM := ae_all_iff.2 fun C : ℕ => ae_cesaro_condDiff hb h C
    have hB := ae_all_iff.2 fun C : ℕ => hL h hh C
    filter_upwards [hM, hB] with ω hMω hBω
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨C, hC⟩ := cesaro_contChar_small hb h3 h hh (ε := ε / 3) (by positivity)
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (hMω C) (ε / 3) (by positivity)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (hBω C) (ε / 3) (by positivity)
    obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 hC
    refine ⟨max (max N₁ N₂) N₃, fun N hN => ?_⟩
    have h1 := hN₁ N (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN))
    have h2 := hN₂ N (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
    have h3' := hN₃ N (le_trans (le_max_right _ _) hN)
    rw [dist_zero_right] at h1 h2 ⊢
    set s : ℕ → ℕ := fun n => stageOf b C n
    set Y : ℕ → ℂ := fun n => ee (h * (b : ℝ) ^ n * cpt (descentU ω)) -
      condChar (h * (b : ℝ) ^ n) (s n) (buildU (s n) ω)
    set B : ℕ → ℂ := fun n => localBias b C h n ω
    set K : ℕ → ℂ := fun n => contChar (h * (b : ℝ) ^ n) (buildU (s n) ω)
    have hdec : ∀ n, ee (h * (b : ℝ) ^ n * cpt (descentU ω)) = Y n + B n + K n := by
      intro n; simp only [Y, B, K, localBias, s]; ring
    have hK : ‖(∑ n ∈ Finset.range N, K n) / (N : ℂ)‖ ≤ ε / 3 := by
      rw [norm_div, Complex.norm_natCast]
      refine le_trans ?_ h3'
      gcongr
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
      simp only [K, norm_contChar, length_buildU, s]
    have hsplit : (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (descentU ω))) / (N : ℂ) =
        (∑ n ∈ Finset.range N, Y n) / (N : ℂ) + (∑ n ∈ Finset.range N, B n) / (N : ℂ) +
          (∑ n ∈ Finset.range N, K n) / (N : ℂ) := by
      simp_rw [hdec, Finset.sum_add_distrib, add_div]
    rw [hsplit]
    calc _ ≤ ‖(∑ n ∈ Finset.range N, Y n) / (N : ℂ)‖ + ‖(∑ n ∈ Finset.range N, B n) / (N : ℂ)‖ +
          ‖(∑ n ∈ Finset.range N, K n) / (N : ℂ)‖ := norm_add₃_le
      _ < ε / 3 + ε / 3 + ε / 3 := by
          have e1 : ‖(∑ n ∈ Finset.range N, Y n) / (N : ℂ)‖ < ε / 3 := h1
          have e2 : ‖(∑ n ∈ Finset.range N, B n) / (N : ℂ)‖ < ε / 3 := h2
          linarith
      _ = ε := by ring
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (descentU ω))) / (N : ℂ))
      atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Eventually.of_forall fun ω hne => absurd hh hne
    · filter_upwards [key h hh] with ω hω _ using hω
  filter_upwards [hall] with ω hω
  exact isNormal_of_weylMeans hb _ hω

/-- **The reduction, almost-sure form.**  Proved: a law on `K ∩ Bad` that is almost surely
normal in every base prime to 3 has a point with all three properties. -/
theorem exists_of_law_ae (L : Law)
    (hL : ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → ∀ᵐ ω ∂coinMeasure, IsNormal b (cpt (L.φ ω))) :
    ∃ x : ℝ, x ∈ cantorSet ∧ x ∈ Bad ∧ ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b x := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cpt (L.φ ω)) := by
    rw [ae_all_iff]; intro b
    by_cases hb : 2 ≤ b
    · by_cases h3 : 3 ∣ b
      · exact Eventually.of_forall fun _ _ h => absurd h3 h
      · filter_upwards [hL b hb h3] with ω hω _ _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hb
  obtain ⟨ω, hω⟩ := hall.exists
  exact ⟨_, cpt_mem_cantorSet _, L.bad ω, hω⟩

/-- **A badly approximable point of the middle-third Cantor set, normal to every base prime to 3.**

Believed true, confidence 90%; Lean 15%.

English sketch.  Build a measure `ν` on `K ∩ BAD` by a descent through triadic Cantor
intervals that deletes, at each stage, the children too close to a rational `p/q` of the
current height (the `Bad` potential, BFS §3), while keeping at least two children alive so `ν`
has positive Frostman exponent.  Then run Cassels' second-moment argument for `ν`: bound
`∫ |N⁻¹ Σ_{n<N} e(h bⁿ x)|² dν` for `3 ∤ b`, sum over a sparse sequence of `N`, and conclude
`ν`-almost every point is normal to every base prime to 3.

The crux (unproved premise) is that second moment for a game-built, non-product `ν`.  The
sweep (§2.3) shows per-block total-variation closeness to the product Cantor measure is not
enough by itself.  A mechanism must keep the Fourier saving of `K`'s product structure at the
scales where the `Bad` deletions are sparse, which is most scales: a deletion at height `q`
removes `O(1)` children among `≍ q` triadic intervals.

Known-false siblings the mechanism must fail on:
* `b = 3` (`cantor_not_normal_three_pow`): no Cantor point is normal in base `3ᵏ`, so the
  second-moment bound must use `3 ∤ b`;
* the game alone (`schmidt_normal_not_winning`): normality is not potential winning, so the
  normality half cannot come from the deletion game and must come from the measure.

Evidence: each pair of the three sets meets, with full-dimensional `K ∩ BAD`; Hochman–Shmerkin
and Cassels give normality to bases prime to 3 for many non-product measures on `K`.

Lean route (lap 6).  `ν = resLaw` (dead blocks resampled uniformly from fresh coins), then
`exists_of_law_ae` and the local reduction `ae_isNormal_resLaw_of_localDeadBias`.  The open
leaves are `localDeadBias_resLaw` (the crux) and the two standard leaves `ae_cesaro_condDiff`,
`cesaro_contChar_small`. -/
theorem exists_mem_cantorSet_bad_isNormal_coprime_three :
    ∃ x : ℝ, x ∈ cantorSet ∧ x ∈ Bad ∧ ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b x :=
  exists_of_law_ae resLaw fun _ hb h3 =>
    ae_isNormal_resLaw_of_localDeadBias hb h3 (localDeadBias_resLaw hb h3)

end NormalNumbers.CantorBadNormal
