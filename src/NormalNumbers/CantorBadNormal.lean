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

open Classical in
/-- The alive children of `w`, as a finset of selector blocks. -/
noncomputable def aliveSet (w : List Bool) : Finset (Fin 10 → Bool) :=
  Finset.univ.filter fun f => Alive 5 c₀ w (List.ofFn f)

/-- **Conditional uniformity of the resampled block** (open leaf, believed 97%; standard
rejection sampling).  Given the prefix `w` after `s` stages, each alive child `v` is the next
block with probability `1/|A(w)|`.  English proof: the stage-`s` coin blocks `blk ω s t` are
i.i.d. uniform and independent of `buildU s` (which reads only blocks `pair(s', t)`, `s' < s`);
the first alive one among i.i.d. uniform draws is uniform on `A(w)`, and `|A(w)| ≥ 536 > 0`
(`card_dead_le`) so one exists a.s. -/
theorem buildU_succ_uniform (s : ℕ) (w v : List Bool) (hv : v.length = 10 ∧ Alive 5 c₀ w v) :
    coinMeasure {ω | buildU (s + 1) ω = w ++ v} * (aliveSet w).card =
      coinMeasure {ω | buildU s ω = w} := by
  sorry

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

/-- **Telescoping identity for `resLaw`** (open leaf, believed 90%).
`μ̂_K(ξ) − ν̂(ξ) = Σ_S deadChar(ξ, S) · μ̂_K(ξ 3^{−10S−10})`, absolutely convergent.

English proof.  `ν̂_{S+1}(ξ) − ν̂_S(ξ) = E_ν[e(ξ·cylLeft w_S)(ψ_S(w_S) − ρ_S)]·μ̂_K(ξ3^{−10S−10})`,
where `ψ_S(w) = |A(w)|⁻¹ Σ_{f∈A(w)} e(ξ J f 3^{−10S−10})` is the conditional block character
(`buildU_succ_uniform`) and the tail after stage `S` is an independent rescaled Cantor point.
`ψ − ρ = −deadErr`.  Absolute convergence: `|deadErr| ≤ 4π|ξ|3^{−10S}` (each `e_f − ρ` is),
and `ν̂_S → ν̂` since `cpt` of `ν_S` and of `ν` agree on `10S` digits. -/
theorem resLaw_fourier_telescope (ξ : ℝ) :
    HasSum (fun S => deadChar ξ S * muK (ξ / 3 ^ (10 * S + 10)))
        (muK ξ - ∫ ω, ee (ξ * cpt (resLaw.φ ω)) ∂coinMeasure) ∧
      Summable fun S => ‖deadChar ξ S‖ * ‖muK (ξ / 3 ^ (10 * S + 10))‖ := by
  sorry

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

/-- **Cassels for `μ_K`** (open leaf, believed 99%): the pair sum of `|μ̂_K|` over the
frequencies `h(bⁿ − bᵐ)` has a power saving.  This is the bound inside
`CantorLiouvilleAll.secondMoment_le_explicit_b` with `free = fun _ => true` (there it is applied
to the second moment; `charFun_real` bounds `|μ̂|` by the truncated product `Bf`). -/
theorem cassels_muK {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖muK (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))‖ ≤
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
  have hmu : ∀ ξ : ℝ, ‖muK ξ‖ ≤ CantorLiouville.Bf (fun _ => true) (Nat.log 3 N / 2) ξ :=
    fun ξ => CantorLiouville.charFun_real _ _ ξ
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hr2 : (0 : ℝ) ≤ Real.exp c * (N : ℝ) ^ (-δ) := by positivity
  have hEN := hE N hN
  calc _ ≤ _ := Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hmu _
    _ ≤ _ := hB
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + K * (N : ℝ) ^ 2 * (Real.exp c * (N : ℝ) ^ (-δ)) := by
        have := mul_le_mul_of_nonneg_left hEN (mul_nonneg hK hN2)
        simp only [K] at this ⊢
        linarith
    _ ≤ _ := by nlinarith [mul_nonneg hN2 hr, mul_nonneg hN2 hr2, mul_nonneg (mul_nonneg hK hN2) hr]

/-- **The crux: cancellation in the dead-children characters.**  Believed, confidence 55%.

`Σ_{n,m<N} Σ_S |deadChar(ξ, S)|·|μ̂_K(ξ3^{−10S−10})| = O(N² W(N))`, `ξ = h(bⁿ − bᵐ)`.  The
Cantor tail factor localizes `S` to `O(1)` stages near `log₃|ξ|/10` on average over `(n, m)`
(as in `cassels_muK`).  At those stages a dead child sits within `c₀/q²` of an obstacle `p/q`,
`q² ≍ 3^{10S}`, so `deadChar ≈ E_ν Σ_{p/q near w} e(ξ p/q)·(…)`: an exponential sum of
`h bⁿ p/q` over rationals near `K`, weighted by `ν`.  The bound needs cancellation in `n` of
`e(h bⁿ p / q)`, i.e. `b` generating a large subgroup mod most `q` near `K`.  The trivial bound
`|deadChar| ≤ 2·P(dead at S)` is the `DeadRateDecay` route (believed false).

Guards: `b = 3` is false (`cantor_not_normal_three_pow`; `3ⁿ p/q` with `q | 3^k` does not
cancel), and the base-2 dyadic sibling (`perStage_deadCount_not_enough`) has centres `p/2ᵏ`,
for which `e(2ⁿ p/2ᵏ) = 1` once `n ≥ k`: no cancellation, as required. -/
theorem deadCharCancel {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑' S, ‖deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S‖ *
          ‖muK (h * ((b : ℝ) ^ n - (b : ℝ) ^ m) / 3 ^ (10 * S + 10))‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  sorry

/-- Pointwise: `|ν̂| ≤ |μ̂_K| + Σ_S |deadChar|·|μ̂_K(·/3^{10S+10})|`.  Proved from the telescope. -/
theorem fourierAbs_resLaw_le (ξ : ℝ) :
    fourierAbs resLaw ξ ≤ ‖muK ξ‖ +
      ∑' S, ‖deadChar ξ S‖ * ‖muK (ξ / 3 ^ (10 * S + 10))‖ := by
  obtain ⟨hS, hN⟩ := resLaw_fourier_telescope ξ
  have heq : (∫ ω, ee (ξ * cpt (resLaw.φ ω)) ∂coinMeasure) =
      muK ξ - ∑' S, deadChar ξ S * muK (ξ / 3 ^ (10 * S + 10)) := by
    rw [hS.tsum_eq]; ring
  unfold fourierAbs
  rw [heq]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun S => norm_mul _ _))
  exact hN.congr fun S => (norm_mul _ _).symm

/-- **The crux for the resampling law**, from the decomposition.  Proved modulo the leaves
`resLaw_fourier_telescope`, `cassels_muK` and `deadCharCancel`.

The mechanism uses uniformity through `resLaw_fourier_telescope`: a proof that uses only that
the stage block is alive (any admissible rule) reduces to `DeadRateDecay` (believed false), and
per-stage dead counts alone are refuted by `perStage_deadCount_not_enough` (whose sibling with
uniform resampling is still never 2-normal).  So `deadCharCancel` must use the arithmetic of
the centres `p/q`.  Known-false sibling: `b = 3` (`cantor_not_normal_three_pow`). -/
theorem fourierPairRate_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    FourierPairRate resLaw b := by
  intro h hh
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := cassels_muK hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := deadCharCancel hb h3 h hh
  refine ⟨|C₁| + |C₂|, fun N => |W₁ N| + |W₂ N|, hW₁.abs.add hW₂.abs, fun N hN => ?_⟩
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (‖muK (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))‖ +
            ∑' S, ‖deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S‖ *
              ‖muK (h * ((b : ℝ) ^ n - (b : ℝ) ^ m) / 3 ^ (10 * S + 10))‖) :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => fourierAbs_resLaw_le _
    _ = _ + _ := by simp only [Finset.sum_add_distrib]
    _ ≤ C₁ * (N : ℝ) ^ 2 * W₁ N + C₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add (h₁ N hN) (h₂ N hN)
    _ ≤ |C₁| * (N : ℝ) ^ 2 * |W₁ N| + |C₂| * (N : ℝ) ^ 2 * |W₂ N| := by
        have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
          (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
        exact add_le_add (k _ _) (k _ _)
    _ ≤ _ := by
        have := abs_nonneg C₁; have := abs_nonneg C₂
        have := abs_nonneg (W₁ N); have := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg (abs_nonneg C₁) hN2) (abs_nonneg (W₂ N)),
          mul_nonneg (mul_nonneg (abs_nonneg C₂) hN2) (abs_nonneg (W₁ N))]


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
and Cassels give normality to bases prime to 3 for many non-product measures on `K`. -/
theorem exists_mem_cantorSet_bad_isNormal_coprime_three :
    ∃ x : ℝ, x ∈ cantorSet ∧ x ∈ Bad ∧ ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b x :=
  exists_of_law resLaw fun _ hb h3 => casselsRate_of_fourierPairRate (fourierPairRate_resLaw hb h3)

end NormalNumbers.CantorBadNormal
