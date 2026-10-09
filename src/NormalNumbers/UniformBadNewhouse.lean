/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadThreshold

/-!
# The Newhouse route to `c⋆ ≤ 4`

**Idea (c⋆ lap 5).**  Counting and potential engines lose a dimension deficit: they charge a
window against a sparse alive set (`UniformBadJoint`, Maze row "counted medium bases").  The
Newhouse gap lemma has no such loss: two compact sets with thicknesses `τ₁ τ₂ > 1`, neither inside
a gap of the other, intersect.  Split the bases as `{2}` against `{b ≥ 3}`:

* `A = E₂(4) = {x ∈ [0,1] : ‖2ⁿx‖ ≥ 2⁻⁴ ∀ n}` has thickness exactly `3` (`thick_E2_four`).  Its
  gaps are `A/2ⁿ ± 2⁻ⁿ/15` (each window `A/2ⁿ ± 2^{−n−4}` absorbs the cascade of windows at its
  edges, `1/15 = 0.000100010001…₂`); the worst ratio is the gap around `1/8`, of length `1/60`,
  with bridge `1/20` to the gap around `0`.
* `B ⊆ ⋂_{b ≥ 3} E_b(4)` must be compact with thickness `> 1/3` (`ThickCore`).  The raw intersection
  has thickness `0` (windows of different bases can nearly touch), but merging the near-touching
  windows costs almost nothing: probe `scripts/cstar_models/thick.py`,
  `merge.py` (bases `3 … 40`, all windows of length `≥ 3·10⁻⁷`): forcing thickness `0.4 / 1 / 2`
  needs `26 / 64 / 126` merges among `≈ 56 700` gaps, and the hull `[1/80, 79/80]` is untouched.
* The intersection point then has `‖bⁿξ‖ ≥ b⁻⁴` for every `b ≥ 2` (`cStar_le_four_of_newhouse`).

Control (known answer): below the lower bound `c⋆ ≥ 12/5` the same probe collapses (`c = 2.2, 2.4`:
the merged `E₂` shrinks to a neighbourhood of `2/3` and the merged `B` has thickness `< 0.005`).
At `c = 3`, `τ(E₂(3)) = 1` and the merged `B` reaches `1.05`, so the route plausibly gives `c⋆ ≤ 3`
as well (`CStarLeThree`), with a thin margin.
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear dnear_le_abs_sub)

namespace Newhouse

/-- `(a, b)` is a bounded gap of `K`: its endpoints lie in `K` and it misses `K`. -/
def IsGap (K : Set ℝ) (a b : ℝ) : Prop := a < b ∧ a ∈ K ∧ b ∈ K ∧ Disjoint (Set.Ioo a b) K

/-- Newhouse thickness at least `τ`, in the separation form (Falconer–Yavicoli, Definition 3,
symmetrised): two disjoint gaps are at distance at least `τ` times the shorter one, and every gap
is at distance at least `τ` times its length from the ends of the convex hull. -/
def Thick (K : Set ℝ) (τ : ℝ) : Prop :=
  (∀ a b a' b', IsGap K a b → IsGap K a' b' → b ≤ a' →
      τ * min (b - a) (b' - a') ≤ a' - b) ∧
    ∀ a b, IsGap K a b → τ * (b - a) ≤ a - sInf K ∧ τ * (b - a) ≤ sSup K - b

/-- The gaps `(a, b)` of `K` and `(a', b')` of `L` are linked, with the `K`-gap on the left:
each contains exactly one endpoint of the other. -/
def Linked (K L : Set ℝ) (a b a' b' : ℝ) : Prop :=
  IsGap K a b ∧ IsGap L a' b' ∧ a < a' ∧ a' < b ∧ b < b'

/-- A point of the hull of a compact set that misses the set lies in a gap, whose endpoints are the
nearest points of the set on either side. -/
lemma exists_gap_of_not_mem {K : Set ℝ} (hK : IsCompact K) {x l r : ℝ} (hl : l ∈ K) (hr : r ∈ K)
    (hlx : l ≤ x) (hxr : x ≤ r) (hx : x ∉ K) :
    ∃ c d, IsGap K c d ∧ c < x ∧ x < d ∧ (∀ k ∈ K, k ≤ x → k ≤ c) ∧
      (∀ k ∈ K, x ≤ k → d ≤ k) := by
  have hc1 : IsCompact (K ∩ Set.Iic x) := hK.inter_right isClosed_Iic
  have hc2 : IsCompact (K ∩ Set.Ici x) := hK.inter_right isClosed_Ici
  obtain ⟨hcK, hcx⟩ := hc1.sSup_mem ⟨l, hl, hlx⟩
  obtain ⟨hdK, hdx⟩ := hc2.sInf_mem ⟨r, hr, hxr⟩
  have hle : ∀ k ∈ K, k ≤ x → k ≤ sSup (K ∩ Set.Iic x) := fun k hk hkx =>
    le_csSup hc1.bddAbove ⟨hk, hkx⟩
  have hge : ∀ k ∈ K, x ≤ k → sInf (K ∩ Set.Ici x) ≤ k := fun k hk hkx =>
    csInf_le hc2.bddBelow ⟨hk, hkx⟩
  have hcx' : sSup (K ∩ Set.Iic x) < x :=
    lt_of_le_of_ne hcx (fun h => hx (by rw [← h]; exact hcK))
  have hdx' : x < sInf (K ∩ Set.Ici x) :=
    lt_of_le_of_ne hdx (fun h => hx (by rw [h]; exact hdK))
  refine ⟨_, _, ⟨hcx'.trans hdx', hcK, hdK, ?_⟩, hcx', hdx', hle, hge⟩
  rw [Set.disjoint_left]
  rintro y ⟨hy1, hy2⟩ hyK
  rcases le_total y x with h | h
  · exact absurd (hle y hyK h) (not_le.2 hy1)
  · exact absurd (hge y hyK h) (not_le.2 hy2)

/-- A gap is determined by its left endpoint. -/
lemma IsGap.right_unique {K : Set ℝ} {a b b' : ℝ} (h : IsGap K a b) (h' : IsGap K a b') :
    b = b' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact Set.disjoint_left.1 h'.2.2.2 ⟨h.1, hlt⟩ h.2.2.1
  · exact Set.disjoint_left.1 h.2.2.2 ⟨h'.1, hlt⟩ h'.2.2.1

/-- A compact set has only finitely many gaps of length at least `δ > 0`. -/
lemma finite_long_gaps {K : Set ℝ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    {a | ∃ b, IsGap K a b ∧ δ ≤ b - a}.Finite := by
  obtain ⟨M, hM⟩ := hK.bddAbove
  obtain ⟨m, hm⟩ := hK.bddBelow
  have key : ∀ a b a', IsGap K a b → δ ≤ b - a → (∃ b', IsGap K a' b') → a < a' →
      ⌊a / δ⌋ < ⌊a' / δ⌋ := by
    rintro a b a' hg hb ⟨b', hg'⟩ h
    have hba : b ≤ a' := by
      by_contra hlt
      push_neg at hlt
      exact Set.disjoint_left.1 hg.2.2.2 ⟨h, hlt⟩ hg'.2.1
    have h1 : a / δ + 1 ≤ a' / δ := by
      rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith
    have h2 := Int.floor_mono h1
    rw [Int.floor_add_one] at h2
    omega
  apply Set.Finite.of_finite_image (f := fun a => ⌊a / δ⌋)
  · apply (Set.finite_Icc ⌊m / δ⌋ ⌊M / δ⌋).subset
    rintro _ ⟨a, ⟨b, hg, -⟩, rfl⟩
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (hm hg.2.1) hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right (hM hg.2.1) hδ.le)⟩
  · rintro a ⟨b, hg, hb⟩ a' ⟨b', hg', hb'⟩ heq
    simp only at heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := key a b a' hg hb ⟨b', hg'⟩ h; omega
    · have := key a' b' a hg' hb' ⟨b, hg⟩ h; omega

/-- **Linked-pair descent** (the heart of the gap lemma).  From a linked pair, either the bridge of
`K` beyond `b` or the bridge of `L` before `a'` reaches a shorter gap, giving a linked pair (now with
the `L`-gap on the left) of strictly smaller total length; otherwise the two bridge inequalities
`τK|U| < |V|`, `τL|V| < |U|` contradict `τK τL > 1`. -/
lemma linked_descent {K L : Set ℝ} {τK τL : ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) (htK : Thick K τK) (htL : Thick L τL) (hτK : 0 < τK) (hτL : 0 < τL)
    (hτ : 1 < τK * τL) {a b a' b' : ℝ} (h : Linked K L a b a' b') :
    ∃ c d c' d', Linked L K c' d' c d ∧ (d - c) + (d' - c') < (b - a) + (b' - a') := by
  obtain ⟨hU, hV, h1, h2, h3⟩ := h
  have hb'K : b' ∉ K := fun hk => Set.disjoint_left.1 hKL hk hV.2.2.1
  have haL : a ∉ L := fun hl => Set.disjoint_left.1 hKL hU.2.1 hl
  have hR : (∃ c d, Linked L K a' b' c d ∧ d - c < b - a) ∨ τK * (b - a) < b' - a' := by
    by_cases hM : b' < sSup K
    · obtain ⟨c, d, hg, hc, hd, hle, -⟩ := exists_gap_of_not_mem hK hU.2.2.1
        (hK.sSup_mem ⟨_, hU.2.1⟩) h3.le hM.le hb'K
      have hbc : b ≤ c := hle b hU.2.2.1 h3.le
      by_cases hlen : d - c < b - a
      · exact Or.inl ⟨c, d, ⟨hV, hg, by linarith, hc, hd⟩, hlen⟩
      · right
        have := htK.1 a b c d hU hg hbc
        rw [min_eq_left (by linarith)] at this
        linarith
    · right
      push_neg at hM
      have := (htK.2 a b hU).2
      linarith
  have hL' : (∃ c' d', Linked L K c' d' a b ∧ d' - c' < b' - a') ∨ τL * (b' - a') < b - a := by
    by_cases hm : sInf L < a
    · obtain ⟨c', d', hg, hc, hd, -, hge⟩ := exists_gap_of_not_mem hL
        (hL.sInf_mem ⟨_, hV.2.1⟩) hV.2.1 hm.le h1.le haL
      have hda : d' ≤ a' := hge a' hV.2.1 h1.le
      by_cases hlen : d' - c' < b' - a'
      · exact Or.inl ⟨c', d', ⟨hg, hU, hc, hd, by linarith⟩, hlen⟩
      · right
        have := htL.1 c' d' a' b' hg hV hda
        rw [min_eq_right (by linarith)] at this
        linarith
    · right
      push_neg at hm
      have := (htL.2 a' b' hV).1
      linarith
  rcases hR with ⟨c, d, hl, hlen⟩ | hR
  · exact ⟨c, d, a', b', hl, by linarith⟩
  rcases hL' with ⟨c', d', hl, hlen⟩ | hL'
  · exact ⟨a, b, c', d', hl, by linarith⟩
  exfalso
  have hpos : 0 < b - a := by linarith [hU.1]
  have := mul_lt_mul_of_pos_left hR hτL
  nlinarith

/-- Existence of a first linked pair, from the hull and no-gap-containment conditions. -/
lemma exists_linked_init {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L)
    (hneK : K.Nonempty) (hneL : L.Nonempty) (hle : sInf K ≤ sInf L) (hhull : sInf L ≤ sSup K)
    (hgap : ¬ ∃ a b, IsGap K a b ∧ L ⊆ Set.Ioo a b) :
    ∃ a b a' b', Linked K L a b a' b' := by
  have hmL : sInf L ∈ L := hL.sInf_mem hneL
  have hmK : sInf L ∉ K := fun h => Set.disjoint_left.1 hKL h hmL
  obtain ⟨a, b, hg, ha, hb, -, hge⟩ := exists_gap_of_not_mem hK (hK.sInf_mem hneK)
    (hK.sSup_mem hneK) hle hhull hmK
  have hbL : b ∉ L := fun h => Set.disjoint_left.1 hKL hg.2.2.1 h
  have hbM : b ≤ sSup L := by
    by_contra hlt
    push_neg at hlt
    refine hgap ⟨a, b, hg, fun y hy => ⟨?_, ?_⟩⟩
    · exact ha.trans_le (csInf_le hL.bddBelow hy)
    · exact (le_csSup hL.bddAbove hy).trans_lt hlt
  obtain ⟨a', b', hg', ha', hb', hle', -⟩ := exists_gap_of_not_mem hL hmL (hL.sSup_mem hneL)
    hb.le hbM hbL
  have hma : sInf L ≤ a' := hle' _ hmL hb.le
  exact ⟨a, b, a', b', hg, hg', by linarith, ha', hb'⟩

/-- **Newhouse gap lemma** (Newhouse 1979; Falconer–Yavicoli 2022, Theorem 2), proved here for the
separation form of thickness.  Two compact sets with `τ₁ τ₂ > 1` whose hulls overlap and neither of which lies
inside a bounded gap of the other intersect.

English proof (Palis–Takens).  If not, the hull condition gives a linked pair of gaps `(U₁, U₂)`
(each contains exactly one endpoint of the other).  At the endpoints, the bridges `C₁, C₂` satisfy
`|C₁| ≥ τ₁|U₁|`, `|C₂| ≥ τ₂|U₂|`, so `|C₁| > |U₂|` or `|C₂| > |U₁|`; in the first case the far endpoint
of `U₂` lies in `C₁`, hence in a gap of `K₁` shorter than `U₁`, linked with `U₂`.  Gap lengths in a
compact set accumulate only at `0`; in Lean, linked pairs have both gaps longer than
`dist(K₁, K₂) > 0` (`finite_long_gaps`), so a linked pair of minimal total length exists and
`linked_descent` contradicts its minimality. -/
theorem gap_lemma {K₁ K₂ : Set ℝ} {τ₁ τ₂ : ℝ} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty) (ht₁ : Thick K₁ τ₁) (ht₂ : Thick K₂ τ₂)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ : 1 < τ₁ * τ₂)
    (hhull₁ : sInf K₁ ≤ sSup K₂) (hhull₂ : sInf K₂ ≤ sSup K₁)
    (hgap₁ : ¬ ∃ a b, IsGap K₁ a b ∧ K₂ ⊆ Set.Ioo a b)
    (hgap₂ : ¬ ∃ a b, IsGap K₂ a b ∧ K₁ ⊆ Set.Ioo a b) :
    (K₁ ∩ K₂).Nonempty := by
  by_contra hempty
  have hdisj : Disjoint K₁ K₂ :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hempty)
  obtain ⟨p, hp, hpmin⟩ := (h₁.prod h₂).exists_isMinOn (hne₁.prod hne₂)
    ((continuous_fst.sub continuous_snd).abs.continuousOn)
  have hδ : 0 < |p.1 - p.2| :=
    abs_pos.2 (sub_ne_zero.2 fun h => Set.disjoint_left.1 hdisj hp.1 (by rw [h]; exact hp.2))
  have hsep : ∀ x ∈ K₁, ∀ y ∈ K₂, |p.1 - p.2| ≤ |x - y| := fun x hx y hy => by
    simpa using hpmin (Set.mk_mem_prod hx hy)
  set δ := |p.1 - p.2|
  -- the linked pairs, as `(a₁, b₁, a₂, b₂)` with `(a₁, b₁)` a gap of `K₁`, `(a₂, b₂)` one of `K₂`
  let P : Set (ℝ × ℝ × ℝ × ℝ) := {q | Linked K₁ K₂ q.1 q.2.1 q.2.2.1 q.2.2.2 ∨
    Linked K₂ K₁ q.2.2.1 q.2.2.2 q.1 q.2.1}
  have hP : ∀ q ∈ P, IsGap K₁ q.1 q.2.1 ∧ IsGap K₂ q.2.2.1 q.2.2.2 ∧ δ ≤ q.2.1 - q.1 ∧
      δ ≤ q.2.2.2 - q.2.2.1 := by
    rintro ⟨a, b, a', b'⟩ (⟨hU, hV, h1, h2, h3⟩ | ⟨hV, hU, h1, h2, h3⟩)
    · have := hsep b hU.2.2.1 a' hV.2.1
      rw [abs_of_pos (by linarith)] at this
      exact ⟨hU, hV, by simp only; linarith, by simp only; linarith⟩
    · have := hsep a hU.2.1 b' hV.2.2.1
      rw [abs_of_neg (by linarith)] at this
      exact ⟨hU, hV, by simp only; linarith, by simp only; linarith⟩
  have hfin : P.Finite := by
    apply Set.Finite.of_finite_image (f := fun q => (q.1, q.2.2.1))
    · apply ((finite_long_gaps h₁ hδ).prod (finite_long_gaps h₂ hδ)).subset
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨hU, hV, hl1, hl2⟩ := hP q hq
      exact ⟨⟨_, hU, hl1⟩, ⟨_, hV, hl2⟩⟩
    · rintro ⟨a, b, a', b'⟩ hq ⟨c, d, c', d'⟩ hq' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨hU, hV, -⟩ := hP _ hq
      obtain ⟨hU', hV', -⟩ := hP _ hq'
      have e1 := hU.right_unique hU'
      have e2 := hV.right_unique hV'
      simp only at e1 e2
      rw [e1, e2]
  have hne : P.Nonempty := by
    rcases le_total (sInf K₁) (sInf K₂) with hle | hle
    · obtain ⟨a, b, a', b', hl⟩ :=
        exists_linked_init h₁ h₂ hdisj hne₁ hne₂ hle hhull₂ hgap₁
      exact ⟨(a, b, a', b'), Or.inl hl⟩
    · obtain ⟨a', b', a, b, hl⟩ :=
        exists_linked_init h₂ h₁ hdisj.symm hne₂ hne₁ hle hhull₁ hgap₂
      exact ⟨(a, b, a', b'), Or.inr hl⟩
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image P
    (fun q => (q.2.1 - q.1) + (q.2.2.2 - q.2.2.1)) hfin hne
  obtain ⟨a, b, a', b'⟩ := q
  rcases hq with hl | hl
  · obtain ⟨c, d, c', d', hl', hlt⟩ :=
      linked_descent h₁ h₂ hdisj ht₁ ht₂ hτ₁ hτ₂ hτ hl
    have := hmin (c, d, c', d') (Or.inr hl')
    simp only at this
    linarith
  · obtain ⟨c, d, c', d', hl', hlt⟩ :=
      linked_descent h₂ h₁ hdisj.symm ht₂ ht₁ hτ₂ hτ₁ (by linarith [mul_comm τ₁ τ₂]) hl
    have := hmin (c', d', c, d) (Or.inl hl')
    simp only at this
    linarith

/-- The base-`b` good set at exponent `c`: `‖bⁿx‖ ≥ b^{−c}` for every `n`. -/
def goodSet (c b : ℕ) : Set ℝ := {x | ∀ n : ℕ, ((b : ℝ) ^ c)⁻¹ ≤ dnear ((b : ℝ) ^ n * x)}

/-- `E₂(c)` on `[0, 1]`. -/
def E2 (c : ℕ) : Set ℝ := Set.Icc 0 1 ∩ goodSet c 2

/-- **Node, off the route** (the wiring uses `e15_facts` on `E15 ⊆ E₂(4)` instead; in fact
`E₂(4) = E15`, by the descent `‖2ⁿx‖ ∈ [1/16, 1/15) ⇒ ‖2ⁿ⁺⁴x‖ − 1/15 = 16(‖2ⁿx‖ − 1/15)`).
Believed 90%.  `E₂(4)` is compact, its hull is `[1/15, 14/15]`, its gaps have length
at most `1/15`, and its thickness is `3` (probe: `thick.py 4 1e-7 2` returns exactly `3.000`, at the
gap `(7/60, 2/15)`).  Proof plan: the gaps are `A/2ⁿ ± 2⁻ⁿ/15` (`A` odd), and the bridge from the
gap of order `n` to a gap of order `m ≤ n` is `(k − (2^{n−m} + 1)/15)·2⁻ⁿ` for the least admissible
integer `k`, whose ratio to `2·2⁻ⁿ/15` is at least `3`. -/
theorem e2_four_facts :
    IsCompact (E2 4) ∧ (1 / 15 : ℝ) ∈ E2 4 ∧ (14 / 15 : ℝ) ∈ E2 4 ∧ E2 4 ⊆ Set.Icc (1 / 15) (14 / 15) ∧
      (∀ a b, IsGap (E2 4) a b → b - a ≤ 1 / 15) ∧ Thick (E2 4) 3 := by
  sorry

/-! ### `E₂` at the exact scale `1/15`

`E15 = {x ∈ [0, 1] : ‖2ⁿx‖ ≥ 1/15 ∀ n} ⊆ E₂(4)`.  Its gaps are exactly the windows
`((A − 1/15)/2ⁿ, (A + 1/15)/2ⁿ)` (`gap_eq_window`), and two such windows are separated by three times
the shorter one, because `15k − 2ʲ ≥ 1` forces `15k − 2ʲ ≥ 7` (`2ʲ mod 15 ∈ {1, 2, 4, 8}`). -/

/-- `E₂` at scale `1/15`, inside `E₂(4)` (`E15_subset_goodSet`). -/
def E15 : Set ℝ := Set.Icc 0 1 ∩ {x | ∀ n : ℕ, ∀ z : ℤ, 1 / 15 ≤ |(2 : ℝ) ^ n * x - z|}

lemma E15_subset_goodSet : E15 ⊆ goodSet 4 2 := by
  intro x hx n
  have := hx.2 n (round ((2 : ℝ) ^ n * x))
  unfold dnear
  push_cast
  norm_num
  linarith

lemma two_pow_mod_fifteen (j : ℕ) :
    (2 : ℤ) ^ j % 15 = 1 ∨ (2 : ℤ) ^ j % 15 = 2 ∨ (2 : ℤ) ^ j % 15 = 4 ∨ (2 : ℤ) ^ j % 15 = 8 := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

lemma two_pow_mul_emod_ne {i : ℕ} {e : ℤ} (he : e % 15 = 1 ∨ e % 15 = 14) :
    (2 ^ i * e) % 15 ≠ 0 := by
  rw [Int.mul_emod]
  rcases two_pow_mod_fifteen i with h | h | h | h <;> rcases he with h' | h' <;> rw [h, h'] <;>
    norm_num

lemma one_fifteenth_le_abs {u : ℤ} (hu : u % 15 ≠ 0) (z : ℤ) : 1 / 15 ≤ |(u : ℝ) / 15 - z| := by
  have h1 : u - 15 * z ≠ 0 := by omega
  have h3 : (1 : ℝ) ≤ |(u : ℝ) - 15 * z| := by exact_mod_cast Int.one_le_abs h1
  have : (u : ℝ) / 15 - z = ((u : ℝ) - 15 * z) / 15 := by ring
  rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 15)]
  linarith

lemma sep_seven (j : ℕ) (k : ℤ) (h : 1 ≤ 15 * k - 2 ^ j) : 7 ≤ 15 * k - 2 ^ j := by
  have := two_pow_mod_fifteen j
  omega

/-- A window of order `m` to the left of a window of order `n ≥ m` is three of the latter's lengths
away. -/
lemma window_sep_left {m j : ℕ} {C A : ℤ}
    (h : ((C : ℝ) + 1 / 15) / 2 ^ m ≤ ((A : ℝ) - 1 / 15) / 2 ^ (m + j)) :
    3 * (2 / (15 * 2 ^ (m + j))) ≤ ((A : ℝ) - 1 / 15) / 2 ^ (m + j) - ((C : ℝ) + 1 / 15) / 2 ^ m := by
  have hP : (0 : ℝ) < 2 ^ m := by positivity
  have hQ : (0 : ℝ) < 2 ^ j := by positivity
  rw [pow_add] at h ⊢
  rw [div_le_div_iff₀ hP (by positivity)] at h
  have hi : (1 : ℝ) ≤ 15 * ((A - C * 2 ^ j : ℤ) : ℝ) - ((2 ^ j : ℤ) : ℝ) := by
    push_cast; nlinarith
  have h7 : (7 : ℝ) ≤ 15 * ((A - C * 2 ^ j : ℤ) : ℝ) - ((2 ^ j : ℤ) : ℝ) := by
    exact_mod_cast sep_seven j _ (by exact_mod_cast hi)
  push_cast at h7
  rw [show ((A : ℝ) - 1 / 15) / (2 ^ m * 2 ^ j) - ((C : ℝ) + 1 / 15) / 2 ^ m =
      (15 * (A - C * 2 ^ j) - 2 ^ j - 1) / (15 * (2 ^ m * 2 ^ j)) by field_simp; ring]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- A window of order `n ≥ m` to the left of a window of order `m`. -/
lemma window_sep_right {m j : ℕ} {C A : ℤ}
    (h : ((A : ℝ) + 1 / 15) / 2 ^ (m + j) ≤ ((C : ℝ) - 1 / 15) / 2 ^ m) :
    3 * (2 / (15 * 2 ^ (m + j))) ≤ ((C : ℝ) - 1 / 15) / 2 ^ m - ((A : ℝ) + 1 / 15) / 2 ^ (m + j) := by
  have hP : (0 : ℝ) < 2 ^ m := by positivity
  have hQ : (0 : ℝ) < 2 ^ j := by positivity
  rw [pow_add] at h ⊢
  rw [div_le_div_iff₀ (by positivity) hP] at h
  have hi : (1 : ℝ) ≤ 15 * ((C * 2 ^ j - A : ℤ) : ℝ) - ((2 ^ j : ℤ) : ℝ) := by
    push_cast; nlinarith
  have h7 : (7 : ℝ) ≤ 15 * ((C * 2 ^ j - A : ℤ) : ℝ) - ((2 ^ j : ℤ) : ℝ) := by
    exact_mod_cast sep_seven j _ (by exact_mod_cast hi)
  push_cast at h7
  rw [show ((C : ℝ) - 1 / 15) / 2 ^ m - ((A : ℝ) + 1 / 15) / (2 ^ m * 2 ^ j) =
      (15 * (C * 2 ^ j - A) - 2 ^ j - 1) / (15 * (2 ^ m * 2 ^ j)) by field_simp; ring]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  linarith

lemma E15_subset_Icc : E15 ⊆ Set.Icc (1 / 15) (14 / 15) := by
  intro x hx
  have h0 := hx.2 0 0
  have h1 := hx.2 0 1
  simp only [pow_zero, one_mul, Int.cast_zero, sub_zero, Int.cast_one] at h0 h1
  have := hx.1
  constructor
  · rw [abs_of_nonneg this.1] at h0; exact h0
  · rw [abs_of_nonpos (by linarith [this.2])] at h1; linarith

/-- `2ᵏ · (A ± 1/15)/2ⁿ` for `k ≥ n` is `u/15` with `15 ∤ u`. -/
lemma endpoint_good {n k : ℕ} (hnk : n ≤ k) {A : ℤ} {e : ℤ} (he : (15 * A + e) % 15 = 1 ∨
    (15 * A + e) % 15 = 14) (z : ℤ) :
    1 / 15 ≤ |(2 : ℝ) ^ k * (((A : ℝ) + e / 15) / 2 ^ n) - z| := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hnk
  have := one_fifteenth_le_abs (two_pow_mul_emod_ne (i := i) he) z
  convert this using 3
  push_cast
  rw [pow_add]
  field_simp

/-- **Every gap of `E15` is a window** `((A − 1/15)/2ⁿ, (A + 1/15)/2ⁿ)`. -/
lemma gap_eq_window {a b : ℝ} (h : IsGap E15 a b) :
    ∃ n : ℕ, ∃ A : ℤ, a = ((A : ℝ) - 1 / 15) / 2 ^ n ∧ b = ((A : ℝ) + 1 / 15) / 2 ^ n := by
  obtain ⟨hab, haE, hbE, hdis⟩ := h
  have hnot : ∀ w ∈ Set.Ioo a b, w ∉ E15 := fun w hw hwE => Set.disjoint_left.1 hdis hw hwE
  have hbad : ∀ w ∈ Set.Ioo a b, ∃ n : ℕ, ∃ z : ℤ, |(2 : ℝ) ^ n * w - z| < 1 / 15 := by
    intro w hw
    by_contra hc
    push_neg at hc
    exact hnot w hw ⟨⟨haE.1.1.trans hw.1.le, hw.2.le.trans hbE.1.2⟩, hc⟩
  have hP : ∃ n : ℕ, ∃ z : ℤ, ∃ w ∈ Set.Ioo a b, |(2 : ℝ) ^ n * w - z| < 1 / 15 := by
    obtain ⟨n, z, hz⟩ := hbad ((a + b) / 2) ⟨by linarith, by linarith⟩
    exact ⟨n, z, _, ⟨by linarith, by linarith⟩, hz⟩
  classical
  set n := Nat.find hP with hn
  obtain ⟨A, w, hw, hwA⟩ := Nat.find_spec hP
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  -- membership in the window
  have hwin : ∀ x : ℝ, ((A : ℝ) - 1 / 15) / 2 ^ n < x → x < ((A : ℝ) + 1 / 15) / 2 ^ n →
      x ∉ E15 := by
    intro x h1 h2 hx
    rw [div_lt_iff₀ hpos] at h1
    rw [lt_div_iff₀ hpos] at h2
    have := hx.2 n A
    exact absurd this (not_le.2 (abs_lt.2 ⟨by linarith, by linarith⟩))
  rw [abs_lt] at hwA
  have hw1 : ((A : ℝ) - 1 / 15) / 2 ^ n < w := by rw [div_lt_iff₀ hpos]; linarith
  have hw2 : w < ((A : ℝ) + 1 / 15) / 2 ^ n := by rw [lt_div_iff₀ hpos]; linarith
  -- an endpoint of the window lying strictly inside `(a, b)` is impossible
  have hend : ∀ e : ℤ, ((15 * A + e) % 15 = 1 ∨ (15 * A + e) % 15 = 14) →
      ((A : ℝ) + e / 15) / 2 ^ n ∉ Set.Ioo a b := by
    intro e he hin
    obtain ⟨k, z, hk⟩ := hbad _ hin
    rcases lt_or_ge k n with hkn | hkn
    · exact Nat.find_min hP hkn ⟨z, _, hin, hk⟩
    · exact absurd hk (not_lt.2 (endpoint_good hkn he z))
  refine ⟨n, A, ?_, ?_⟩
  · rcases lt_trichotomy a (((A : ℝ) - 1 / 15) / 2 ^ n) with h1 | h1 | h1
    · exfalso
      refine hend (-1) (by omega) ⟨?_, ?_⟩ <;> push_cast <;> [skip; skip]
      · rw [show ((A : ℝ) + -1 / 15) = (A : ℝ) - 1 / 15 by ring]; exact h1
      · rw [show ((A : ℝ) + -1 / 15) = (A : ℝ) - 1 / 15 by ring]; linarith [hw.2]
    · exact h1
    · exact absurd haE (hwin a h1 (by linarith [hw.1]))
  · rcases lt_trichotomy b (((A : ℝ) + 1 / 15) / 2 ^ n) with h1 | h1 | h1
    · exact absurd hbE (hwin b (by linarith [hw.2]) h1)
    · exact h1
    · exfalso
      refine hend 1 (by omega) ⟨?_, ?_⟩ <;> push_cast
      · linarith [hw.1]
      · exact h1

lemma sInf_E15 : sInf E15 = 1 / 15 := by
  refine IsLeast.csInf_eq ⟨?_, fun x hx => (E15_subset_Icc hx).1⟩
  refine ⟨⟨by norm_num, by norm_num⟩, fun n z => ?_⟩
  have := endpoint_good (n := 0) (Nat.zero_le n) (A := 0) (e := 1) (by norm_num) z
  simpa using this

lemma one_fifteenth_mem : (1 / 15 : ℝ) ∈ E15 := by
  refine ⟨⟨by norm_num, by norm_num⟩, fun n z => ?_⟩
  have := endpoint_good (n := 0) (Nat.zero_le n) (A := 0) (e := 1) (by norm_num) z
  simpa using this

lemma fourteen_fifteenths_mem : (14 / 15 : ℝ) ∈ E15 := by
  refine ⟨⟨by norm_num, by norm_num⟩, fun n z => ?_⟩
  have := endpoint_good (n := 0) (Nat.zero_le n) (A := 1) (e := -1) (by norm_num) z
  convert this using 4
  norm_num

/-- **`E15` facts** (proved): compact, hull `[1/15, 14/15]`, gaps of length `≤ 1/15`, thickness `3`. -/
theorem e15_facts :
    IsCompact E15 ∧ (1 / 15 : ℝ) ∈ E15 ∧ (14 / 15 : ℝ) ∈ E15 ∧ E15 ⊆ Set.Icc (1 / 15) (14 / 15) ∧
      (∀ a b, IsGap E15 a b → b - a ≤ 1 / 15) ∧ Thick E15 3 := by
  have hInf : sInf E15 = 1 / 15 :=
    IsLeast.csInf_eq ⟨one_fifteenth_mem, fun x hx => (E15_subset_Icc hx).1⟩
  have hSup : sSup E15 = 14 / 15 :=
    IsGreatest.csSup_eq ⟨fourteen_fifteenths_mem, fun x hx => (E15_subset_Icc hx).2⟩
  refine ⟨?_, one_fifteenth_mem, fourteen_fifteenths_mem, E15_subset_Icc, ?_, ?_, ?_⟩
  · refine isCompact_Icc.inter_right ?_
    have : {x : ℝ | ∀ n : ℕ, ∀ z : ℤ, 1 / 15 ≤ |(2 : ℝ) ^ n * x - z|} =
        ⋂ n : ℕ, ⋂ z : ℤ, {x : ℝ | 1 / 15 ≤ |(2 : ℝ) ^ n * x - z|} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun n => isClosed_iInter fun z =>
      isClosed_le continuous_const ((continuous_const.mul continuous_id).sub continuous_const).abs
  · intro a b hg
    obtain ⟨n, A, rfl, rfl⟩ := gap_eq_window hg
    have ha := E15_subset_Icc hg.2.1
    have hb := E15_subset_Icc hg.2.2.1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      simp only [pow_zero, div_one] at ha hb
      have h1 : (0 : ℝ) < A := by linarith [ha.1]
      have h2 : (0 : ℤ) < A := by exact_mod_cast h1
      have h3 : (1 : ℝ) ≤ A := by exact_mod_cast h2
      linarith [hb.2]
    · have h2 : (2 : ℝ) ≤ 2 ^ n := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
      rw [show ((A : ℝ) + 1 / 15) / 2 ^ n - ((A : ℝ) - 1 / 15) / 2 ^ n = 2 / 15 / 2 ^ n by ring]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  · intro a b a' b' hg hg' hle
    obtain ⟨n, A, rfl, rfl⟩ := gap_eq_window hg
    obtain ⟨n', A', rfl, rfl⟩ := gap_eq_window hg'
    have len : ∀ (k : ℕ) (B : ℤ), ((B : ℝ) + 1 / 15) / 2 ^ k - ((B : ℝ) - 1 / 15) / 2 ^ k =
        2 / (15 * 2 ^ k) := fun k B => by field_simp; ring
    rw [len, len]
    rcases le_total n n' with h | h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have := window_sep_left hle
      have hm : min (2 / (15 * 2 ^ n) : ℝ) (2 / (15 * 2 ^ (n + j))) ≤ 2 / (15 * 2 ^ (n + j)) :=
        min_le_right _ _
      linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have := window_sep_right hle
      have hm : min (2 / (15 * 2 ^ (n' + j)) : ℝ) (2 / (15 * 2 ^ n')) ≤ 2 / (15 * 2 ^ (n' + j)) :=
        min_le_left _ _
      linarith
  · intro a b hg
    obtain ⟨n, A, rfl, rfl⟩ := gap_eq_window hg
    have ha := E15_subset_Icc hg.2.1
    have hb := E15_subset_Icc hg.2.2.1
    rw [hInf, hSup]
    have len : ((A : ℝ) + 1 / 15) / 2 ^ n - ((A : ℝ) - 1 / 15) / 2 ^ n = 2 / (15 * 2 ^ (0 + n)) := by
      rw [zero_add]; field_simp; ring
    rw [len]
    constructor
    · have := window_sep_left (m := 0) (j := n) (C := 0) (A := A) (by simpa using ha.1)
      simpa using this
    · have := window_sep_right (m := 0) (j := n) (C := 1) (A := A) (by
        simp only [zero_add, pow_zero, div_one, Int.cast_one]; linarith [hb.2])
      norm_num at this ⊢
      linarith

/-! ### The exact base-`b` sets `Fset b c`

`Fset b c = {x ∈ [0, 1] : ‖bⁿx‖ ≥ 1/(b^c − 1) ∀ n} ⊆ E_b(c)` (`E15` is the case `b = 2`, `c = 4`).
The orbit of `1/(b^c − 1)` under `×b` is periodic, so the gaps are exactly the windows
`(A ± 1/M)/bⁿ`, `M = b^c − 1` (`Fset_gap_eq_window`), and `Mk − bʲ ≥ 1 ⇒ Mk − bʲ ≥ M − b^{c−1}`
(`bʲ ≡ b^{j mod c} mod M`) gives thickness `(b^c − b^{c−1} − 2)/2` (`fset_facts`): `3` for `(2, 4)`,
`26` for `(3, 4)`, `1` for `(2, 3)`, `8` for `(3, 3)`. -/

/-- The exact base-`b` good set at exponent `c`. -/
def Fset (b c : ℕ) : Set ℝ :=
  Set.Icc 0 1 ∩ {x | ∀ n : ℕ, ∀ z : ℤ, 1 / ((b : ℝ) ^ c - 1) ≤ |(b : ℝ) ^ n * x - z|}

lemma pow_decomp (b : ℕ) {c : ℕ} (hc : 0 < c) (j : ℕ) :
    ∃ t : ℤ, (b : ℤ) ^ j = (b : ℤ) ^ (j % c) + ((b : ℤ) ^ c - 1) * t := by
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow ((b : ℤ) ^ c) 1 (j / c)
  refine ⟨(b : ℤ) ^ (j % c) * t, ?_⟩
  rw [one_pow] at ht
  have e : ((b : ℤ) ^ c) ^ (j / c) = 1 + ((b : ℤ) ^ c - 1) * t := by linarith
  conv_lhs => rw [← Nat.div_add_mod j c]
  rw [pow_add, pow_mul, e]
  ring

lemma Fset_M_pos {b c : ℕ} (hbc : 3 ≤ b ^ c) : (0 : ℤ) < (b : ℤ) ^ c - 1 := by
  have : (3 : ℤ) ≤ (b : ℤ) ^ c := by exact_mod_cast hbc
  linarith

lemma Fset_top_lt {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) :
    (b : ℤ) ^ (c - 1) < (b : ℤ) ^ c - 1 := by
  have key : b ^ (c - 1) + 1 < b ^ c := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hc
    simp only [zero_add, Nat.add_sub_cancel] at *
    rw [pow_succ] at hbc ⊢
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at hbc ⊢; omega
    · have : 2 ≤ b ^ d := by
        calc 2 ≤ b := hb
          _ = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ d := Nat.pow_le_pow_right (by omega) hd
      nlinarith
  have : ((b ^ (c - 1) + 1 : ℕ) : ℤ) < ((b ^ c : ℕ) : ℤ) := by exact_mod_cast key
  push_cast at this
  linarith

lemma Fset_sep {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) (j : ℕ) (k : ℤ)
    (h : 1 ≤ ((b : ℤ) ^ c - 1) * k - (b : ℤ) ^ j) :
    ((b : ℤ) ^ c - 1) - (b : ℤ) ^ (c - 1) ≤ ((b : ℤ) ^ c - 1) * k - (b : ℤ) ^ j := by
  obtain ⟨t, ht⟩ := pow_decomp b hc j
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hr1 : 1 ≤ (b : ℤ) ^ (j % c) := one_le_pow₀ hb1
  have hr2 : (b : ℤ) ^ (j % c) ≤ (b : ℤ) ^ (c - 1) :=
    pow_le_pow_right₀ hb1 (by have := Nat.mod_lt j hc; omega)
  have hM := Fset_M_pos hbc
  set M := (b : ℤ) ^ c - 1
  rw [ht] at h ⊢
  have e : M * k - ((b : ℤ) ^ (j % c) + M * t) = M * (k - t) - (b : ℤ) ^ (j % c) := by ring
  rw [e] at h ⊢
  have hkt : 1 ≤ k - t := by
    by_contra hlt
    push_neg at hlt
    have : M * (k - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.le (by omega)
    linarith
  have : M * 1 ≤ M * (k - t) := mul_le_mul_of_nonneg_left hkt hM.le
  linarith

lemma Fset_not_dvd {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) (i : ℕ) (A e : ℤ)
    (he : e = 1 ∨ e = -1) : ¬ ((b : ℤ) ^ c - 1) ∣ (b : ℤ) ^ i * (((b : ℤ) ^ c - 1) * A + e) := by
  intro hd
  obtain ⟨t, ht⟩ := pow_decomp b hc i
  have hM := Fset_M_pos hbc
  have htop := Fset_top_lt hb hc hbc
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hr1 : 1 ≤ (b : ℤ) ^ (i % c) := one_le_pow₀ hb1
  have hr2 : (b : ℤ) ^ (i % c) ≤ (b : ℤ) ^ (c - 1) :=
    pow_le_pow_right₀ hb1 (by have := Nat.mod_lt i hc; omega)
  set M := (b : ℤ) ^ c - 1
  have h1 : M ∣ e * (b : ℤ) ^ i := by
    have e0 : e * (b : ℤ) ^ i = (b : ℤ) ^ i * (M * A + e) - M * ((b : ℤ) ^ i * A) := by ring
    rw [e0]; exact hd.sub (dvd_mul_right _ _)
  have h2 : M ∣ (b : ℤ) ^ i := by
    rcases he with rfl | rfl
    · simpa using h1
    · simpa using h1
  have h3 : M ∣ (b : ℤ) ^ (i % c) := by
    have e0 : (b : ℤ) ^ (i % c) = (b : ℤ) ^ i - M * t := by rw [ht]; ring
    rw [e0]; exact h2.sub (dvd_mul_right _ _)
  have := Int.le_of_dvd (by linarith) h3
  linarith

lemma Fset_le_abs {M u : ℤ} (hM : 0 < M) (hu : ¬ M ∣ u) (z : ℤ) :
    1 / (M : ℝ) ≤ |(u : ℝ) / M - z| := by
  have h1 : u - M * z ≠ 0 := fun h => hu ⟨z, by linarith⟩
  have h3 : (1 : ℝ) ≤ |(u : ℝ) - M * z| := by exact_mod_cast Int.one_le_abs h1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have : (u : ℝ) / M - z = ((u : ℝ) - M * z) / M := by field_simp
  rw [this, abs_div, abs_of_pos hMr]
  exact div_le_div_of_nonneg_right h3 hMr.le

lemma Fset_endpoint_good {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) {n k : ℕ}
    (hnk : n ≤ k) (A e : ℤ) (he : e = 1 ∨ e = -1) (z : ℤ) :
    1 / ((b : ℝ) ^ c - 1) ≤ |(b : ℝ) ^ k * (((A : ℝ) + e / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ n) - z| := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hnk
  have hM := Fset_M_pos hbc
  have := Fset_le_abs hM (Fset_not_dvd hb hc hbc i A e he) z
  have hMr : (0 : ℝ) < (b : ℝ) ^ c - 1 := by exact_mod_cast hM
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  push_cast at this
  convert this using 3
  rw [pow_add]
  field_simp

lemma Fset_subset_Icc {b c : ℕ} : Fset b c ⊆ Set.Icc (1 / ((b : ℝ) ^ c - 1))
    (1 - 1 / ((b : ℝ) ^ c - 1)) := by
  intro x hx
  have h0 := hx.2 0 0
  have h1 := hx.2 0 1
  simp only [pow_zero, one_mul, Int.cast_zero, sub_zero, Int.cast_one] at h0 h1
  have := hx.1
  constructor
  · rw [abs_of_nonneg this.1] at h0; exact h0
  · rw [abs_of_nonpos (by linarith [this.2])] at h1; linarith

/-- **Every gap of `Fset b c` is a window** `((A − 1/M)/bⁿ, (A + 1/M)/bⁿ)`. -/
lemma Fset_gap_eq_window {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) {u v : ℝ}
    (h : IsGap (Fset b c) u v) :
    ∃ n : ℕ, ∃ A : ℤ, u = ((A : ℝ) - 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ n ∧
      v = ((A : ℝ) + 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ n := by
  obtain ⟨huv, huE, hvE, hdis⟩ := h
  set M : ℝ := (b : ℝ) ^ c - 1 with hMdef
  have hnot : ∀ w ∈ Set.Ioo u v, w ∉ Fset b c := fun w hw hwE => Set.disjoint_left.1 hdis hw hwE
  have hbad : ∀ w ∈ Set.Ioo u v, ∃ n : ℕ, ∃ z : ℤ, |(b : ℝ) ^ n * w - z| < 1 / M := by
    intro w hw
    by_contra hcon
    push_neg at hcon
    exact hnot w hw ⟨⟨huE.1.1.trans hw.1.le, hw.2.le.trans hvE.1.2⟩, hcon⟩
  have hP : ∃ n : ℕ, ∃ z : ℤ, ∃ w ∈ Set.Ioo u v, |(b : ℝ) ^ n * w - z| < 1 / M := by
    obtain ⟨n, z, hz⟩ := hbad ((u + v) / 2) ⟨by linarith, by linarith⟩
    exact ⟨n, z, _, ⟨by linarith, by linarith⟩, hz⟩
  classical
  set n := Nat.find hP with hn
  obtain ⟨A, w, hw, hwA⟩ := Nat.find_spec hP
  have hpos : (0 : ℝ) < (b : ℝ) ^ n := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  have hwin : ∀ x : ℝ, ((A : ℝ) - 1 / M) / (b : ℝ) ^ n < x → x < ((A : ℝ) + 1 / M) / (b : ℝ) ^ n →
      x ∉ Fset b c := by
    intro x h1 h2 hx
    rw [div_lt_iff₀ hpos] at h1
    rw [lt_div_iff₀ hpos] at h2
    have := hx.2 n A
    exact absurd this (not_le.2 (abs_lt.2 ⟨by linarith, by linarith⟩))
  rw [abs_lt] at hwA
  have hw1 : ((A : ℝ) - 1 / M) / (b : ℝ) ^ n < w := by rw [div_lt_iff₀ hpos]; linarith
  have hw2 : w < ((A : ℝ) + 1 / M) / (b : ℝ) ^ n := by rw [lt_div_iff₀ hpos]; linarith
  have hend : ∀ e : ℤ, (e = 1 ∨ e = -1) → ((A : ℝ) + e / M) / (b : ℝ) ^ n ∉ Set.Ioo u v := by
    intro e he hin
    obtain ⟨k, z, hk⟩ := hbad _ hin
    rcases lt_or_ge k n with hkn | hkn
    · exact Nat.find_min hP hkn ⟨z, _, hin, hk⟩
    · exact absurd hk (not_lt.2 (Fset_endpoint_good hb hc hbc hkn A e he z))
  refine ⟨n, A, ?_, ?_⟩
  · rcases lt_trichotomy u (((A : ℝ) - 1 / M) / (b : ℝ) ^ n) with h1 | h1 | h1
    · exfalso
      have e1 : ((A : ℝ) + ((-1 : ℤ) : ℝ) / M) = (A : ℝ) - 1 / M := by push_cast; ring
      refine hend (-1) (Or.inr rfl) ⟨?_, ?_⟩
      · rw [e1]; exact h1
      · rw [e1]; linarith [hw.2]
    · exact h1
    · exact absurd huE (hwin u h1 (by linarith [hw.1]))
  · rcases lt_trichotomy v (((A : ℝ) + 1 / M) / (b : ℝ) ^ n) with h1 | h1 | h1
    · exact absurd hvE (hwin v (by linarith [hw.2]) h1)
    · exact h1
    · exfalso
      have e1 : ((A : ℝ) + ((1 : ℤ) : ℝ) / M) = (A : ℝ) + 1 / M := by push_cast; ring
      refine hend 1 (Or.inl rfl) ⟨?_, ?_⟩
      · rw [e1]; linarith [hw.1]
      · rw [e1]; exact h1

/-- Separation of a window of order `m` (left) from one of order `m + j` (right). -/
lemma Fset_window_sep_left {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) {m j : ℕ}
    {C A : ℤ}
    (h : ((C : ℝ) + 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ m ≤
      ((A : ℝ) - 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ (m + j)) :
    (((b : ℝ) ^ c - 1 - (b : ℝ) ^ (c - 1) - 1) / 2) * (2 / (((b : ℝ) ^ c - 1) * (b : ℝ) ^ (m + j))) ≤
      ((A : ℝ) - 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ (m + j) -
        ((C : ℝ) + 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ m := by
  have hMz := Fset_M_pos hbc
  have hM : (0 : ℝ) < (b : ℝ) ^ c - 1 := by exact_mod_cast hMz
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hP : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  have hQ : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  set M : ℝ := (b : ℝ) ^ c - 1 with hMdef
  rw [pow_add] at h ⊢
  rw [div_le_div_iff₀ hP (by positivity)] at h
  have h' : ((C : ℝ) + 1 / M) * (b : ℝ) ^ j ≤ (A : ℝ) - 1 / M := by
    rw [show ((C : ℝ) + 1 / M) * ((b : ℝ) ^ m * (b : ℝ) ^ j) =
      (((C : ℝ) + 1 / M) * (b : ℝ) ^ j) * (b : ℝ) ^ m by ring] at h
    exact le_of_mul_le_mul_right h hP
  have h'' : ((C : ℝ) * M + 1) * (b : ℝ) ^ j ≤ (A : ℝ) * M - 1 := by
    have := mul_le_mul_of_nonneg_right h' hM.le
    have e1 : ((C : ℝ) + 1 / M) * (b : ℝ) ^ j * M = ((C : ℝ) * M + 1) * (b : ℝ) ^ j := by
      field_simp
    have e2 : ((A : ℝ) - 1 / M) * M = (A : ℝ) * M - 1 := by field_simp
    linarith
  have hi : (1 : ℤ) ≤ ((b : ℤ) ^ c - 1) * (A - C * (b : ℤ) ^ j) - (b : ℤ) ^ j := by
    have : (1 : ℝ) ≤ (((b : ℤ) ^ c - 1) * (A - C * (b : ℤ) ^ j) - (b : ℤ) ^ j : ℤ) := by
      push_cast; rw [← hMdef]; nlinarith
    exact_mod_cast this
  have h7 := Fset_sep hb hc hbc j _ hi
  have h7r : (((b : ℤ) ^ c - 1) - (b : ℤ) ^ (c - 1) : ℤ) ≤
      ((((b : ℤ) ^ c - 1) * (A - C * (b : ℤ) ^ j) - (b : ℤ) ^ j : ℤ) : ℝ) := by exact_mod_cast h7
  push_cast at h7r
  rw [← hMdef] at h7r
  rw [show ((A : ℝ) - 1 / M) / ((b : ℝ) ^ m * (b : ℝ) ^ j) - ((C : ℝ) + 1 / M) / (b : ℝ) ^ m =
      (M * (A - C * (b : ℝ) ^ j) - (b : ℝ) ^ j - 1) / (M * ((b : ℝ) ^ m * (b : ℝ) ^ j)) by
      field_simp; ring]
  rw [show (M - (b : ℝ) ^ (c - 1) - 1) / 2 * (2 / (M * ((b : ℝ) ^ m * (b : ℝ) ^ j))) =
      (M - (b : ℝ) ^ (c - 1) - 1) / (M * ((b : ℝ) ^ m * (b : ℝ) ^ j)) by field_simp]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- Separation of a window of order `m + j` (left) from one of order `m` (right). -/
lemma Fset_window_sep_right {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) {m j : ℕ}
    {C A : ℤ}
    (h : ((A : ℝ) + 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ (m + j) ≤
      ((C : ℝ) - 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ m) :
    (((b : ℝ) ^ c - 1 - (b : ℝ) ^ (c - 1) - 1) / 2) * (2 / (((b : ℝ) ^ c - 1) * (b : ℝ) ^ (m + j))) ≤
      ((C : ℝ) - 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ m -
        ((A : ℝ) + 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ (m + j) := by
  have hMz := Fset_M_pos hbc
  have hM : (0 : ℝ) < (b : ℝ) ^ c - 1 := by exact_mod_cast hMz
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hP : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  have hQ : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  set M : ℝ := (b : ℝ) ^ c - 1 with hMdef
  rw [pow_add] at h ⊢
  rw [div_le_div_iff₀ (by positivity) hP] at h
  have h' : (A : ℝ) + 1 / M ≤ ((C : ℝ) - 1 / M) * (b : ℝ) ^ j := by
    rw [show ((C : ℝ) - 1 / M) * ((b : ℝ) ^ m * (b : ℝ) ^ j) =
      (((C : ℝ) - 1 / M) * (b : ℝ) ^ j) * (b : ℝ) ^ m by ring] at h
    exact le_of_mul_le_mul_right h hP
  have h'' : (A : ℝ) * M + 1 ≤ ((C : ℝ) * M - 1) * (b : ℝ) ^ j := by
    have := mul_le_mul_of_nonneg_right h' hM.le
    have e1 : ((C : ℝ) - 1 / M) * (b : ℝ) ^ j * M = ((C : ℝ) * M - 1) * (b : ℝ) ^ j := by
      field_simp
    have e2 : ((A : ℝ) + 1 / M) * M = (A : ℝ) * M + 1 := by field_simp
    linarith
  have hi : (1 : ℤ) ≤ ((b : ℤ) ^ c - 1) * (C * (b : ℤ) ^ j - A) - (b : ℤ) ^ j := by
    have : (1 : ℝ) ≤ (((b : ℤ) ^ c - 1) * (C * (b : ℤ) ^ j - A) - (b : ℤ) ^ j : ℤ) := by
      push_cast; rw [← hMdef]; nlinarith
    exact_mod_cast this
  have h7 := Fset_sep hb hc hbc j _ hi
  have h7r : (((b : ℤ) ^ c - 1) - (b : ℤ) ^ (c - 1) : ℤ) ≤
      ((((b : ℤ) ^ c - 1) * (C * (b : ℤ) ^ j - A) - (b : ℤ) ^ j : ℤ) : ℝ) := by exact_mod_cast h7
  push_cast at h7r
  rw [← hMdef] at h7r
  rw [show ((C : ℝ) - 1 / M) / (b : ℝ) ^ m - ((A : ℝ) + 1 / M) / ((b : ℝ) ^ m * (b : ℝ) ^ j) =
      (M * (C * (b : ℝ) ^ j - A) - (b : ℝ) ^ j - 1) / (M * ((b : ℝ) ^ m * (b : ℝ) ^ j)) by
      field_simp; ring]
  rw [show (M - (b : ℝ) ^ (c - 1) - 1) / 2 * (2 / (M * ((b : ℝ) ^ m * (b : ℝ) ^ j))) =
      (M - (b : ℝ) ^ (c - 1) - 1) / (M * ((b : ℝ) ^ m * (b : ℝ) ^ j)) by field_simp]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  linarith

lemma Fset_left_mem {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) :
    1 / ((b : ℝ) ^ c - 1) ∈ Fset b c := by
  have hM : (3 : ℝ) ≤ (b : ℝ) ^ c := by exact_mod_cast hbc
  refine ⟨⟨by apply div_nonneg <;> linarith, by rw [div_le_one (by linarith)]; linarith⟩,
    fun n z => ?_⟩
  have := Fset_endpoint_good hb hc hbc (n := 0) (Nat.zero_le n) 0 1 (Or.inl rfl) z
  simpa using this

lemma Fset_right_mem {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) :
    1 - 1 / ((b : ℝ) ^ c - 1) ∈ Fset b c := by
  have hM : (3 : ℝ) ≤ (b : ℝ) ^ c := by exact_mod_cast hbc
  have h1 : 1 / ((b : ℝ) ^ c - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h0 : 0 ≤ 1 / ((b : ℝ) ^ c - 1) := by apply div_nonneg <;> linarith
  refine ⟨⟨by linarith, by linarith⟩, fun n z => ?_⟩
  have := Fset_endpoint_good hb hc hbc (n := 0) (Nat.zero_le n) 1 (-1) (Or.inr rfl) z
  convert this using 4
  push_cast; ring

/-- **`Fset` facts** (proved): compact, hull `[1/M, 1 − 1/M]`, gaps of length `≤ 2/(Mb)`, thickness
`(b^c − b^{c−1} − 2)/2`, inside `E_b(c)` (`M = b^c − 1`). -/
theorem fset_facts {b c : ℕ} (hb : 2 ≤ b) (hc : 0 < c) (hbc : 3 ≤ b ^ c) :
    IsCompact (Fset b c) ∧ 1 / ((b : ℝ) ^ c - 1) ∈ Fset b c ∧
      1 - 1 / ((b : ℝ) ^ c - 1) ∈ Fset b c ∧
      Fset b c ⊆ Set.Icc (1 / ((b : ℝ) ^ c - 1)) (1 - 1 / ((b : ℝ) ^ c - 1)) ∧
      (∀ u v, IsGap (Fset b c) u v → v - u ≤ 2 / (((b : ℝ) ^ c - 1) * b)) ∧
      Thick (Fset b c) (((b : ℝ) ^ c - 1 - (b : ℝ) ^ (c - 1) - 1) / 2) ∧
      Fset b c ⊆ goodSet c b := by
  have hMz := Fset_M_pos hbc
  have hM : (0 : ℝ) < (b : ℝ) ^ c - 1 := by exact_mod_cast hMz
  have hbr : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hInf : sInf (Fset b c) = 1 / ((b : ℝ) ^ c - 1) :=
    IsLeast.csInf_eq ⟨Fset_left_mem hb hc hbc, fun x hx => (Fset_subset_Icc hx).1⟩
  have hSup : sSup (Fset b c) = 1 - 1 / ((b : ℝ) ^ c - 1) :=
    IsGreatest.csSup_eq ⟨Fset_right_mem hb hc hbc, fun x hx => (Fset_subset_Icc hx).2⟩
  have len : ∀ (k : ℕ) (B : ℤ), ((B : ℝ) + 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ k -
      ((B : ℝ) - 1 / ((b : ℝ) ^ c - 1)) / (b : ℝ) ^ k = 2 / (((b : ℝ) ^ c - 1) * (b : ℝ) ^ k) :=
    fun k B => by field_simp; ring
  refine ⟨?_, Fset_left_mem hb hc hbc, Fset_right_mem hb hc hbc, Fset_subset_Icc, ?_, ⟨?_, ?_⟩, ?_⟩
  · refine isCompact_Icc.inter_right ?_
    have : {x : ℝ | ∀ n : ℕ, ∀ z : ℤ, 1 / ((b : ℝ) ^ c - 1) ≤ |(b : ℝ) ^ n * x - z|} =
        ⋂ n : ℕ, ⋂ z : ℤ, {x : ℝ | 1 / ((b : ℝ) ^ c - 1) ≤ |(b : ℝ) ^ n * x - z|} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun n => isClosed_iInter fun z =>
      isClosed_le continuous_const ((continuous_const.mul continuous_id).sub continuous_const).abs
  · intro u v hg
    obtain ⟨n, A, rfl, rfl⟩ := Fset_gap_eq_window hb hc hbc hg
    have ha := Fset_subset_Icc hg.2.1
    have hb' := Fset_subset_Icc hg.2.2.1
    rw [len]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      simp only [pow_zero, div_one] at ha hb'
      have hpos : 0 < 1 / ((b : ℝ) ^ c - 1) := by positivity
      have h1 : (0 : ℝ) < A := by linarith [ha.1]
      have h2 : (0 : ℤ) < A := by exact_mod_cast h1
      have h3 : (1 : ℝ) ≤ A := by exact_mod_cast h2
      linarith [hb'.2]
    · have h2 : (b : ℝ) ≤ (b : ℝ) ^ n := by
        calc (b : ℝ) = (b : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (b : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left h2 hM.le
  · intro u v u' v' hg hg' hle
    obtain ⟨n, A, rfl, rfl⟩ := Fset_gap_eq_window hb hc hbc hg
    obtain ⟨n', A', rfl, rfl⟩ := Fset_gap_eq_window hb hc hbc hg'
    rw [len, len]
    have htau : 0 ≤ ((b : ℝ) ^ c - 1 - (b : ℝ) ^ (c - 1) - 1) / 2 := by
      have := Fset_top_lt hb hc hbc
      have h' : ((b : ℝ) ^ (c - 1)) < (b : ℝ) ^ c - 1 := by exact_mod_cast this
      have h'' : ((b : ℝ) ^ (c - 1)) + 1 ≤ (b : ℝ) ^ c - 1 := by
        have : (((b : ℤ) ^ (c - 1) + 1 : ℤ) : ℝ) ≤ (((b : ℤ) ^ c - 1 : ℤ) : ℝ) := by
          exact_mod_cast this
        push_cast at this; linarith
      linarith
    rcases le_total n n' with h | h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have := Fset_window_sep_left hb hc hbc hle
      have hm := mul_le_mul_of_nonneg_left (min_le_right
        (2 / (((b : ℝ) ^ c - 1) * (b : ℝ) ^ n)) (2 / (((b : ℝ) ^ c - 1) * (b : ℝ) ^ (n + j)))) htau
      linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have := Fset_window_sep_right hb hc hbc hle
      have hm := mul_le_mul_of_nonneg_left (min_le_left
        (2 / (((b : ℝ) ^ c - 1) * (b : ℝ) ^ (n' + j))) (2 / (((b : ℝ) ^ c - 1) * (b : ℝ) ^ n'))) htau
      linarith
  · intro u v hg
    obtain ⟨n, A, rfl, rfl⟩ := Fset_gap_eq_window hb hc hbc hg
    have ha := Fset_subset_Icc hg.2.1
    have hb' := Fset_subset_Icc hg.2.2.1
    rw [hInf, hSup, len]
    rw [show n = 0 + n from (zero_add n).symm]
    constructor
    · have := Fset_window_sep_left hb hc hbc (m := 0) (j := n) (C := 0) (A := A)
        (by simpa using ha.1)
      simpa using this
    · have := Fset_window_sep_right hb hc hbc (m := 0) (j := n) (C := 1) (A := A) (by
        simp only [zero_add, pow_zero, div_one, Int.cast_one]; linarith [hb'.2])
      have e : ((1 : ℤ) : ℝ) - 1 / ((b : ℝ) ^ c - 1) = 1 - 1 / ((b : ℝ) ^ c - 1) := by simp
      simp only [pow_zero, div_one] at this
      rw [e] at this
      exact this
  · intro x hx n
    have h := hx.2 n (round ((b : ℝ) ^ n * x))
    unfold dnear
    refine le_trans ?_ h
    rw [one_div]
    exact inv_anti₀ hM (by linarith)

/-! ### Cantor schemes are thick

A node `J = (p, q)` is split at `r J < s J`, keeping `[p, r J]` and `[s J, q]`, with both kept
pieces at least `τ` times the removed gap and at most `ρ < 1` times `J`.  The limit set `B` has
`Thick B τ`, its gaps are exactly the removed `(r J, s J)` (`Scheme.gap_eq`), and if every endpoint
lies in a closed set `G` then `B ⊆ G`.  This turns the crux into a local, coinductive splitting
statement (`SplitCore`). -/

namespace Scheme

variable (r s : ℝ × ℝ → ℝ)

/-- The two children of a node. -/
def child (J : ℝ × ℝ) : Bool → ℝ × ℝ
  | false => (J.1, r J)
  | true => (s J, J.2)

/-- Nodes of depth `k` below the root `J₀`. -/
def level (J₀ : ℝ × ℝ) : ℕ → Set (ℝ × ℝ)
  | 0 => {J₀}
  | k + 1 => (fun p : (ℝ × ℝ) × Bool => child r s p.1 p.2) '' (level J₀ k ×ˢ Set.univ)

/-- The admissible-split conditions at a node. -/
def NodeOk (τ ρ : ℝ) (G : Set ℝ) (J : ℝ × ℝ) : Prop :=
  J.1 < r J ∧ r J < s J ∧ s J < J.2 ∧ τ * (s J - r J) ≤ r J - J.1 ∧
    τ * (s J - r J) ≤ J.2 - s J ∧ r J - J.1 ≤ ρ * (J.2 - J.1) ∧ J.2 - s J ≤ ρ * (J.2 - J.1) ∧
    J.1 ∈ G ∧ J.2 ∈ G

/-- The limit set. -/
def limit (J₀ : ℝ × ℝ) : Set ℝ := ⋂ k, ⋃ J ∈ level r s J₀ k, Set.Icc J.1 J.2

/-- A set of nodes closed under children, all admissible. -/
def Closed (τ ρ : ℝ) (G : Set ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  ∀ J ∈ S, NodeOk r s τ ρ G J ∧ child r s J false ∈ S ∧ child r s J true ∈ S

variable {r s} {τ ρ : ℝ} {G : Set ℝ} {S : Set (ℝ × ℝ)} {J₀ J : ℝ × ℝ}

lemma mem_level_succ {J₀ J : ℝ × ℝ} {k : ℕ} :
    J ∈ level r s J₀ (k + 1) ↔ ∃ P ∈ level r s J₀ k, ∃ d, J = child r s P d := by
  show J ∈ (fun p : (ℝ × ℝ) × Bool => child r s p.1 p.2) '' (level r s J₀ k ×ˢ Set.univ) ↔ _
  constructor
  · rintro ⟨⟨P, d⟩, ⟨hP, -⟩, rfl⟩; exact ⟨P, hP, d, rfl⟩
  · rintro ⟨P, hP, d, rfl⟩; exact ⟨(P, d), ⟨hP, trivial⟩, rfl⟩

lemma level_sub (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) : ∀ k, ∀ J ∈ level r s J₀ k, J ∈ S
  | 0, J, hJ => by rw [show J = J₀ from hJ]; exact h0
  | k + 1, J, hJ => by
    obtain ⟨P, hP, d, rfl⟩ := mem_level_succ.1 hJ
    have := hS P (level_sub hS h0 k P hP)
    cases d
    · exact this.2.1
    · exact this.2.2

lemma level_finite : ∀ k, (level r s J₀ k).Finite
  | 0 => Set.finite_singleton _
  | k + 1 => ((level_finite k).prod Set.finite_univ).image _

lemma child_sub (hJ : NodeOk r s τ ρ G J) (d : Bool) :
    Set.Icc (child r s J d).1 (child r s J d).2 ⊆ Set.Icc J.1 J.2 := by
  obtain ⟨h1, h2, h3, -⟩ := hJ
  cases d
  · exact Set.Icc_subset_Icc le_rfl (by simp only [child]; linarith)
  · exact Set.Icc_subset_Icc (by simp only [child]; linarith) le_rfl

lemma child_len (hJ : NodeOk r s τ ρ G J) (d : Bool) :
    (child r s J d).1 < (child r s J d).2 ∧
      (child r s J d).2 - (child r s J d).1 ≤ ρ * (J.2 - J.1) := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -⟩ := hJ
  cases d
  · exact ⟨h1, h6⟩
  · exact ⟨h3, h7⟩

lemma level_len (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) (hρ : 0 ≤ ρ) :
    ∀ k, ∀ J ∈ level r s J₀ k, J.2 - J.1 ≤ ρ ^ k * (J₀.2 - J₀.1)
  | 0, J, hJ => by rw [show J = J₀ from hJ]; simp
  | k + 1, J, hJ => by
    obtain ⟨P, hP, d, rfl⟩ := mem_level_succ.1 hJ
    have hPS := level_sub hS h0 k P hP
    have := (child_len (hS P hPS).1 d).2
    have ih := level_len hS h0 hρ k P hP
    calc _ ≤ ρ * (P.2 - P.1) := this
      _ ≤ ρ * (ρ ^ k * (J₀.2 - J₀.1)) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ ^ (k + 1) * (J₀.2 - J₀.1) := by ring

lemma level_anc (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) :
    ∀ k, ∀ J ∈ level r s J₀ k, ∀ m ≤ k, ∃ A ∈ level r s J₀ m,
      Set.Icc J.1 J.2 ⊆ Set.Icc A.1 A.2
  | 0, J, hJ, m, hm => ⟨J, by rw [Nat.le_zero.1 hm]; exact hJ, le_rfl⟩
  | k + 1, J, hJ, m, hm => by
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · obtain ⟨P, hP, d, rfl⟩ := mem_level_succ.1 hJ
      obtain ⟨A, hA, hsub⟩ := level_anc hS h0 k P hP m (by omega)
      exact ⟨A, hA, (child_sub (hS P (level_sub hS h0 k P hP)).1 d).trans hsub⟩
    · exact ⟨J, by rw [show m = k + 1 by omega]; exact hJ, le_rfl⟩

lemma level_disj (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) :
    ∀ k, ∀ J ∈ level r s J₀ k, ∀ J' ∈ level r s J₀ k, J ≠ J' →
      Disjoint (Set.Icc J.1 J.2) (Set.Icc J'.1 J'.2)
  | 0, J, hJ, J', hJ', hne => absurd ((show J = J₀ from hJ).trans (show J' = J₀ from hJ').symm) hne
  | k + 1, J, hJ, J', hJ', hne => by
    obtain ⟨P, hP, d, rfl⟩ := mem_level_succ.1 hJ
    obtain ⟨P', hP', d', rfl⟩ := mem_level_succ.1 hJ'
    have hok := (hS P (level_sub hS h0 k P hP)).1
    by_cases hPP : P = P'
    · subst hPP
      have hdd : d ≠ d' := fun h => hne (by rw [h])
      obtain ⟨h1, h2, h3, -⟩ := hok
      rw [Set.disjoint_iff]
      rintro x ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩
      cases d <;> cases d' <;> simp only [child, ne_eq, not_true_eq_false] at hdd hx1 hx2 hx3 hx4 <;>
        linarith
    · exact ((level_disj hS h0 k P hP P' hP' hPP).mono (child_sub hok d)
        (child_sub (hS P' (level_sub hS h0 k P' hP')).1 d'))

/-- The left (resp. right) endpoint of a node survives in a node of every deeper level. -/
lemma left_persist (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) {k : ℕ} {J : ℝ × ℝ}
    (hJ : J ∈ level r s J₀ k) : ∀ i, ∃ J' ∈ level r s J₀ (k + i), J'.1 = J.1 ∧ J.1 ≤ J'.2
  | 0 => ⟨J, hJ, rfl, (hS J (level_sub hS h0 k J hJ)).1.1.le.trans
      ((hS J (level_sub hS h0 k J hJ)).1.2.1.le.trans (hS J (level_sub hS h0 k J hJ)).1.2.2.1.le)⟩
  | i + 1 => by
    obtain ⟨J', hJ', h1, -⟩ := left_persist hS h0 hJ i
    have hok := (hS J' (level_sub hS h0 _ J' hJ')).1
    refine ⟨child r s J' false, mem_level_succ.2 ⟨J', hJ', false, rfl⟩, h1, ?_⟩
    simp only [child]; rw [← h1]; exact hok.1.le

lemma right_persist (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) {k : ℕ} {J : ℝ × ℝ}
    (hJ : J ∈ level r s J₀ k) : ∀ i, ∃ J' ∈ level r s J₀ (k + i), J'.2 = J.2 ∧ J'.1 ≤ J.2
  | 0 => ⟨J, hJ, rfl, (hS J (level_sub hS h0 k J hJ)).1.1.le.trans
      ((hS J (level_sub hS h0 k J hJ)).1.2.1.le.trans (hS J (level_sub hS h0 k J hJ)).1.2.2.1.le)⟩
  | i + 1 => by
    obtain ⟨J', hJ', h1, -⟩ := right_persist hS h0 hJ i
    have hok := (hS J' (level_sub hS h0 _ J' hJ')).1
    refine ⟨child r s J' true, mem_level_succ.2 ⟨J', hJ', true, rfl⟩, h1, ?_⟩
    simp only [child]; rw [← h1]; exact hok.2.2.1.le

lemma endpoints_mem (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) {k : ℕ} {J : ℝ × ℝ}
    (hJ : J ∈ level r s J₀ k) : J.1 ∈ limit r s J₀ ∧ J.2 ∈ limit r s J₀ := by
  have hok := (hS J (level_sub hS h0 k J hJ)).1
  have hJ12 : J.1 ≤ J.2 := hok.1.le.trans (hok.2.1.le.trans hok.2.2.1.le)
  constructor <;> refine Set.mem_iInter.2 fun m => ?_ <;> rw [Set.mem_iUnion₂]
  · rcases le_total m k with hm | hm
    · obtain ⟨A, hA, hsub⟩ := level_anc hS h0 k J hJ m hm
      exact ⟨A, hA, hsub ⟨le_rfl, hJ12⟩⟩
    · obtain ⟨J', hJ', h1, h2⟩ := left_persist hS h0 hJ (m - k)
      rw [show k + (m - k) = m by omega] at hJ'
      exact ⟨J', hJ', ⟨h1.le, h2⟩⟩
  · rcases le_total m k with hm | hm
    · obtain ⟨A, hA, hsub⟩ := level_anc hS h0 k J hJ m hm
      exact ⟨A, hA, hsub ⟨hJ12, le_rfl⟩⟩
    · obtain ⟨J', hJ', h1, h2⟩ := right_persist hS h0 hJ (m - k)
      rw [show k + (m - k) = m by omega] at hJ'
      exact ⟨J', hJ', ⟨h2, h1.ge⟩⟩

lemma limit_sub : limit r s J₀ ⊆ Set.Icc J₀.1 J₀.2 := by
  intro x hx
  have := Set.mem_iInter.1 hx 0
  rw [Set.mem_iUnion₂] at this
  obtain ⟨J, hJ, hx⟩ := this
  rw [show J = J₀ from hJ] at hx
  exact hx

lemma limit_closed : IsClosed (limit r s J₀) :=
  isClosed_iInter fun k => (level_finite k).isClosed_biUnion fun _ _ => isClosed_Icc

lemma mem_level_of_mem {x : ℝ} (hx : x ∈ limit r s J₀) (k : ℕ) :
    ∃ J ∈ level r s J₀ k, x ∈ Set.Icc J.1 J.2 := by
  have := Set.mem_iInter.1 hx k
  rw [Set.mem_iUnion₂] at this
  obtain ⟨J, hJ, hxJ⟩ := this
  exact ⟨J, hJ, hxJ⟩

/-- The limit set lies in the closed set `G` containing all endpoints. -/
lemma limit_sub_G (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hG : IsClosed G) : limit r s J₀ ⊆ G := by
  intro x hx
  choose J hJ hxJ using mem_level_of_mem hx
  apply hG.mem_of_tendsto (f := fun k => (J k).1) (b := Filter.atTop)
  · rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (g := fun k : ℕ => ρ ^ k * (J₀.2 - J₀.1))
    · intro k
      rw [Real.dist_eq, abs_of_nonpos (by linarith [(hxJ k).1])]
      have := level_len hS h0 hρ0 k (J k) (hJ k)
      linarith [(hxJ k).2]
    · rw [show (0 : ℝ) = 0 * (J₀.2 - J₀.1) by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const _
  · exact Filter.Eventually.of_forall fun k => (hS (J k) (level_sub hS h0 k (J k) (hJ k))).1.2.2.2.2.2.2.2.1

/-- **Every gap of the limit set is a removed gap.** -/
lemma gap_eq (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {a b : ℝ}
    (h : IsGap (limit r s J₀) a b) :
    ∃ k, ∃ J ∈ level r s J₀ k, a = r J ∧ b = s J := by
  obtain ⟨hab, haB, hbB, hdis⟩ := h
  let P : ℕ → Prop := fun k => ∃ J ∈ level r s J₀ k, a ∈ Set.Icc J.1 J.2 ∧ b ∈ Set.Icc J.1 J.2
  have hP0 : P 0 := ⟨J₀, rfl, limit_sub haB, limit_sub hbB⟩
  have hex : ∃ k, ¬ P k := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (b - a) / (J₀.2 - J₀.1 + 1) by
      have := limit_sub haB; have := limit_sub hbB
      apply div_pos (by linarith); linarith [this.1, this.2]) hρ1
    refine ⟨k, ?_⟩
    rintro ⟨J, hJ, ha, hb⟩
    have hlen := level_len hS h0 hρ0 k J hJ
    have hJ0 : 0 ≤ J₀.2 - J₀.1 := by have := limit_sub haB; linarith [this.1, this.2]
    have : ρ ^ k * (J₀.2 - J₀.1) < b - a := by
      rw [lt_div_iff₀ (by linarith)] at hk
      nlinarith [pow_nonneg hρ0 k]
    linarith [ha.1, hb.2]
  classical
  have hspec := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := fun h => hspec (by rw [h]; exact hP0)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hPk : P k := by
    by_contra hc
    exact Nat.find_min hex (show k < Nat.find hex by omega) hc
  have hnP : ¬ P (k + 1) := by rw [← hk]; exact hspec
  obtain ⟨J, hJ, haJ, hbJ⟩ := hPk
  have hok := (hS J (level_sub hS h0 k J hJ)).1
  -- the level-(k+1) nodes containing `a`, `b` are children of `J`
  have hchild : ∀ x ∈ limit r s J₀, x ∈ Set.Icc J.1 J.2 →
      ∃ d, x ∈ Set.Icc (child r s J d).1 (child r s J d).2 := by
    intro x hx hxJ
    obtain ⟨J', hJ', hxJ'⟩ := mem_level_of_mem hx (k + 1)
    obtain ⟨Pp, hPp, d, rfl⟩ := mem_level_succ.1 hJ'
    have hsub := child_sub (hS Pp (level_sub hS h0 k Pp hPp)).1 d
    by_cases hPJ : Pp = J
    · exact ⟨d, hPJ ▸ hxJ'⟩
    · exact absurd (Set.disjoint_left.1 (level_disj hS h0 k Pp hPp J hJ hPJ) (hsub hxJ') hxJ)
        id
  obtain ⟨d1, ha1⟩ := hchild a haB haJ
  obtain ⟨d2, hb2⟩ := hchild b hbB hbJ
  have hrB : r J ∈ limit r s J₀ :=
    (endpoints_mem hS h0 (mem_level_succ.2 ⟨J, hJ, false, rfl⟩)).2
  have hsB : s J ∈ limit r s J₀ :=
    (endpoints_mem hS h0 (mem_level_succ.2 ⟨J, hJ, true, rfl⟩)).1
  obtain ⟨h1, h2, h3, -⟩ := hok
  have hd : d1 = false ∧ d2 = true := by
    cases d1 <;> cases d2
    · exact absurd ⟨child r s J false, mem_level_succ.2 ⟨J, hJ, false, rfl⟩, ha1, hb2⟩ hnP
    · exact ⟨rfl, rfl⟩
    · simp only [child] at ha1 hb2; linarith [ha1.1, hb2.2]
    · exact absurd ⟨child r s J true, mem_level_succ.2 ⟨J, hJ, true, rfl⟩, ha1, hb2⟩ hnP
  obtain ⟨rfl, rfl⟩ := hd
  simp only [child] at ha1 hb2
  refine ⟨k, J, hJ, ?_, ?_⟩
  · by_contra hne
    have hlt : a < r J := lt_of_le_of_ne ha1.2 hne
    exact Set.disjoint_left.1 hdis ⟨hlt, by linarith [hb2.1]⟩ hrB
  · by_contra hne
    have hlt : s J < b := lt_of_le_of_ne hb2.1 (Ne.symm hne)
    exact Set.disjoint_left.1 hdis ⟨by linarith [ha1.2], hlt⟩ hsB

/-- Two removed gaps: one misses the other's node. -/
lemma gap_node_disj (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) {k₁ k₂ : ℕ} {J₁ J₂ : ℝ × ℝ}
    (hJ₁ : J₁ ∈ level r s J₀ k₁) (hJ₂ : J₂ ∈ level r s J₀ k₂) (hk : k₁ ≤ k₂) :
    J₁ = J₂ ∨ Disjoint (Set.Ioo (r J₁) (s J₁)) (Set.Icc J₂.1 J₂.2) := by
  obtain ⟨A, hA, hsubA⟩ := level_anc hS h0 k₂ J₂ hJ₂ k₁ hk
  have hJ2ne : (Set.Icc J₂.1 J₂.2).Nonempty := by
    have hok := (hS J₂ (level_sub hS h0 k₂ J₂ hJ₂)).1
    exact Set.nonempty_Icc.2 (hok.1.le.trans (hok.2.1.le.trans hok.2.2.1.le))
  have hok1 := (hS J₁ (level_sub hS h0 k₁ J₁ hJ₁)).1
  have hgap_sub : Set.Ioo (r J₁) (s J₁) ⊆ Set.Icc J₁.1 J₁.2 := fun x hx =>
    ⟨by linarith [hx.1, hok1.1], by linarith [hx.2, hok1.2.2.1]⟩
  by_cases hAJ : A = J₁
  · subst hAJ
    rcases Nat.eq_or_lt_of_le hk with heq | hlt
    · subst heq
      by_contra hc
      push_neg at hc
      have hne : J₂ ≠ A := fun h => hc.1 h.symm
      obtain ⟨x, hx⟩ := hJ2ne
      exact Set.disjoint_left.1 (level_disj hS h0 k₁ J₂ hJ₂ A hA hne) hx (hsubA hx)
    · right
      obtain ⟨A', hA', hsubA'⟩ := level_anc hS h0 k₂ J₂ hJ₂ (k₁ + 1) hlt
      obtain ⟨Pp, hPp, d, rfl⟩ := mem_level_succ.1 hA'
      have hsubP := child_sub (hS Pp (level_sub hS h0 k₁ Pp hPp)).1 d
      have hPA : Pp = A := by
        by_contra hne
        obtain ⟨x, hx⟩ := hJ2ne
        exact Set.disjoint_left.1 (level_disj hS h0 k₁ Pp hPp A hA hne) (hsubP (hsubA' hx))
          (hsubA hx)
      subst hPA
      refine Set.disjoint_of_subset_right hsubA' ?_
      rw [Set.disjoint_iff]
      rintro x ⟨⟨hx1, hx2⟩, hx3, hx4⟩
      cases d <;> simp only [child] at hx3 hx4 <;> linarith
  · right
    exact (level_disj hS h0 k₁ A hA J₁ hJ₁ hAJ).symm.mono hgap_sub hsubA

/-- Separation from a gap that misses a node. -/
lemma sep_of_disj {r₁ s₁ r₂ s₂ P Q : ℝ} (h1 : r₁ < s₁) (hP : P ≤ r₂) (hQ : s₂ ≤ Q)
    (h2 : r₂ < s₂) (hdis : Disjoint (Set.Ioo r₁ s₁) (Set.Icc P Q)) :
    (s₁ ≤ r₂ → s₁ ≤ P) ∧ (s₂ ≤ r₁ → Q ≤ r₁) := by
  constructor
  · intro hle
    by_contra hlt
    push_neg at hlt
    have hm : max r₁ P < s₁ := max_lt h1 hlt
    exact Set.disjoint_left.1 hdis (show (max r₁ P + s₁) / 2 ∈ Set.Ioo r₁ s₁ from
      ⟨by linarith [le_max_left r₁ P], by linarith⟩)
      ⟨by linarith [le_max_right r₁ P], by linarith⟩
  · intro hle
    by_contra hlt
    push_neg at hlt
    have hm : r₁ < min s₁ Q := lt_min h1 hlt
    exact Set.disjoint_left.1 hdis (show (r₁ + min s₁ Q) / 2 ∈ Set.Ioo r₁ s₁ from
      ⟨by linarith, by linarith [min_le_left s₁ Q]⟩)
      ⟨by linarith, by linarith [min_le_right s₁ Q]⟩

/-- **Cantor schemes are thick.** -/
theorem limit_thick (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hτ : 0 ≤ τ) : Thick (limit r s J₀) τ := by
  have hinf : sInf (limit r s J₀) = J₀.1 :=
    IsLeast.csInf_eq ⟨(endpoints_mem hS h0 (k := 0) rfl).1, fun x hx => (limit_sub hx).1⟩
  have hsup : sSup (limit r s J₀) = J₀.2 :=
    IsGreatest.csSup_eq ⟨(endpoints_mem hS h0 (k := 0) rfl).2, fun x hx => (limit_sub hx).2⟩
  have ok : ∀ {k J}, J ∈ level r s J₀ k → NodeOk r s τ ρ G J := fun {k J} hJ =>
    (hS J (level_sub hS h0 k J hJ)).1
  refine ⟨?_, ?_⟩
  · intro a b a' b' hg hg' hle
    obtain ⟨k₁, J₁, hJ₁, rfl, rfl⟩ := gap_eq hS h0 hρ0 hρ1 hg
    obtain ⟨k₂, J₂, hJ₂, rfl, rfl⟩ := gap_eq hS h0 hρ0 hρ1 hg'
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := ok hJ₁
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := ok hJ₂
    have hm1 := min_le_left (s J₁ - r J₁) (s J₂ - r J₂)
    have hm2 := min_le_right (s J₁ - r J₁) (s J₂ - r J₂)
    rcases le_total k₁ k₂ with hk | hk
    · rcases gap_node_disj hS h0 hJ₁ hJ₂ hk with heq | hdis
      · subst heq; linarith
      · have := (sep_of_disj a2 b1.le b3.le b2 hdis).1 hle
        nlinarith
    · rcases gap_node_disj hS h0 hJ₂ hJ₁ hk with heq | hdis
      · subst heq; linarith
      · have := (sep_of_disj b2 a1.le a3.le a2 hdis).2 hle
        nlinarith
  · intro a b hg
    obtain ⟨k, J, hJ, rfl, rfl⟩ := gap_eq hS h0 hρ0 hρ1 hg
    obtain ⟨A, hA, hsub⟩ := level_anc hS h0 k J hJ 0 (Nat.zero_le _)
    rw [show A = J₀ from hA] at hsub
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := ok hJ
    have h1 := (hsub ⟨le_rfl, by linarith⟩ : J.1 ∈ Set.Icc J₀.1 J₀.2)
    have h2 := (hsub ⟨by linarith, le_rfl⟩ : J.2 ∈ Set.Icc J₀.1 J₀.2)
    rw [hinf, hsup]
    exact ⟨by linarith [h1.1], by linarith [h2.2]⟩

/-- Gaps of the limit set are removed gaps, so a uniform bound on removed gaps bounds them. -/
lemma gap_le (hS : Closed r s τ ρ G S) (h0 : J₀ ∈ S) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {g : ℝ}
    (hg : ∀ J ∈ S, s J - r J ≤ g) {a b : ℝ} (h : IsGap (limit r s J₀) a b) : b - a ≤ g := by
  obtain ⟨k, J, hJ, rfl, rfl⟩ := gap_eq hS h0 hρ0 hρ1 h
  exact hg J (level_sub hS h0 k J hJ)

end Scheme

/-- **Crux node: a thick core for the bases `b ≥ 3`.**  A compact `B` inside every `E_b(c)`,
`b ≥ 3`, with thickness `τ`, short gaps, and points near both ends of `[0, 1]`.

Believed for `c = 4`, `τ = 2/5`: 70% (probe in the module doc: merging near-touching windows of
bases `3 … 40` to thickness `0.4` costs `26` merges and leaves the hull `[1/80, 79/80]`; the open
point is a worst-case bound on merge cascades at all scales and over all bases, where the windows
of distinct bases can cluster near rationals with large denominators). -/
def ThickCore (c : ℕ) (τ : ℝ) : Prop :=
  ∃ B : Set ℝ, IsCompact B ∧ Thick B τ ∧ (∀ b : ℕ, 3 ≤ b → B ⊆ goodSet c b) ∧
    (∀ a b, IsGap B a b → b - a ≤ 1 / 10) ∧
    (∃ x ∈ B, x ≤ 1 / 4) ∧ (∃ y ∈ B, 3 / 4 ≤ y) ∧ B ⊆ Set.Icc 0 1

/-- The closed good set for the bases `b ≥ 3` at exponent `c` (inside every `E_b(c)`, `b ≥ 3`). -/
def goodCore (c : ℕ) : Set ℝ :=
  Set.Icc 0 1 ∩ {x | ∀ b : ℕ, 3 ≤ b → ∀ n : ℕ, ∀ z : ℤ, ((b : ℝ) ^ c)⁻¹ ≤ |(b : ℝ) ^ n * x - z|}

lemma goodCore_closed (c : ℕ) : IsClosed (goodCore c) := by
  refine isClosed_Icc.inter ?_
  have : {x : ℝ | ∀ b : ℕ, 3 ≤ b → ∀ n : ℕ, ∀ z : ℤ, ((b : ℝ) ^ c)⁻¹ ≤ |(b : ℝ) ^ n * x - z|} =
      ⋂ b : ℕ, ⋂ (_ : 3 ≤ b), ⋂ n : ℕ, ⋂ z : ℤ,
        {x : ℝ | ((b : ℝ) ^ c)⁻¹ ≤ |(b : ℝ) ^ n * x - z|} := by
    ext; simp
  rw [this]
  exact isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_iInter fun n =>
    isClosed_iInter fun z =>
      isClosed_le continuous_const ((continuous_const.mul continuous_id).sub continuous_const).abs

lemma goodCore_sub (c : ℕ) {b : ℕ} (hb : 3 ≤ b) : goodCore c ⊆ goodSet c b :=
  fun _ hx n => hx.2 b hb n _

/-! ### Forced merging: a thick core has no adaptive freedom

A `τ`-thick compact `B` cannot put two intervals it misses, both inside its hull and closer than `τ`
times the shorter one, into different gaps (`merge_forced`).  For a core `B ⊆ ⋂_{b ≥ 3} E_b(c)` the
windows of the bases `b ≥ 3` are such intervals (`window_disjoint`), so the gaps of every thick core
contain the `τ`-merge closure of those windows (`windows_merge_forced`; iterate on merged hulls).
Hence `ThickCore c τ` holds exactly when that canonical closure stays local: it must not reach the
ends of the hull nor make a gap longer than `1/10`.  Adaptive constructions (`SplitCore`, the
flipped pairing `A = Fset 3 4`, discarding clusters) can only enlarge gaps, so they add nothing
beyond the canonical closure.  What a proof of `ThickCore` must supply is a bound on merge cascades
of windows of distinct bases at every depth (Maze row "adaptive split cores for the Newhouse thick
core"). -/

/-- A nonempty open interval inside the hull of a compact set and missing it lies in one gap. -/
lemma exists_gap_of_Ioo {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) {u v : ℝ} (huv : u < v)
    (hdisj : Disjoint (Set.Ioo u v) K) (hu : sInf K ≤ u) (hv : v ≤ sSup K) :
    ∃ a b, IsGap K a b ∧ a ≤ u ∧ v ≤ b := by
  have hxK : (u + v) / 2 ∉ K := fun h =>
    Set.disjoint_left.1 hdisj ⟨by linarith, by linarith⟩ h
  obtain ⟨c, d, hg, hc, hd, -, -⟩ := exists_gap_of_not_mem hK (hK.sInf_mem hne)
    (hK.sSup_mem hne) (by linarith) (by linarith) hxK
  refine ⟨c, d, hg, ?_, ?_⟩
  · by_contra h
    push_neg at h
    exact Set.disjoint_left.1 hdisj ⟨h, by linarith⟩ hg.2.1
  · by_contra h
    push_neg at h
    exact Set.disjoint_left.1 hdisj ⟨by linarith, h⟩ hg.2.2.1

/-- **Forced merging** (proved).  If a `τ`-thick compact `B` misses the open intervals `(u₁, u₂)` and
`(v₁, v₂)`, both inside its hull, with `u₂ ≤ v₁ < u₂ + τ · min(u₂ − u₁, v₂ − v₁)`, then a single gap of
`B` contains `(u₁, v₂)`. -/
theorem merge_forced {B : Set ℝ} {τ : ℝ} (hB : IsCompact B) (hne : B.Nonempty) (hτ : Thick B τ)
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ < u₂) (hv : v₁ < v₂) (huv : u₂ ≤ v₁)
    (hU : Disjoint (Set.Ioo u₁ u₂) B) (hV : Disjoint (Set.Ioo v₁ v₂) B)
    (h1 : sInf B ≤ u₁) (h2 : v₂ ≤ sSup B) (hclose : v₁ - u₂ < τ * min (u₂ - u₁) (v₂ - v₁)) :
    ∃ a b, IsGap B a b ∧ a ≤ u₁ ∧ v₂ ≤ b := by
  obtain ⟨a, b, hg, ha, hb⟩ := exists_gap_of_Ioo hB hne hu hU h1 (by linarith)
  obtain ⟨a', b', hg', ha', hb'⟩ := exists_gap_of_Ioo hB hne hv hV (by linarith) h2
  rcases le_or_gt b a' with hba | hab
  · exfalso
    have hmin : 0 < min (u₂ - u₁) (v₂ - v₁) := lt_min (by linarith) (by linarith)
    have hτ0 : 0 < τ := by
      by_contra h
      push_neg at h
      nlinarith
    have hsep := hτ.1 a b a' b' hg hg' hba
    have hmono : min (u₂ - u₁) (v₂ - v₁) ≤ min (b - a) (b' - a') :=
      min_le_min (by linarith) (by linarith)
    nlinarith
  · have haa : a = a' := by
      rcases lt_trichotomy a a' with h | h | h
      · exact absurd hg'.2.1 (Set.disjoint_left.1 hg.2.2.2 ⟨h, hab⟩)
      · exact h
      · exact absurd hg.2.1 (Set.disjoint_left.1 hg'.2.2.2 ⟨h, by linarith⟩)
    subst haa
    have hbb := hg.right_unique hg'
    subst hbb
    exact ⟨a, b, hg, ha, hb'⟩

/-- The open base-`b` window of order `n` around `z/bⁿ` at exponent `c`. -/
def window (c b n : ℕ) (z : ℤ) : Set ℝ :=
  Set.Ioo ((z - ((b : ℝ) ^ c)⁻¹) / (b : ℝ) ^ n) ((z + ((b : ℝ) ^ c)⁻¹) / (b : ℝ) ^ n)

/-- Base-`b` windows miss `E_b(c)`. -/
lemma window_disjoint {c b : ℕ} (hb : 2 ≤ b) (n : ℕ) (z : ℤ) : Disjoint (window c b n z) (goodSet c b) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ hx
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos (by exact_mod_cast (by omega : 0 < b)) n
  rw [div_lt_iff₀ hbn] at h1
  rw [lt_div_iff₀ hbn] at h2
  have habs : |(b : ℝ) ^ n * x - z| < ((b : ℝ) ^ c)⁻¹ := by
    rw [abs_lt]; constructor <;> linarith
  exact absurd (lt_of_le_of_lt (dnear_le_abs_sub _ z) habs) (not_lt.2 (hx n))

/-- **No adaptive freedom** (proved).  In a `τ`-thick compact `B ⊆ ⋂_{b ≥ 3} E_b(c)`, two windows
(or pieces of windows) of bases `≥ 3` inside the hull of `B`, closer than `τ` times the shorter, lie
in one gap of `B`. -/
theorem windows_merge_forced {c : ℕ} {τ : ℝ} {B : Set ℝ} (hB : IsCompact B) (hne : B.Nonempty)
    (hτ : Thick B τ) (hgood : ∀ b : ℕ, 3 ≤ b → B ⊆ goodSet c b) {u₁ u₂ v₁ v₂ : ℝ}
    (hu : u₁ < u₂) (hv : v₁ < v₂) (huv : u₂ ≤ v₁)
    (hU : ∃ b n z, 3 ≤ b ∧ Set.Ioo u₁ u₂ ⊆ window c b n z)
    (hV : ∃ b n z, 3 ≤ b ∧ Set.Ioo v₁ v₂ ⊆ window c b n z)
    (h1 : sInf B ≤ u₁) (h2 : v₂ ≤ sSup B) (hclose : v₁ - u₂ < τ * min (u₂ - u₁) (v₂ - v₁)) :
    ∃ a b, IsGap B a b ∧ a ≤ u₁ ∧ v₂ ≤ b := by
  have key : ∀ {p q : ℝ}, (∃ b n z, 3 ≤ b ∧ Set.Ioo p q ⊆ window c b n z) →
      Disjoint (Set.Ioo p q) B := by
    rintro p q ⟨b, n, z, hb, hsub⟩
    exact ((window_disjoint (by omega) n z).mono_left hsub).mono_right (hgood b hb)
  exact merge_forced hB hne hτ hu hv huv (key hU) (key hV) h1 h2 hclose

/-- **Split core** (a local, coinductive form of `ThickCore`).  A family `S` of intervals with
endpoints in `goodCore c`, closed under an admissible split (both kept pieces at least `τ` times the
removed gap, at most `ρ < 1` times the node, removed gap at most `1/10`), containing a root that
reaches `1/4` and `3/4`. -/
def SplitCore (c : ℕ) (τ : ℝ) : Prop :=
  ∃ (r s : ℝ × ℝ → ℝ) (ρ : ℝ) (S : Set (ℝ × ℝ)) (J₀ : ℝ × ℝ), 0 ≤ ρ ∧ ρ < 1 ∧
    Scheme.Closed r s τ ρ (goodCore c) S ∧ J₀ ∈ S ∧ J₀.1 ≤ 1 / 4 ∧ 3 / 4 ≤ J₀.2 ∧
    ∀ J ∈ S, s J - r J ≤ 1 / 10

/-- **Reduction** (proved): a split core gives a thick core. -/
theorem thickCore_of_splitCore {c : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (h : SplitCore c τ) :
    ThickCore c τ := by
  obtain ⟨r, s, ρ, S, J₀, hρ0, hρ1, hS, h0, hl, hr, hg⟩ := h
  have hG := Scheme.limit_sub_G hS h0 hρ0 hρ1 (goodCore_closed c)
  have hend := Scheme.endpoints_mem hS h0 (k := 0) rfl
  refine ⟨Scheme.limit r s J₀, ?_, Scheme.limit_thick hS h0 hρ0 hρ1 hτ,
    fun b hb => hG.trans (goodCore_sub c hb), fun a b hab => Scheme.gap_le hS h0 hρ0 hρ1 hg hab,
    ⟨J₀.1, hend.1, hl⟩, ⟨J₀.2, hend.2, hr⟩, fun x hx => (hG hx).1⟩
  exact (isCompact_Icc.of_isClosed_subset Scheme.limit_closed Scheme.limit_sub)

/-- **The route** (proved, axiom-clean).  A thick core at exponent `4` with `τ > 1/3` gives
`c⋆ ≤ 4`: `gap_lemma` applied to `E15` (thickness `3`, `e15_facts`) and the core. -/
theorem cStar_le_four_of_newhouse {τ : ℝ} (hτ : 1 / 3 < τ) (h : ThickCore 4 τ) : cStar ≤ 4 := by
  obtain ⟨B, hBc, hBt, hBgood, hBgap, ⟨x, hxB, hx⟩, ⟨y, hyB, hy⟩, hB01⟩ := h
  obtain ⟨hAc, h1A, h2A, hAsub, hAgap, hAt⟩ := e15_facts
  have hτ0 : 0 < τ := lt_trans (by norm_num) hτ
  have hBbdd : BddBelow B := hBc.bddBelow
  have hBbddA : BddAbove B := hBc.bddAbove
  have hAbdd : BddBelow E15 := hAc.bddBelow
  have hAbddA : BddAbove E15 := hAc.bddAbove
  have hInfA : sInf E15 ≤ 1 / 15 := csInf_le hAbdd h1A
  have hSupA : 14 / 15 ≤ sSup E15 := le_csSup hAbddA h2A
  have hInfB : sInf B ≤ 1 / 4 := (csInf_le hBbdd hxB).trans hx
  have hSupB : 3 / 4 ≤ sSup B := hy.trans (le_csSup hBbddA hyB)
  obtain ⟨ξ, hξA, hξB⟩ := gap_lemma hAc hBc ⟨_, h1A⟩ ⟨x, hxB⟩ hAt hBt (by norm_num) hτ0
    (by nlinarith) (by linarith) (by linarith)
    (by
      rintro ⟨a, b, hab, hsub⟩
      have h1 := hsub hxB
      have h2 := hsub hyB
      have := hAgap a b hab
      simp only [Set.mem_Ioo] at h1 h2
      linarith)
    (by
      rintro ⟨a, b, hab, hsub⟩
      have h1 := hsub h1A
      have h2 := hsub h2A
      have := hBgap a b hab
      simp only [Set.mem_Ioo] at h1 h2
      linarith)
  -- ξ is good in every base
  have hgood : ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, ((b : ℝ) ^ 4)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
    intro b hb n
    rcases (by omega : b = 2 ∨ 3 ≤ b) with rfl | hb3
    · exact E15_subset_goodSet hξA n
    · exact hBgood b hb3 hξB n
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => csInf_le bddBelow_admissible ?_
  refine ⟨ξ, fun b hb n => lt_of_lt_of_le ?_ (hgood b hb n)⟩
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have h1 : (b : ℝ) ^ ((4 : ℕ) : ℝ) < (b : ℝ) ^ c :=
    Real.rpow_lt_rpow_of_exponent_lt hb1 (by exact_mod_cast hc)
  rw [Real.rpow_natCast] at h1
  rw [Real.rpow_neg (by positivity)]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 h1

/-- **The route at any integer exponent `c ≥ 3`** (proved).  `Fset 2 c` has thickness
`2^{c−2} − 1` (`fset_facts`), so a thick core with `τ (2^{c−2} − 1) > 1` gives `c⋆ ≤ c`.  At `c = 3`
this needs `ThickCore 3 τ` with `τ > 1` (`cStarLeThree_of_newhouse`). -/
theorem cStar_le_of_newhouse {c : ℕ} (hc : 3 ≤ c) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : 1 < τ * (((2 : ℝ) ^ c - 1 - (2 : ℝ) ^ (c - 1) - 1) / 2)) (h : ThickCore c τ) :
    cStar ≤ c := by
  obtain ⟨B, hBc, hBt, hBgood, hBgap, ⟨x, hxB, hx⟩, ⟨y, hyB, hy⟩, hB01⟩ := h
  have h8 : 8 ≤ 2 ^ c := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
  obtain ⟨hAc, h1A, h2A, hAsub, hAgap, hAt, hAgood⟩ :=
    fset_facts (b := 2) (c := c) le_rfl (by omega) (by omega)
  push_cast at h1A h2A hAsub hAgap hAt hAgood
  have h8r : (8 : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast h8
  have hm : 1 / ((2 : ℝ) ^ c - 1) ≤ 1 / 7 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hm0 : 0 < 1 / ((2 : ℝ) ^ c - 1) := by apply div_pos one_pos; linarith
  have hτA : 0 < ((2 : ℝ) ^ c - 1 - (2 : ℝ) ^ (c - 1) - 1) / 2 := by
    by_contra hneg; push_neg at hneg; nlinarith
  have hBbdd : BddBelow B := hBc.bddBelow
  have hBbddA : BddAbove B := hBc.bddAbove
  have hInfA : sInf (Fset 2 c) ≤ 1 / ((2 : ℝ) ^ c - 1) := csInf_le hAc.bddBelow h1A
  have hSupA : 1 - 1 / ((2 : ℝ) ^ c - 1) ≤ sSup (Fset 2 c) := le_csSup hAc.bddAbove h2A
  have hInfB : sInf B ≤ 1 / 4 := (csInf_le hBbdd hxB).trans hx
  have hSupB : 3 / 4 ≤ sSup B := hy.trans (le_csSup hBbddA hyB)
  obtain ⟨ξ, hξA, hξB⟩ := gap_lemma hAc hBc ⟨_, h1A⟩ ⟨x, hxB⟩ hAt hBt hτA hτ0
    (by linarith [mul_comm τ (((2 : ℝ) ^ c - 1 - (2 : ℝ) ^ (c - 1) - 1) / 2)])
    (by linarith) (by linarith)
    (by
      rintro ⟨a, b, hab, hsub⟩
      have h1 := hsub hxB
      have h2 := hsub hyB
      have := hAgap a b hab
      have h7 : 2 / (((2 : ℝ) ^ c - 1) * 2) ≤ 1 / 7 := by
        rw [show 2 / (((2 : ℝ) ^ c - 1) * 2) = 1 / ((2 : ℝ) ^ c - 1) by field_simp]; exact hm
      simp only [Set.mem_Ioo] at h1 h2
      linarith)
    (by
      rintro ⟨a, b, hab, hsub⟩
      have h1 := hsub h1A
      have h2 := hsub h2A
      have := hBgap a b hab
      simp only [Set.mem_Ioo] at h1 h2
      linarith)
  have hgood : ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, ((b : ℝ) ^ c)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
    intro b hb n
    rcases (by omega : b = 2 ∨ 3 ≤ b) with rfl | hb3
    · have := hAgood hξA n
      push_cast at this
      exact this
    · exact hBgood b hb3 hξB n
  refine le_of_forall_gt_imp_ge_of_dense fun c' hc' => csInf_le bddBelow_admissible ?_
  refine ⟨ξ, fun b hb n => lt_of_lt_of_le ?_ (hgood b hb n)⟩
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have h1 : (b : ℝ) ^ ((c : ℕ) : ℝ) < (b : ℝ) ^ c' :=
    Real.rpow_lt_rpow_of_exponent_lt hb1 (by exact_mod_cast hc')
  rw [Real.rpow_natCast] at h1
  rw [Real.rpow_neg (by positivity)]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 h1

/-- `c⋆ ≤ 3` from a thick core at exponent `3` with thickness `> 1` (`Fset 2 3` has thickness `1`). -/
theorem cStarLeThree_of_newhouse {τ : ℝ} (hτ : 1 < τ) (h : ThickCore 3 τ) : CStarLeThree := by
  have := cStar_le_of_newhouse (c := 3) le_rfl (by linarith) (by norm_num; linarith) h
  exact_mod_cast this

/-- **Crux statement (frozen 2026-10-07).**  Believed 70%: a thick core at `c = 4` with `τ = 2/5`.

Review 2026-10-07 (c⋆ lap 7): by `windows_merge_forced` this is equivalent to the canonical
`2/5`-merge closure of the windows of the bases `b ≥ 3` staying local (no gap longer than `1/10`, none
reaching the hull ends).  The confidence is about truth (merge cascades should stay local: clusters
are rare at every scale and must climb across scales to grow); no mechanism for a proof is known,
since it needs control of clusters of windows of distinct bases at every depth.  Maze row "adaptive
split cores for the Newhouse thick core". -/
theorem thickCore_four : ThickCore 4 (2 / 5) := by
  sorry

end Newhouse

end NormalNumbers.UniformBadThreshold
