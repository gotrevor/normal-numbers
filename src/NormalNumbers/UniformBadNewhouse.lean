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

open NormalNumbers.UniformBad (dnear)

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

/-- **Crux statement (frozen 2026-10-07).**  Believed 70%: a thick core at `c = 4` with `τ = 2/5`. -/
theorem thickCore_four : ThickCore 4 (2 / 5) := by
  sorry

end Newhouse

end NormalNumbers.UniformBadThreshold
