/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OffsetRigidity
import NormalNumbers.G4ResidualConfinement

/-!
# After the extraction, F: **rigidity of the tensor deformation T(K′)**

`DESIGN-2026-09-15-deformation.md` tests one deformation of the carry/tensor construction:
vary the multipliers `d` and offsets `t` jointly and freely, keeping coordinatewise
cancellation of the first `K′` layers only (`CoordCancelUpTo`).  `K′ = K` is the implemented
mechanism; `K′ = 0` is total release.

This module proves the *combinatorial* half of the verdict:

* **(R1)** `diff_rel` — cancellation at layer `i+1` is `Δ_i t = (i+1)·Δ_i d`.
* **(R2)** `mixed_diff_zero` — hence `Δ_i Δ_{i′} d = 0` for `i ≠ i′ < K′`.
* **additivity** `additive_of_mixed_diff` — a function with vanishing mixed differences on a
  coordinate set `S` is `f α₀ + Σ_{i∈S} (f(update α₀ i (α i)) − f α₀)` on the fibre of the
  other coordinates; `eq_of_update_invariant_on` is the walking lemma behind it.
* **(R3)** `additive_form` — so `d` and `t` are determined on each fibre `β = α|_{[K′,K)}` by
  `ψ(β) = d α₀`, `χ(β) = t α₀`, and the one-variable functions
  `φ_i(x;β) = d(update α₀ i x) − d α₀`, with `t` carrying the weights `(i+1)`.
  L2 (`offset_rigidity`) is the instance `K′ = K`, `d` fixed.
* **(C)** `card_family_le` — a family of such pairs with values in `[−M, M]` has at most
  `(4M+1)^{|fibres|·(K′(s+1)+2)}` members (`|fibres| = (s+1)^{K−K′}`).
* **(U)** `union_card_le` — L1 summed over a family: the union of the members' read sets
  below `L` has at most `|𝓕|·(L·m·H·d_max/(2 d_min^H) + H·m)` elements.

The *analytic* half — that the rough-error budget forces `K′ ≥ 3K/8` — is the design's (E),
read off draft (6.4)–(6.5) with base-4 weights; it is documented, not formalized, and no axiom
stands in for it.  With `K′ ≥ 2` the exponent in (C) is already `≤ 3H/(s+1)`
(`family_exponent_le`), which is what makes (U) vanish at the schedule
(`Sched.deformation_coeff_le`).
-/

open Finset Function

namespace NormalNumbers.G4.Rigidity

/-! ### Walking and additivity on the product grid -/

/-- If `g` is invariant under updates at every coordinate in `S′`, it agrees on any two atoms
that agree off `S′`. -/
theorem eq_of_update_invariant_on {K : ℕ} {X R : Type*} [DecidableEq (Fin K)]
    (g : (Fin K → X) → R) (S' : Finset (Fin K))
    (hg : ∀ i ∈ S', ∀ γ c, g (update γ i c) = g γ)
    (γ γ' : Fin K → X) (h : ∀ i ∉ S', γ i = γ' i) : g γ = g γ' := by
  induction S' using Finset.induction_on generalizing γ with
  | empty =>
    have : γ = γ' := funext fun i => h i (Finset.notMem_empty i)
    rw [this]
  | insert a S' ha ih =>
    have h1 : g γ = g (update γ a (γ' a)) := (hg a (Finset.mem_insert_self a S') γ (γ' a)).symm
    rw [h1]
    refine ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)) _ fun i hi => ?_
    by_cases hia : i = a
    · rw [hia, update_self]
    · rw [update_of_ne hia]
      exact h i (fun hmem => hi ((Finset.mem_insert.1 hmem).resolve_left hia))

/-- **Additivity from vanishing mixed differences.**  If all mixed second differences of `f`
along pairs of distinct coordinates in `S` vanish, then on the fibre of the coordinates outside
`S` (through `α₀`) `f` is `f α₀` plus a sum of one-coordinate increments. -/
theorem additive_of_mixed_diff {K : ℕ} {X R : Type*} [AddCommGroup R] [DecidableEq (Fin K)]
    (f : (Fin K → X) → R) (S : Finset (Fin K))
    (hf : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → ∀ α c c',
      f (update (update α i c) i' c') - f (update α i c) - f (update α i' c') + f α = 0)
    (α₀ α : Fin K → X) (hout : ∀ i ∉ S, α i = α₀ i) :
    f α = f α₀ + ∑ i ∈ S, (f (update α₀ i (α i)) - f α₀) := by
  induction S using Finset.induction_on generalizing α with
  | empty =>
    have : α = α₀ := funext fun i => hout i (Finset.notMem_empty i)
    rw [this]; simp
  | insert a S ha ih =>
    -- the atom with coordinate `a` reset
    set α' := update α a (α₀ a) with hα'
    have hout' : ∀ i ∉ S, α' i = α₀ i := by
      intro i hi
      by_cases hia : i = a
      · rw [hia, hα', update_self]
      · rw [hα', update_of_ne hia]
        exact hout i (fun hmem => hi ((Finset.mem_insert.1 hmem).resolve_left hia))
    have hf' : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → ∀ α c c',
        f (update (update α i c) i' c') - f (update α i c) - f (update α i' c') + f α = 0 :=
      fun i hi i' hi' => hf i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi')
    have ih' := ih hf' α' hout'
    -- `α = update α' a (α a)`
    have hα : α = update α' a (α a) := by
      rw [hα', update_idem, update_eq_self]
    -- the `a`-increment is invariant under updates in `S`
    have hinc : f (update α' a (α a)) - f α' = f (update α₀ a (α a)) - f α₀ := by
      refine eq_of_update_invariant_on (fun γ => f (update γ a (α a)) - f γ) S ?_ α' α₀ hout'
      intro i hi γ c
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have := hf a (Finset.mem_insert_self a S) i (Finset.mem_insert_of_mem hi) hia.symm γ (α a) c
      show f (update (update γ i c) a (α a)) - f (update γ i c) = f (update γ a (α a)) - f γ
      rw [update_comm hia.symm] at this
      rw [sub_eq_sub_iff_sub_eq_sub, ← sub_eq_zero]
      rw [← this]
      abel
    have hsum : ∑ i ∈ S, (f (update α₀ i (α' i)) - f α₀) = ∑ i ∈ S, (f (update α₀ i (α i)) - f α₀) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [hα', update_of_ne hia]
    rw [Finset.sum_insert ha]
    calc f α = f (update α' a (α a)) := by rw [← hα]
      _ = (f (update α' a (α a)) - f α') + f α' := by abel
      _ = (f (update α₀ a (α a)) - f α₀) + (f α₀ + ∑ i ∈ S, (f (update α₀ i (α i)) - f α₀)) := by
          rw [hinc, ih', hsum]
      _ = _ := by abel

/-! ### The deformation T(K′): cancellation of the first `K′` layers -/

/-- Coordinatewise cancellation of layers `1..K′`: for every coordinate `i < K′`, the
layer-`(i+1)` shift `(i+1)·d_α − t_α` ignores coordinate `i`. -/
def CoordCancelUpTo {K s : ℕ} (K' : ℕ) (d t : (Fin K → Fin (s + 1)) → ℤ) : Prop :=
  ∀ (i : Fin K), (i : ℕ) < K' → ∀ (α : Fin K → Fin (s + 1)) (c : Fin (s + 1)),
    ((i : ℕ) + 1 : ℤ) * d (update α i c) - t (update α i c) = ((i : ℕ) + 1 : ℤ) * d α - t α

/-- `K′ = K` is the implemented mechanism (`CoordCancel`). -/
lemma coordCancel_iff {K s : ℕ} (d t : (Fin K → Fin (s + 1)) → ℤ) :
    CoordCancel d t ↔ CoordCancelUpTo K d t := by
  constructor
  · intro h i _ α c; exact h i α c
  · intro h i α c; exact h i i.isLt α c

/-- **(R1)** `Δ_i t = (i+1)·Δ_i d` for `i < K′`. -/
lemma diff_rel {K s K' : ℕ} {d t : (Fin K → Fin (s + 1)) → ℤ} (h : CoordCancelUpTo K' d t)
    (i : Fin K) (hi : (i : ℕ) < K') (α : Fin K → Fin (s + 1)) (c : Fin (s + 1)) :
    t (update α i c) - t α = ((i : ℕ) + 1 : ℤ) * (d (update α i c) - d α) := by
  have := h i hi α c
  linarith

/-- **(R2)** mixed differences of `d` vanish on the cancelled coordinates. -/
theorem mixed_diff_zero {K s K' : ℕ} {d t : (Fin K → Fin (s + 1)) → ℤ}
    (h : CoordCancelUpTo K' d t) (i i' : Fin K) (hi : (i : ℕ) < K') (hi' : (i' : ℕ) < K')
    (hne : i ≠ i') (α : Fin K → Fin (s + 1)) (c c' : Fin (s + 1)) :
    d (update (update α i c) i' c') - d (update α i c) - d (update α i' c') + d α = 0 := by
  have h1 := diff_rel h i hi α c
  have h2 := diff_rel h i' hi' (update α i c) c'
  have h3 := diff_rel h i' hi' α c'
  have h4 := diff_rel h i hi (update α i' c') c
  rw [update_comm hne.symm] at h4
  have hne' : ((i : ℕ) : ℤ) ≠ ((i' : ℕ) : ℤ) := by
    intro heq; exact hne (Fin.ext (by exact_mod_cast heq))
  have key : (((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ)) *
      (d (update (update α i c) i' c') - d (update α i c) - d (update α i' c') + d α) = 0 := by
    linear_combination h3 + h4 - h1 - h2
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd (sub_eq_zero.1 h0).symm hne'
  · exact h0

/-- Mixed differences of `t` vanish too (they are `(i+1)` times those of `d`). -/
theorem mixed_diff_zero_t {K s K' : ℕ} {d t : (Fin K → Fin (s + 1)) → ℤ}
    (h : CoordCancelUpTo K' d t) (i i' : Fin K) (hi : (i : ℕ) < K') (hi' : (i' : ℕ) < K')
    (hne : i ≠ i') (α : Fin K → Fin (s + 1)) (c c' : Fin (s + 1)) :
    t (update (update α i c) i' c') - t (update α i c) - t (update α i' c') + t α = 0 := by
  have h2 := diff_rel h i' hi' (update α i c) c'
  have h3 := diff_rel h i' hi' α c'
  have hm := mixed_diff_zero h i i' hi hi' hne α c c'
  linear_combination h2 - h3 + (((i' : ℕ) : ℤ) + 1) * hm

/-- The cancelled coordinates. -/
def lowSet (K K' : ℕ) : Finset (Fin K) := Finset.univ.filter (fun i : Fin K => (i : ℕ) < K')

/-- The fibre representative: zero out the cancelled coordinates. -/
def zeroLow {K s : ℕ} (K' : ℕ) (α : Fin K → Fin (s + 1)) : Fin K → Fin (s + 1) :=
  fun i => if (i : ℕ) < K' then 0 else α i

/-- **(R3) the additive form.**  On the deformation T(K′), `d` and `t` are determined on each
fibre `zeroLow K′ α` by the fibre values `d (zeroLow K′ α)`, `t (zeroLow K′ α)` and the
one-coordinate increments `φ_i(x) = d (update (zeroLow K′ α) i x) − d (zeroLow K′ α)`, with
`t` carrying the layer weights `(i+1)`. -/
theorem additive_form {K s K' : ℕ} {d t : (Fin K → Fin (s + 1)) → ℤ}
    (h : CoordCancelUpTo K' d t) (α : Fin K → Fin (s + 1)) :
    d α = d (zeroLow K' α) + ∑ i ∈ lowSet K K',
        (d (update (zeroLow K' α) i (α i)) - d (zeroLow K' α)) ∧
    t α = t (zeroLow K' α) + ∑ i ∈ lowSet K K',
        ((i : ℕ) + 1 : ℤ) * (d (update (zeroLow K' α) i (α i)) - d (zeroLow K' α)) := by
  have hout : ∀ i ∉ lowSet K K', α i = zeroLow K' α i := by
    intro i hi
    have : ¬ ((i : ℕ) < K') := fun hlt => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩)
    simp [zeroLow, this]
  have hlow : ∀ i ∈ lowSet K K', (i : ℕ) < K' := fun i hi => (Finset.mem_filter.1 hi).2
  constructor
  · exact additive_of_mixed_diff d (lowSet K K')
      (fun i hi i' hi' hne α c c' => mixed_diff_zero h i i' (hlow i hi) (hlow i' hi') hne α c c')
      (zeroLow K' α) α hout
  · have ht := additive_of_mixed_diff t (lowSet K K')
      (fun i hi i' hi' hne α c c' => mixed_diff_zero_t h i i' (hlow i hi) (hlow i' hi') hne α c c')
      (zeroLow K' α) α hout
    rw [ht]
    congr 1
    exact Finset.sum_congr rfl fun i hi => diff_rel h i (hlow i hi) _ _

/-- L2 recovered: at `K′ = K` with `d` fixed, `t′ − t` is constant. -/
theorem offset_rigidity' {K s : ℕ} (d t t' : (Fin K → Fin (s + 1)) → ℤ)
    (ht : CoordCancelUpTo K d t) (ht' : CoordCancelUpTo K d t') :
    ∃ Δ : ℤ, ∀ α, t' α = t α + Δ :=
  offset_rigidity d t t' ((coordCancel_iff d t).2 ht) ((coordCancel_iff d t').2 ht')

/-! ### (C) counting the family -/

/-- The fibres of `zeroLow`: atoms vanishing on the cancelled coordinates. -/
def fibres (K s K' : ℕ) : Finset (Fin K → Fin (s + 1)) :=
  Finset.univ.filter (fun α => ∀ i : Fin K, (i : ℕ) < K' → α i = 0)

lemma card_fibres (K s K' : ℕ) (hK : K' ≤ K) :
    (fibres K s K').card = (s + 1) ^ (K - K') := by
  sorry

/-- The parameters of a member: fibre values of `d`, `t`, and the increments. -/
def params {K s : ℕ} (K' : ℕ) (d t : (Fin K → Fin (s + 1)) → ℤ) :
    (Fin K → Fin (s + 1)) → ℤ × ℤ × (Fin K → Fin (s + 1) → ℤ) :=
  fun β => (d β, t β, fun i x => if (i : ℕ) < K' then d (update β i x) - d β else 0)

/-- Two members with the same parameters on the fibres coincide. -/
theorem params_injective {K s K' : ℕ} {d t d' t' : (Fin K → Fin (s + 1)) → ℤ}
    (h : CoordCancelUpTo K' d t) (h' : CoordCancelUpTo K' d' t')
    (hp : ∀ β ∈ fibres K s K', params K' d t β = params K' d' t' β) :
    d = d' ∧ t = t' := by
  sorry

/-- **(C)** A family of members of T(K′) with values in `[−M, M]` has at most
`(4M+1)^{(s+1)^{K−K′} · (K′(s+1) + 2)}` members. -/
theorem card_family_le {K s K' M : ℕ} (hK : K' ≤ K)
    (𝓕 : Finset (((Fin K → Fin (s + 1)) → ℤ) × ((Fin K → Fin (s + 1)) → ℤ)))
    (hcancel : ∀ p ∈ 𝓕, CoordCancelUpTo K' p.1 p.2)
    (hM : ∀ p ∈ 𝓕, ∀ α, |p.1 α| ≤ M ∧ |p.2 α| ≤ M) :
    𝓕.card ≤ (4 * M + 1) ^ ((s + 1) ^ (K - K') * (K' * (s + 1) + 2)) := by
  sorry

/-- The exponent in (C) is at most `3(s+1)^{K−1}` once `K′ ≥ 2` (and `s ≥ 1`). -/
lemma family_exponent_le {K s K' : ℕ} (hK : K' ≤ K) (h2 : 2 ≤ K') (hs : 1 ≤ s) :
    (s + 1) ^ (K - K') * (K' * (s + 1) + 2) ≤ 3 * (s + 1) ^ (K - 1) := by
  sorry

end NormalNumbers.G4.Rigidity

/-! ### (U) the union over a family is still confined -/

namespace NormalNumbers.G4Confine

/-- **(U)** L1 summed over a finite family of samplers on the same atom type: if every member
`ν` has pairwise-coprime multipliers in `[d_min, d_max]`, its own sample `P ν` satisfying the
exact identities, and `U` is covered by the union of the members' read sets, then
`#U ∩ [0,L) ≤ |𝓕|·(L · m · |ι| · d_max /(2 d_min^{|ι|}) + |ι|·m)`. -/
theorem union_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [DecidableEq κ]
    (𝓕 : Finset κ) (d : κ → ι → ℕ) (t : κ → ι → ℕ) (P : κ → Finset ℕ)
    {dmin dmax m L : ℕ} (hdmin : 0 < dmin)
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin ≤ d ν α ∧ d ν α ≤ dmax)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ n ∈ P ν, ∀ α, n % d ν α = t ν α)
    (U : ℕ → Prop) [DecidablePred U]
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ n ∈ P ν, ∃ α, ∃ h < m,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      𝓕.card * ((L : ℝ) * m * Fintype.card ι * dmax / (2 * (dmin : ℝ) ^ Fintype.card ι)
        + Fintype.card ι * m) := by
  sorry

end NormalNumbers.G4Confine
