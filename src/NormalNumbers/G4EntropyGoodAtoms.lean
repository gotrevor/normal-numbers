/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropySubsample

/-!
# Entropy expedition — most single coordinates are individually good

`G4EntropySubsample` shows what an *arbitrary* sub-collection of coordinates costs
(`√(1/ρ)`), and `chunks_insufficient` uses that to refute the chunking route.  The missing
dual is this module: the deficit does not merely control the **average** over all coordinates,
it forces **all but a `ρ`-fraction of the individual coordinates** to be good on their own.

The mechanism is Markov applied to the per-coordinate entropy deficits, which are nonnegative
(each coordinate carries at most `m` bits) and sum to at most the total deficit `δ·|A|` by
subadditivity (`H₂_le_sum_H₂_map`).  So

    `#{α : coordDeficit L α > δ/ρ} ≤ ρ·|A|`,

and each surviving coordinate's own window law has deficit `≤ δ/ρ`, hence — by the capture
inequality `abs_posAvg_sub_le` applied to the one-coordinate family — word frequencies within
`2√(log 2 · ℓ · (δ/ρ) / (m−ℓ+1))` of `2^{−ℓ}`, **for that coordinate alone**.

This is not in tension with `no_pointwise_bound_from_deficit`: that result rules out a bound at
a *fixed position* of a window; here every position of the window is still averaged over, only
the coordinate is pinned.

Nothing in this module mentions `G₄`; the scale-`i` instance for an arbitrary `x` with an
entropy deficit is at the end.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

namespace FinLaw

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The entropy deficit of the window law at the single coordinate `α`. -/
noncomputable def coordDeficit {m : ℕ} (L : FinLaw (A → Fin (2 ^ m))) (α : A) : ℝ :=
  (m : ℝ) - (L.map (fun z => z α)).H₂

lemma logb_two_pow (m : ℕ) : Real.logb 2 ((2 ^ m : ℕ) : ℝ) = (m : ℝ) := by
  rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m by push_cast; ring, Real.logb, Real.log_pow]
  have hne : Real.log 2 ≠ 0 := by
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
    linarith
  field_simp

/-- A single coordinate carries at most `m` bits. -/
lemma coordDeficit_nonneg {m : ℕ} (L : FinLaw (A → Fin (2 ^ m))) (α : A) :
    0 ≤ coordDeficit L α := by
  have hcard : Fintype.card (Fin (2 ^ m)) = 2 ^ m := by simp
  have hpos : 0 < Fintype.card (Fin (2 ^ m)) := by rw [hcard]; exact Nat.two_pow_pos m
  have h := (L.map (fun z : A → Fin (2 ^ m) => z α)).H₂_le_logb_card hpos
  rw [hcard, logb_two_pow] at h
  rw [coordDeficit]
  linarith

/-- **The per-coordinate deficits sum to the total deficit.**  Subadditivity of `H₂` along the
coordinate projections. -/
theorem sum_coordDeficit_le {m : ℕ} (L : FinLaw (A → Fin (2 ^ m))) {δ : ℝ}
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    ∑ α, coordDeficit L α ≤ δ * (Fintype.card A : ℝ) := by
  classical
  have hinj : Function.Injective
      (fun z : A → Fin (2 ^ m) => fun α => (fun z' : A → Fin (2 ^ m) => z' α) z) := by
    intro z z' h
    funext α
    exact congrFun h α
  have hsub := L.H₂_le_sum_H₂_map (fun (α : A) (z : A → Fin (2 ^ m)) => z α) hinj
  have hrw : ∑ α, coordDeficit L α
      = (m : ℝ) * (Fintype.card A : ℝ)
        - ∑ α, (L.map (fun z : A → Fin (2 ^ m) => z α)).H₂ := by
    simp only [coordDeficit]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    ring
  rw [hrw]
  nlinarith [hsub, hdef]

open Classical in
/-- The coordinates whose own window law misses the target deficit `δ'`. -/
noncomputable def badCoords {m : ℕ} (L : FinLaw (A → Fin (2 ^ m))) (δ' : ℝ) : Finset A :=
  Finset.univ.filter (fun α => δ' < coordDeficit L α)

open Classical in
/-- **Markov on the per-coordinate deficits.**  At most a `δ/δ'` fraction of the coordinates
can individually miss a deficit of `δ'`. -/
theorem card_badCoords_le {m : ℕ} (L : FinLaw (A → Fin (2 ^ m))) {δ δ' : ℝ} (_hδ' : 0 < δ')
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    ((badCoords L δ').card : ℝ) * δ' ≤ δ * (Fintype.card A : ℝ) := by
  classical
  have hsub : ∑ α ∈ badCoords L δ', coordDeficit L α ≤ ∑ α, coordDeficit L α :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun α _ _ => coordDeficit_nonneg L α)
  have hlow : ((badCoords L δ').card : ℝ) * δ' ≤ ∑ α ∈ badCoords L δ', coordDeficit L α := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun α hα => ?_
    have hmem : α ∈ Finset.univ.filter (fun α => δ' < coordDeficit L α) := hα
    have := (Finset.mem_filter.1 hmem).2
    linarith
  exact hlow.trans (hsub.trans (sum_coordDeficit_le L hdef))

end FinLaw

/-! ### One coordinate's own word statistics -/

/-- The window law at the single coordinate `α`, presented as a one-element family so that the
capture inequality applies to it verbatim. -/
noncomputable def soloLaw {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (L : FinLaw (A → Fin (2 ^ m))) (α : A) : FinLaw (Unit → Fin (2 ^ m)) :=
  L.map (fun z => fun _ => z α)

lemma H₂_soloLaw {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (L : FinLaw (A → Fin (2 ^ m))) (α : A) :
    (soloLaw L α).H₂ = (L.map (fun z : A → Fin (2 ^ m) => z α)).H₂ := by
  refine L.H₂_map_congr_comp (fun z : A → Fin (2 ^ m) => z α)
    (g := fun u : Fin (2 ^ m) => fun _ : Unit => u) ?_ _ (fun z => rfl)
  intro u u' h
  exact congrFun h ()

/-- **One coordinate's word frequency**, averaged over every position of its window. -/
noncomputable def coordAvg {A : Type*} [Fintype A] [DecidableEq A] (m ℓ : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) (α : A) (w : Fin (2 ^ ℓ)) : ℝ :=
  posAvg m ℓ (soloLaw L α) w

/-- **A good coordinate is good on its own.**  If the coordinate `α` carries all but `δ'` of its
`m` bits, then every `ℓ`-block word's frequency over the positions of *that one window* is
within `2√(log 2 · ℓδ'/(m−ℓ+1))` of `2^{−ℓ}`. -/
theorem abs_coordAvg_sub_le {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (α : A) (w : Fin (2 ^ ℓ))
    {δ' : ℝ} (hδ' : 0 < δ') (hα : FinLaw.coordDeficit L α ≤ δ') :
    |coordAvg m ℓ L α w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ' / ((m : ℝ) - ℓ + 1)) := by
  have hdef : ((m : ℝ) - δ') * (Fintype.card Unit : ℝ) ≤ (soloLaw L α).H₂ := by
    rw [H₂_soloLaw]
    have := hα
    rw [FinLaw.coordDeficit] at this
    simp only [Fintype.card_unit, Nat.cast_one, mul_one]
    linarith
  exact abs_posAvg_sub_le hℓ hℓm (soloLaw L α) w hδ' hdef

/-- **`coordAvg` refines `posAvg`**: the repo's already-controlled average over all coordinates
and all positions is the mean of the individual coordinates' averages. -/
theorem posAvg_eq_sum_coordAvg {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (m ℓ : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) :
    posAvg m ℓ L w = (∑ α : A, coordAvg m ℓ L α w) / (Fintype.card A : ℝ) := by
  classical
  have hA : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  have hm : (0 : ℝ) < ((m - ℓ + 1 : ℕ) : ℝ) := by
    have : 0 < m - ℓ + 1 := by omega
    exact_mod_cast this
  have hterm : ∀ α : A, coordAvg m ℓ L α w
      = (∑ p : Fin (m - ℓ + 1),
          (L.map (fun z : A → Fin (2 ^ m) => posAt m ℓ (p : ℕ) (z α))).prob {w})
        / ((m - ℓ + 1 : ℕ) : ℝ) := by
    intro α
    rw [coordAvg, posAvg]
    have hnum : ∀ c : Unit × Fin (m - ℓ + 1),
        ((soloLaw L α).map (fun z : Unit → Fin (2 ^ m) => posAt m ℓ (c.2 : ℕ) (z c.1))).prob {w}
          = (L.map (fun z : A → Fin (2 ^ m) => posAt m ℓ (c.2 : ℕ) (z α))).prob {w} := by
      intro c
      rw [soloLaw, FinLaw.prob_singleton_map_map]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.card_unit, Nat.cast_one, one_mul, Finset.univ_unique,
      Finset.sum_singleton, Nat.cast_add, Nat.cast_one]
    congr 1
    exact Finset.sum_congr rfl fun p _ => hnum (PUnit.unit, p)
  have hsum : ∑ α : A, coordAvg m ℓ L α w
      = (∑ α : A, ∑ p : Fin (m - ℓ + 1),
          (L.map (fun z : A → Fin (2 ^ m) => posAt m ℓ (p : ℕ) (z α))).prob {w})
        / ((m - ℓ + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun α _ => hterm α
  rw [posAvg, hsum, Fintype.sum_prod_type]
  field_simp

open Classical in
/-- **All but a `ρ`-fraction of the coordinates are individually good.**  This is the dual of
`abs_posAvg_restrict_sub_le`: rather than paying `√(1/ρ)` for an arbitrary sub-collection, one
*gets* a sub-collection of relative size `1 − ρ` whose members are good one by one, at the same
price `√(δ/ρ)`.

The good set is `(badCoords L (δ/ρ))ᶜ`, and it is explicitly a set of coordinates, so a
selection route may use it. -/
theorem card_good_ge {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    (1 - ρ) * (Fintype.card A : ℝ)
      ≤ ((Finset.univ.filter (fun α : A =>
          |coordAvg m ℓ L α w - 1 / (2 : ℝ) ^ ℓ|
            ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * (δ / ρ)
                / ((m : ℝ) - ℓ + 1)))).card : ℝ) := by
  classical
  set δ' : ℝ := δ / ρ with hδ'def
  have hδ' : 0 < δ' := by rw [hδ'def]; positivity
  set B : Finset A := FinLaw.badCoords L δ' with hB
  set G : Finset A := Finset.univ.filter (fun α : A =>
      |coordAvg m ℓ L α w - 1 / (2 : ℝ) ^ ℓ|
        ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ' / ((m : ℝ) - ℓ + 1))) with hG
  -- every coordinate outside `B` is good
  have hsub : Bᶜ ⊆ G := by
    intro α hα
    have hnot : ¬ (δ' < FinLaw.coordDeficit L α) := by
      intro hlt
      have hmem : α ∈ B := Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩
      exact (Finset.mem_compl.1 hα) hmem
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      abs_coordAvg_sub_le hℓ hℓm L α w hδ' (not_lt.1 hnot)⟩
  -- Markov bounds the bad set
  have hcardB : ((B.card : ℝ)) * δ' ≤ δ * (Fintype.card A : ℝ) :=
    FinLaw.card_badCoords_le L hδ' hdef
  have hBle : (B.card : ℝ) ≤ ρ * (Fintype.card A : ℝ) := by
    rw [hδ'def] at hcardB
    have h1 : (B.card : ℝ) * (δ / ρ) * ρ ≤ δ * (Fintype.card A : ℝ) * ρ :=
      mul_le_mul_of_nonneg_right hcardB hρ.le
    have h2 : (B.card : ℝ) * (δ / ρ) * ρ = (B.card : ℝ) * δ := by field_simp
    rw [h2] at h1
    have h3 : (B.card : ℝ) * δ ≤ (ρ * (Fintype.card A : ℝ)) * δ := by nlinarith [h1]
    exact le_of_mul_le_mul_right h3 hδ
  have hGcard : (Bᶜ.card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcompl : (Bᶜ.card : ℝ) = (Fintype.card A : ℝ) - (B.card : ℝ) := by
    rw [Finset.card_compl]
    have : B.card ≤ Fintype.card A := Finset.card_le_univ B
    push_cast [Nat.cast_sub this]
    ring
  have : (1 - ρ) * (Fintype.card A : ℝ) ≤ (Bᶜ.card : ℝ) := by
    rw [hcompl]
    nlinarith [hBle]
  linarith

open Classical in
/-- **A coordinate whose own deficit is `δ/ρ`.**  The bare Markov statement: the bad set has size
`< |A|` as soon as `ρ < 1`, so some coordinate misses it. -/
theorem exists_good_coord_deficit {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {m : ℕ}
    (L : FinLaw (A → Fin (2 ^ m))) {δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    ∃ α : A, FinLaw.coordDeficit L α ≤ δ / ρ := by
  classical
  set δ' : ℝ := δ / ρ with hδ'def
  have hδ' : 0 < δ' := by rw [hδ'def]; positivity
  have hcardB : ((FinLaw.badCoords L δ').card : ℝ) * δ' ≤ δ * (Fintype.card A : ℝ) :=
    FinLaw.card_badCoords_le L hδ' hdef
  have hBle : ((FinLaw.badCoords L δ').card : ℝ) ≤ ρ * (Fintype.card A : ℝ) := by
    rw [hδ'def] at hcardB
    have h1 : ((FinLaw.badCoords L δ').card : ℝ) * (δ / ρ) * ρ
        ≤ δ * (Fintype.card A : ℝ) * ρ := mul_le_mul_of_nonneg_right hcardB hρ0.le
    have h2 : ((FinLaw.badCoords L δ').card : ℝ) * (δ / ρ) * ρ
        = ((FinLaw.badCoords L δ').card : ℝ) * δ := by field_simp
    rw [h2] at h1
    have h3 : ((FinLaw.badCoords L δ').card : ℝ) * δ
        ≤ (ρ * (Fintype.card A : ℝ)) * δ := by nlinarith [h1]
    exact le_of_mul_le_mul_right h3 hδ
  have hApos : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  have hlt : ((FinLaw.badCoords L δ').card : ℝ) < (Fintype.card A : ℝ) := by
    nlinarith [hBle, hApos]
  have hne : (FinLaw.badCoords L δ')ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    have : (FinLaw.badCoords L δ').card < Fintype.card A := by exact_mod_cast hlt
    omega
  obtain ⟨α, hα⟩ := hne
  refine ⟨α, ?_⟩
  have hnot : ¬ (δ' < FinLaw.coordDeficit L α) := by
    intro hcon
    exact (Finset.mem_compl.1 hα) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
  exact not_lt.1 hnot

open Classical in
/-- **One atom, good for every word of every length at once.**  The per-coordinate deficit does
not mention `ℓ` or `w`, so a single coordinate outside `badCoords L (δ/ρ)` carries the capture
bound for **all** word lengths and all words simultaneously.  Such a coordinate exists as soon
as `ρ < 1`.

This is the selection tool: it picks a single window family — one atom's windows across the
sample times — whose own statistics are near-uniform, with no reference to which word is being
counted. -/
theorem exists_good_coord {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {m : ℕ}
    (L : FinLaw (A → Fin (2 ^ m))) {δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    ∃ α : A, ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ m → ∀ w : Fin (2 ^ ℓ),
      |coordAvg m ℓ L α w - 1 / (2 : ℝ) ^ ℓ|
        ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * (δ / ρ) / ((m : ℝ) - ℓ + 1)) := by
  classical
  set δ' : ℝ := δ / ρ with hδ'def
  have hδ' : 0 < δ' := by rw [hδ'def]; positivity
  have hcardB : ((FinLaw.badCoords L δ').card : ℝ) * δ' ≤ δ * (Fintype.card A : ℝ) :=
    FinLaw.card_badCoords_le L hδ' hdef
  have hBle : ((FinLaw.badCoords L δ').card : ℝ) ≤ ρ * (Fintype.card A : ℝ) := by
    rw [hδ'def] at hcardB
    have h1 : ((FinLaw.badCoords L δ').card : ℝ) * (δ / ρ) * ρ
        ≤ δ * (Fintype.card A : ℝ) * ρ := mul_le_mul_of_nonneg_right hcardB hρ0.le
    have h2 : ((FinLaw.badCoords L δ').card : ℝ) * (δ / ρ) * ρ
        = ((FinLaw.badCoords L δ').card : ℝ) * δ := by field_simp
    rw [h2] at h1
    have h3 : ((FinLaw.badCoords L δ').card : ℝ) * δ
        ≤ (ρ * (Fintype.card A : ℝ)) * δ := by nlinarith [h1]
    exact le_of_mul_le_mul_right h3 hδ
  have hApos : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  have hlt : ((FinLaw.badCoords L δ').card : ℝ) < (Fintype.card A : ℝ) := by
    nlinarith [hBle, hApos]
  have hne : (FinLaw.badCoords L δ')ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    have : (FinLaw.badCoords L δ').card < Fintype.card A := by exact_mod_cast hlt
    omega
  obtain ⟨α, hα⟩ := hne
  refine ⟨α, fun ℓ hℓ hℓm w => ?_⟩
  have hnot : ¬ (δ' < FinLaw.coordDeficit L α) := by
    intro hcon
    exact (Finset.mem_compl.1 hα) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
  exact abs_coordAvg_sub_le hℓ hℓm L α w hδ' (not_lt.1 hnot)


end NormalNumbers.G4Entropy

/-! ### The scale-`i` instance

At every scale, all but a `ρ`-fraction of the **atoms** read a window whose own word statistics
are already near-uniform.  For `G₄` the deficit is `entropy_E1`'s `δ = 50√K`, so at
`ρ = K^{−1/4}` (say) the error is `√(δ/ρ) ≈ K^{3/8}` against a window length `m = K/4`: a
positive fraction of atoms is individually good for every word length `ℓ = o(K^{1/4})`.
-/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

open Classical in
/-- **All but a `ρ`-fraction of the atoms are individually good at scale `i`.**  Stated for any
`x` supplying an entropy deficit of `δ` bits per window. -/
theorem card_goodAtoms_ge (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i) (x : ℝ) (w : Fin (2 ^ ℓ))
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hdef : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂) :
    (1 - ρ) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ ((Finset.univ.filter (fun α : (gridAt i).Atom =>
          |coordAvg (kk i) ℓ (jointLawAt i x) α w - 1 / (2 : ℝ) ^ ℓ|
            ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * (δ / ρ)
                / ((kk i : ℝ) - ℓ + 1)))).card : ℝ) :=
  card_good_ge hℓ hℓm (jointLawAt i x) w hδ hρ hdef

/-- `entropy_E1` in the per-window deficit shape: `δ = 50√K`. -/
theorem deficit_primeLambertFour (i : ℕ) :
    ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ := by
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  refine le_trans (le_of_eq ?_) hE1.le
  rw [card_Atom_gridAt]
  ring

open Classical in
/-- **For `G₄`, at every scale and every relative size `ρ`, at least `(1−ρ)|Atom_K|` atoms read
a window whose own `ℓ`-word frequencies are within `2√(log 2 · ℓ·50√K/ρ/(m_K−ℓ+1))` of
`2^{−ℓ}`.**

This is the affirmative counterpart of `chunks_insufficient`: an *arbitrary* sub-collection
costs `√(1/ρ)` and cannot be made small, but the *good* sub-collection of that size exists and
its members are certified **one atom at a time**. -/
theorem card_goodAtoms_primeLambertFour_ge (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i)
    (w : Fin (2 ^ ℓ)) {ρ : ℝ} (hρ : 0 < ρ) :
    (1 - ρ) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ ((Finset.univ.filter (fun α : (gridAt i).Atom =>
          |coordAvg (kk i) ℓ (jointLawAt i (primeLambertAtBase 4)) α w - 1 / (2 : ℝ) ^ ℓ|
            ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * (50 * Real.sqrt (KK i) / ρ)
                / ((kk i : ℝ) - ℓ + 1)))).card : ℝ) := by
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hδ : (0 : ℝ) < 50 * Real.sqrt (KK i) := by
    have := Real.sqrt_pos.2 hKpos
    linarith
  exact card_goodAtoms_ge i ℓ hℓ hℓm _ w hδ hρ (deficit_primeLambertFour i)

end NormalNumbers.G4.Sched
