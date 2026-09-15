/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4DeformationVerdict

/-!
# After the extraction, F′: **row-balanced (non-coordinatewise) cancellation is confined too**

`DESIGN-2026-09-15-deformation.md` §4 left one route open after the verdict on T(K′): cancel
the heavy layers *not* coordinatewise but **row-balanced** — on every row `ν` of the tensor
matrix `D_s^{⊗K}` (a unit cube of the grid with the parity signs `(−1)^{|T|}`), the signed
multiplicities of the shift values `ρ_{α,j} = j d_α − t_α` over the corners vanish.  The design
asked whether "balanced on every row" forces "ignores a coordinate" (true for `K = 1`).

**The answer is NO for `K ≥ 3`** (`ex_balanced`, `ex_not_ignoring`: at `K = 3`, `s = 2` the
function `[α₀=1 ∧ α₁=2] + [α₀=2 ∧ α₂=2]` is balanced on all eight rows and ignores no
coordinate) — **and it does not matter.**  The right invariant is the lattice
`MDF = {ρ : every full mixed difference vanishes}`:

* `mdf_of_balanced` — balanced ⇒ `MDF` (sum the level-set identities against the values);
* `mdf_d_t_of_two_balanced_layers` — two balanced layers `j ≠ j′` force **both** `d` and `t`
  into `MDF` (`(j′−j) d = ρ_{j′} − ρ_j`, `t = j d − ρ_j`; `ℤ` is torsion-free);
* `mdf_eq_zero_of_skel` — an `MDF` function vanishing on the coordinate skeleton
  `{α : ∃ i, α i = 0}` vanishes everywhere (induction on the coordinate sum: the top corner of a
  cube is determined by the other `2^K − 1`);
* `card_mdf_pairs_le` — hence at most `(2M+1)^{2·|skel|}` pairs, `|skel| ≤ K (s+1)^{K−1}`
  (`card_skel_le`): the exponent is `≈ 2H/K`, against L1's confinement `H log d_min`;
* `balanced_coeff_le`, `balanced_union_le` — the schedule verdict: any family of samplers with
  two row-balanced layers reads, below `L`, at most `L / dmin^{H/2} + (2 dmax+1)^{2K(s+1)^{K−1}} H m`
  positions: upper density `≤ dmin^{−H/2}`, exactly as `deformation_union_le`.

`balanced_of_update_invariant` shows coordinatewise cancellation is a special case, so this
verdict **subsumes** `G4DeformationVerdict` (T(K′) with `K′ ≥ 2` has two balanced layers) with a
shorter proof and no rigidity (R1–R3).  Nothing here is a statement about the normality of `G₄`.
-/

open Finset Function

namespace NormalNumbers.G4.RowBalance

variable {K s : ℕ}

/-- The corner of the unit cube based at `c` selected by the raised coordinate set `T`. -/
def corner (c : Fin K → Fin s) (T : Finset (Fin K)) : Fin K → Fin (s + 1) :=
  fun i => if i ∈ T then (c i).succ else (c i).castSucc

lemma corner_val (c : Fin K → Fin s) (T : Finset (Fin K)) (i : Fin K) :
    ((corner c T i : Fin (s + 1)) : ℕ) = (c i : ℕ) + (if i ∈ T then 1 else 0) := by
  unfold corner; split_ifs <;> simp

/-- The full mixed difference of `ρ` on every unit cube vanishes. -/
def MDF (ρ : (Fin K → Fin (s + 1)) → ℤ) : Prop :=
  ∀ c : Fin K → Fin s, ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * ρ (corner c T) = 0

/-- **Row-balanced**: on every unit cube (row of `D_s^{⊗K}`) and for every value `v`, the signed
multiplicity of `v` among the corner values vanishes. -/
def Balanced (ρ : (Fin K → Fin (s + 1)) → ℤ) : Prop :=
  ∀ (c : Fin K → Fin s) (v : ℤ),
    ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * (if ρ (corner c T) = v then 1 else 0) = 0

/-- Balanced ⇒ mixed-difference-free. -/
theorem mdf_of_balanced {ρ : (Fin K → Fin (s + 1)) → ℤ} (h : Balanced ρ) : MDF ρ := by
  intro c
  classical
  set S := (Finset.univ : Finset (Finset (Fin K))).image (fun T => ρ (corner c T)) with hS
  calc ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * ρ (corner c T)
      = ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * ∑ v ∈ S, (if ρ (corner c T) = v then v else 0) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ T))]
    _ = ∑ v ∈ S, v * ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card *
          (if ρ (corner c T) = v then 1 else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun T _ => ?_
        split_ifs <;> ring
    _ = 0 := Finset.sum_eq_zero fun v _ => by rw [h c v, mul_zero]

/-- `MDF` is closed under `ℤ`-linear combinations. -/
theorem mdf_linear {ρ₁ ρ₂ : (Fin K → Fin (s + 1)) → ℤ} (h₁ : MDF ρ₁) (h₂ : MDF ρ₂) (a b : ℤ) :
    MDF (fun α => a * ρ₁ α + b * ρ₂ α) := by
  intro c
  have e : ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * (a * ρ₁ (corner c T) + b * ρ₂ (corner c T))
      = a * ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * ρ₁ (corner c T)
        + b * ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * ρ₂ (corner c T) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [e, h₁ c, h₂ c]; ring

/-- `MDF` descends along a nonzero integer multiple. -/
theorem mdf_of_mul {ρ : (Fin K → Fin (s + 1)) → ℤ} {a : ℤ} (ha : a ≠ 0)
    (h : MDF (fun α => a * ρ α)) : MDF ρ := by
  intro c
  have := h c
  rw [show ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * (a * ρ (corner c T))
      = a * ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * ρ (corner c T) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun T _ => by ring] at this
  exact (mul_eq_zero.1 this).resolve_left ha

/-- Layer `j` of the shifts: `ρ_{α,j} = j d_α − t_α`. -/
def layer (j : ℕ) (d t : (Fin K → Fin (s + 1)) → ℤ) : (Fin K → Fin (s + 1)) → ℤ :=
  fun α => (j : ℤ) * d α - t α

/-- **Two balanced layers force `d` and `t` into `MDF`.** -/
theorem mdf_d_t_of_two_balanced_layers {d t : (Fin K → Fin (s + 1)) → ℤ} {j j' : ℕ}
    (hne : j ≠ j') (hj : Balanced (layer j d t)) (hj' : Balanced (layer j' d t)) :
    MDF d ∧ MDF t := by
  have m1 := mdf_of_balanced hj
  have m2 := mdf_of_balanced hj'
  have hd : MDF d := by
    refine mdf_of_mul (a := (j' : ℤ) - j) (by
      intro h0; exact hne (by exact_mod_cast (sub_eq_zero.1 h0).symm)) ?_
    have := mdf_linear m2 m1 1 (-1)
    convert this using 2 with α
    simp only [layer]; ring
  refine ⟨hd, ?_⟩
  have := mdf_linear hd m1 (j : ℤ) (-1)
  convert this using 2 with α
  simp only [layer]; ring

/-! ### The coordinate skeleton determines an `MDF` function -/

/-- The coordinate skeleton: atoms with some vanishing coordinate. -/
def skel (K s : ℕ) : Finset (Fin K → Fin (s + 1)) :=
  Finset.univ.filter (fun α => ∃ i, α i = 0)

/-- An `MDF` function vanishing on the skeleton vanishes everywhere. -/
theorem mdf_eq_zero_of_skel {ρ : (Fin K → Fin (s + 1)) → ℤ} (h : MDF ρ)
    (h0 : ∀ α ∈ skel K s, ρ α = 0) : ∀ α, ρ α = 0 := by
  classical
  suffices key : ∀ n, ∀ α : Fin K → Fin (s + 1), ∑ i, ((α i : Fin (s + 1)) : ℕ) = n → ρ α = 0 from
    fun α => key _ α rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α hα
  by_cases hz : ∃ i, α i = 0
  · exact h0 α (Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩)
  push_neg at hz
  have hpos : ∀ i, 0 < ((α i : Fin (s + 1)) : ℕ) := fun i =>
    Nat.pos_of_ne_zero (fun h => hz i (Fin.ext h))
  let c : Fin K → Fin s := fun i => ⟨(α i : ℕ) - 1, by have := (α i).isLt; have := hpos i; omega⟩
  have htop : corner c Finset.univ = α := by
    funext i; apply Fin.ext; rw [corner_val]; simp only [Finset.mem_univ, if_true, c]
    have := hpos i; omega
  have hle : ∀ T (i : Fin K), ((corner c T i : Fin (s + 1)) : ℕ) ≤ (α i : ℕ) := by
    intro T i; rw [corner_val]; simp only [c]; have := hpos i; split_ifs <;> omega
  have hsmall : ∀ T : Finset (Fin K), T ≠ Finset.univ → ρ (corner c T) = 0 := by
    intro T hT
    obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
      by_contra hall; push_neg at hall
      exact hT (Finset.eq_univ_iff_forall.2 hall)
    have hlt : ∑ k, ((corner c T k : Fin (s + 1)) : ℕ) < n := by
      rw [← hα]
      refine Finset.sum_lt_sum (fun k _ => hle T k) ⟨i, Finset.mem_univ _, ?_⟩
      rw [corner_val, if_neg hi]; simp only [c]; have := hpos i; omega
    exact ih _ hlt _ rfl
  have hsum := h c
  rw [Finset.sum_eq_single Finset.univ (fun T _ hT => by rw [hsmall T hT, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  rw [htop] at hsum
  exact (mul_eq_zero.1 hsum).resolve_left (pow_ne_zero _ (by norm_num))

/-- Two `MDF` functions agreeing on the skeleton coincide. -/
theorem mdf_ext {ρ ρ' : (Fin K → Fin (s + 1)) → ℤ} (h : MDF ρ) (h' : MDF ρ')
    (hs : ∀ α ∈ skel K s, ρ α = ρ' α) : ρ = ρ' := by
  have hd := mdf_linear h h' 1 (-1)
  have hz : ∀ α, (1 : ℤ) * ρ α + (-1) * ρ' α = 0 :=
    mdf_eq_zero_of_skel hd (fun α hα => by
      show (1 : ℤ) * ρ α + (-1) * ρ' α = 0
      rw [hs α hα]; ring)
  funext α
  have := hz α
  linarith

/-- The skeleton has at most `K (s+1)^{K−1}` points. -/
theorem card_skel_le (K s : ℕ) : (skel K s).card ≤ K * (s + 1) ^ (K - 1) := by
  classical
  -- the hyperplane `α i = 0`
  let hyp : Fin K → Finset (Fin K → Fin (s + 1)) := fun i => Finset.univ.filter (fun α => α i = 0)
  have hsub : skel K s ⊆ Finset.univ.biUnion hyp := by
    intro α hα
    obtain ⟨i, hi⟩ := (Finset.mem_filter.1 hα).2
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  have hhyp : ∀ i, (hyp i).card ≤ (s + 1) ^ (K - 1) := by
    intro i
    have hK : 1 ≤ K := i.pos
    let i₀ : Fin K := ⟨0, i.pos⟩
    let σ := Equiv.swap i i₀
    have hinj : Set.InjOn (fun α : Fin K → Fin (s + 1) => fun j => α (σ j)) (hyp i) := by
      intro α _ α' _ he
      funext j
      have := congrFun he (σ.symm j)
      simpa using this
    have hmaps : ∀ α ∈ hyp i, (fun j => α (σ j)) ∈ Rigidity.fibres K s 1 := by
      intro α hα
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j hj => ?_⟩
      have hj0 : j = i₀ := Fin.ext (by simp [i₀]; omega)
      subst hj0
      simp only [σ, Equiv.swap_apply_right]
      exact (Finset.mem_filter.1 hα).2
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    rwa [Rigidity.card_fibres K s 1 hK] at this
  calc (skel K s).card ≤ (Finset.univ.biUnion hyp).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (hyp i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin K, (s + 1) ^ (K - 1) := Finset.sum_le_sum fun i _ => hhyp i
    _ = K * (s + 1) ^ (K - 1) := by simp

/-! ### Counting `MDF` pairs -/

/-- A family of `MDF` pairs with values in `[−M, M]` has at most `(2M+1)^{2|skel|}` members. -/
theorem card_mdf_pairs_le {M : ℕ}
    (𝓕 : Finset (((Fin K → Fin (s + 1)) → ℤ) × ((Fin K → Fin (s + 1)) → ℤ)))
    (hmdf : ∀ p ∈ 𝓕, MDF p.1 ∧ MDF p.2)
    (hM : ∀ p ∈ 𝓕, ∀ α, |p.1 α| ≤ M ∧ |p.2 α| ≤ M) :
    𝓕.card ≤ (2 * M + 1) ^ (2 * (skel K s).card) := by
  classical
  let clamp : ℤ → Fin (2 * M + 1) := fun z =>
    ⟨(min (2 * (M : ℤ)) (max 0 (z + M))).toNat, by omega⟩
  have hclamp : ∀ z z' : ℤ, |z| ≤ M → |z'| ≤ M → clamp z = clamp z' → z = z' := by
    intro z z' hz hz' he
    have := congrArg (fun x : Fin (2 * M + 1) => (x : ℕ)) he
    simp only [clamp] at this
    rw [abs_le] at hz hz'
    omega
  let T := ({β // β ∈ skel K s} → Fin (2 * M + 1)) × ({β // β ∈ skel K s} → Fin (2 * M + 1))
  let Φ : (((Fin K → Fin (s + 1)) → ℤ) × ((Fin K → Fin (s + 1)) → ℤ)) → T :=
    fun p => (fun β => clamp (p.1 β), fun β => clamp (p.2 β))
  have hinj : Set.InjOn Φ 𝓕 := by
    intro p hp p' hp' he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 he
    have e1 : p.1 = p'.1 := by
      refine mdf_ext (hmdf p hp).1 (hmdf p' hp').1 fun β hβ => ?_
      have := congrFun h1 ⟨β, hβ⟩
      exact hclamp _ _ (hM p hp β).1 (hM p' hp' β).1 this
    have e2 : p.2 = p'.2 := by
      refine mdf_ext (hmdf p hp).2 (hmdf p' hp').2 fun β hβ => ?_
      have := congrFun h2 ⟨β, hβ⟩
      exact hclamp _ _ (hM p hp β).2 (hM p' hp' β).2 this
    exact Prod.ext e1 e2
  have hle : 𝓕.card ≤ Fintype.card T := by
    have := Finset.card_le_card_of_injOn Φ (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hinj
    simpa [Finset.card_univ] using this
  refine le_trans hle (le_of_eq ?_)
  simp only [T]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, ← pow_add]
  congr 1; ring

/-! ### Coordinatewise cancellation is a special case -/

lemma corner_insert (c : Fin K → Fin s) (T : Finset (Fin K)) (i : Fin K) :
    corner c (insert i T) = update (corner c T) i (c i).succ := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [corner]
  · simp [corner, update_of_ne hj, Finset.mem_insert, hj]

lemma corner_erase (c : Fin K → Fin s) (T : Finset (Fin K)) (i : Fin K) :
    corner c (T.erase i) = update (corner c T) i (c i).castSucc := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [corner]
  · simp [corner, update_of_ne hj, Finset.mem_erase, hj]

/-- A function ignoring coordinate `i` is row-balanced (pair each corner with its `i`-neighbour). -/
theorem balanced_of_update_invariant {ρ : (Fin K → Fin (s + 1)) → ℤ} (i : Fin K)
    (h : ∀ α c, ρ (update α i c) = ρ α) : Balanced ρ := by
  classical
  intro c v
  let g : Finset (Fin K) → Finset (Fin K) := fun T => if i ∈ T then T.erase i else insert i T
  have hρ : ∀ T, ρ (corner c (g T)) = ρ (corner c T) := by
    intro T
    simp only [g]
    split_ifs
    · rw [corner_erase, h]
    · rw [corner_insert, h]
  have hsgn : ∀ T, (-1 : ℤ) ^ (g T).card = -(-1 : ℤ) ^ T.card := by
    intro T
    simp only [g]
    split_ifs with hi
    · rw [show T.card = (T.erase i).card + 1 from (Finset.card_erase_add_one hi).symm, pow_succ]
      ring
    · rw [Finset.card_insert_of_notMem hi, pow_succ]; ring
  refine Finset.sum_ninvolution g (fun T => ?_) (fun T _ => ?_)
    (fun T => Finset.mem_univ _) (fun T => ?_)
  · rw [hρ, hsgn]; ring
  · intro hg
    have := congrArg Finset.card hg
    simp only [g] at this
    split_ifs at this with hi
    · rw [Finset.card_erase_of_mem hi] at this; have := Finset.card_pos.2 ⟨i, hi⟩; omega
    · rw [Finset.card_insert_of_notMem hi] at this; omega
  · by_cases hi : i ∈ T
    · have h2 : i ∉ T.erase i := fun h => (Finset.mem_erase.1 h).1 rfl
      simp only [g, if_pos hi, if_neg h2, Finset.insert_erase hi]
    · simp only [g, if_neg hi, if_pos (Finset.mem_insert_self i T), Finset.erase_insert hi]

/-- Coordinatewise cancellation of layer `i+1` (`CoordCancelUpTo`) makes that layer balanced. -/
theorem balanced_layer_of_coordCancel {K' : ℕ} {d t : (Fin K → Fin (s + 1)) → ℤ}
    (h : Rigidity.CoordCancelUpTo K' d t) (i : Fin K) (hi : (i : ℕ) < K') :
    Balanced (layer ((i : ℕ) + 1) d t) :=
  balanced_of_update_invariant i fun α c => by
    have := h i hi α c
    simp only [layer]; push_cast; linarith

/-! ### The `K = 3`, `s = 2` counterexample to "balanced ⇒ ignores a coordinate" -/

/-- `[α₀ = 1 ∧ α₁ = 2] + [α₀ = 2 ∧ α₂ = 2]` on `(Fin 3 → Fin 3)`. -/
def ex : (Fin 3 → Fin 3) → ℤ :=
  fun α => (if α 0 = 1 ∧ α 1 = 2 then 1 else 0) + (if α 0 = 2 ∧ α 2 = 2 then 1 else 0)

lemma ex_mem : ∀ α : Fin 3 → Fin 3, ex α = 0 ∨ ex α = 1 := by decide

/-- `ex` is row-balanced on every unit cube. -/
theorem ex_balanced : Balanced (K := 3) (s := 2) ex := by
  intro c v
  by_cases h0 : v = 0
  · subst h0; revert c; decide
  by_cases h1 : v = 1
  · subst h1; revert c; decide
  · refine Finset.sum_eq_zero fun T _ => ?_
    have : ex (corner c T) ≠ v := by
      rcases ex_mem (corner c T) with h | h <;> rw [h] <;> exact Ne.symm ‹_›
    rw [if_neg this, mul_zero]

/-- `ex` ignores no coordinate: for each `i` some update along `i` changes the value. -/
theorem ex_not_ignoring : ∀ i : Fin 3, ∃ (α : Fin 3 → Fin 3) (c : Fin 3),
    ex (update α i c) ≠ ex α := by decide

end NormalNumbers.G4.RowBalance

/-! ### The schedule verdict -/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Confine NormalNumbers.G4.RowBalance

/-- The exponent inequality: `4K·E + 2 + H/2 ≤ H` with `H = (K²+1)·E`, `K ≥ 9`. -/
lemma exponent_ineq' (i : ℕ) :
    4 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 2 + (KK i ^ 2 + 1) ^ KK i / 2
      ≤ (KK i ^ 2 + 1) ^ KK i := by
  have hK := KK_ge i
  set E := (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  have hH : (KK i ^ 2 + 1) ^ KK i = KK i * (KK i * E) + E := by
    have h2 : KK i * (KK i * E) + E = (KK i ^ 2 + 1) * E := by ring
    rw [h2, hE, ← pow_succ', show KK i - 1 + 1 = KK i by omega]
  have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by positivity)
  have h1 : 9 * (KK i * E) ≤ KK i * (KK i * E) := Nat.mul_le_mul_right _ (by omega)
  have h2 : 9 ≤ KK i * E := by nlinarith
  rw [hH]
  omega

/-- **The density coefficient of the union over all row-balanced samplers is below
`dmin^{−H/2}`.** -/
theorem balanced_coeff_le (i : ℕ) :
    ((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
        * ((kk i : ℝ) * ((KK i ^ 2 + 1) ^ KK i : ℕ) * dmax i)
        / (2 * (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i))
      ≤ 1 / (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i / 2) := by
  set E := KK i * (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set D := dmin i with hD
  set Dm := dmax i with hDm
  have h9 : 9 ≤ D := nine_le_dmin i
  have hDm2 : Dm ≤ 2 * D := dmax_le i
  have hkey : 8 * (H * kk i) ≤ 2 * D := by
    have := key_size i
    have h8 : (8 : ℕ) ≤ 2 ^ (i + 3) := by
      have : (2 : ℕ) ^ 3 ≤ 2 ^ (i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    calc 8 * (H * kk i) ≤ 2 ^ (i + 3) * (H * kk i) := Nat.mul_le_mul_right _ h8
      _ ≤ 2 * D := this
  have ha : ((2 * Dm + 1 : ℕ) : ℝ) ≤ (D : ℝ) ^ 2 := by
    have : 2 * Dm + 1 ≤ D ^ 2 := by nlinarith
    exact_mod_cast this
  have hb : (kk i : ℝ) * (H : ℕ) * Dm ≤ (D : ℝ) ^ 2 := by
    have : kk i * H * Dm ≤ D ^ 2 := by nlinarith
    exact_mod_cast this
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hpowH2 : (0 : ℝ) < (D : ℝ) ^ (H / 2) := by positivity
  have hnum : ((2 * Dm + 1 : ℕ) : ℝ) ^ (2 * E) * ((kk i : ℝ) * (H : ℕ) * Dm)
      ≤ (D : ℝ) ^ (4 * E + 2) := by
    calc ((2 * Dm + 1 : ℕ) : ℝ) ^ (2 * E) * ((kk i : ℝ) * (H : ℕ) * Dm)
        ≤ ((D : ℝ) ^ 2) ^ (2 * E) * (D : ℝ) ^ 2 := by gcongr
      _ = (D : ℝ) ^ (4 * E + 2) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have hexp : (D : ℝ) ^ (4 * E + 2) * (D : ℝ) ^ (H / 2) ≤ (D : ℝ) ^ H := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hD1 (by have := exponent_ineq' i; omega)
  rw [div_le_div_iff₀ (by positivity) hpowH2]
  calc ((2 * Dm + 1 : ℕ) : ℝ) ^ (2 * E) * ((kk i : ℝ) * (H : ℕ) * Dm) * (D : ℝ) ^ (H / 2)
      ≤ (D : ℝ) ^ (4 * E + 2) * (D : ℝ) ^ (H / 2) := by gcongr
    _ ≤ (D : ℝ) ^ H := hexp
    _ ≤ 1 * (2 * (D : ℝ) ^ H) := by
        have : (0 : ℝ) ≤ (D : ℝ) ^ H := by positivity
        linarith

/-- **The verdict on row-balanced cancellation at the schedule.**  Any family of samplers of the
tensor shape — ℕ-valued multipliers in `[dmin, dmax]` and offsets `≤ dmax`, pairwise coprime,
each member with its own sample satisfying the exact identities — in which **some two distinct
layers are row-balanced** (coordinatewise or not) reads, below `L`, at most
`L / dmin^{H/2} + (2 dmax+1)^{2K(s+1)^{K−1}} · H · m` positions: upper density `≤ dmin^{−H/2}`. -/
theorem balanced_union_le (i : ℕ)
    {κ : Type*} [DecidableEq κ] (𝓕 : Finset κ)
    (d t : κ → (gridAt i).Atom → ℕ) (P : κ → Finset ℕ)
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (hbal : ∀ ν ∈ 𝓕, ∃ j j' : ℕ, j ≠ j' ∧
      RowBalance.Balanced (RowBalance.layer j (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ))) ∧
      RowBalance.Balanced (RowBalance.layer j' (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ))))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin i ≤ d ν α ∧ d ν α ≤ dmax i)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax i)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ n ∈ P ν, ∀ α, n % d ν α = t ν α)
    (U : ℕ → Prop) [DecidablePred U] {L : ℕ}
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ n ∈ P ν, ∃ α, ∃ h < kk i,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i / 2)
        + ((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
            * (((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i) := by
  classical
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set E := KK i * (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  have hcardF : 𝓕.card ≤ (2 * dmax i + 1) ^ (2 * E) := by
    set 𝓕' := 𝓕.image (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) with h𝓕'
    have hc : 𝓕.card = 𝓕'.card := (Finset.card_image_of_injOn hinj).symm
    rw [hc]
    have h1 := card_mdf_pairs_le (K := KK i) (s := KK i ^ 2) (M := dmax i) 𝓕'
      (by
        intro p hp
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨j, j', hne, hj, hj'⟩ := hbal ν hν
        exact mdf_d_t_of_two_balanced_layers hne hj hj')
      (by
        intro p hp α
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        constructor
        · show |((d ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast (hd ν hν α).2
        · show |((t ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast ht ν hν α)
    refine le_trans h1 (Nat.pow_le_pow_right (by omega) ?_)
    have := card_skel_le (KK i) (KK i ^ 2)
    omega
  have hU := union_card_le (ι := (gridAt i).Atom) 𝓕 d t P (dmin_pos i) hd hcop hP U hcov
  rw [card_Atom_gridAt] at hU
  have hcoef := balanced_coeff_le i
  set F : ℝ := ((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * E) with hF
  have hF' : (𝓕.card : ℝ) ≤ F := by rw [hF]; exact_mod_cast hcardF
  have hF0 : (0 : ℝ) ≤ F := by positivity
  have hpos : (0 : ℝ) ≤ (L : ℝ) * kk i * (H : ℕ) * dmax i / (2 * (dmin i : ℝ) ^ H)
      + (H : ℕ) * kk i := by positivity
  calc (((Finset.range L).filter U).card : ℝ)
      ≤ 𝓕.card * ((L : ℝ) * kk i * (H : ℕ) * dmax i / (2 * (dmin i : ℝ) ^ H) + (H : ℕ) * kk i) :=
        hU
    _ ≤ F * ((L : ℝ) * kk i * (H : ℕ) * dmax i / (2 * (dmin i : ℝ) ^ H) + (H : ℕ) * kk i) :=
        mul_le_mul_of_nonneg_right hF' hpos
    _ = (L : ℝ) * (F * ((kk i : ℝ) * (H : ℕ) * dmax i) / (2 * (dmin i : ℝ) ^ H))
          + F * ((H : ℕ) * kk i) := by ring
    _ ≤ (L : ℝ) * (1 / (dmin i : ℝ) ^ (H / 2)) + F * ((H : ℕ) * kk i) := by
        gcongr
    _ = (L : ℝ) / (dmin i : ℝ) ^ (H / 2) + F * ((H : ℕ) * kk i) := by ring

end NormalNumbers.G4.Sched
