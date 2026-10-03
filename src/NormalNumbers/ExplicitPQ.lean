/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitOmegaK
import NormalNumbers.FamilyDerandomizeVar
import NormalNumbers.PQGrid

/-!
# Manai's `P`/`Q` algorithm: `P(x)` normal, `Q(x)` non-normal

Sweep: `docs/OPEN-PROBLEMS-SWEEP-2026-10-03.md` §3.

**Target.**  Manai, *Digit Mixing under Polynomial Maps*, arXiv 2606.08325v1, §1.1: "A natural
next step would be an intrinsic algorithm constructing a number `x` for which `P(x)` is normal
and `Q(x)` is non-normal - provided that the polynomials `P` and `Q` are linearly independent."
"Normal" is absolute normality (the paper's convention).

**Transcription.**  Linear independence is too weak as written: `P = Q + 1` is independent of
`Q` and `P(x)` is normal iff `Q(x)` is (Wall).  The sharp condition is `P ∉ span_ℚ(1, Q)`
(`AffineIn`).  The headline (`exists_computable_PQ`) gives, for every non-constant `Q ∈ ℤ[X]`,
**one** computable `x` (a computable real, on an explicit monotone branch of `Q`) with `Q(x)`
not normal in base 2 and, for every `P ∈ ℤ[X]`, `P(x)` absolutely normal **iff**
`P ∉ span_ℚ(1, Q)`.  `Ω_k` (`ExplicitOmegaK`) is the case `Q = Xᵏ`, `deg P < k`
(`not_affineIn_X_pow`).

**Freshness (2026-10-03).**  `papers followups 2606.08325`: Manai 2609.24665 and 2508.09319 only.
⚠️ Manai 2609.24665 Thm 1.3 (proof in its §4.1) already contains the mechanism for a **single**
pair: applied to the local map `f = Q ∘ P⁻¹` (non-affine iff `P ∉ span(1, Q)`), it yields an
absolutely normal `P(x)` with `Q(x)` not normal, almost surely along a Bernoulli measure.  It is
not stated as an answer, it is not computable, and it handles one `P` with `f'' ≠ 0` on a shrunk
interval.  New here: one computable `x` for **all** `P ∉ span(1, Q)` at once, across the
inflection points of every `G_P`.

## Route (the `Ω_k` engine with `Xᵏ` replaced by `Q`)

* **Branch** (`IsBranch`): `|Q'| ≥ 1` on `[u, ∞)`, `u ∈ ℕ` (`exists_isBranch`).  The window
  `[u + 1, u + 2]` has integer endpoints, `Q` is injective there, and
  `a = 2Q(u+1) − Q(u+2)`, `c = 2(Q(u+2) − Q(u+1)) ≠ 0` send `y ∈ [1/2, 1]` onto `Q([u+1, u+2])`.
* **Point**: `x = Q⁻¹(a + c·y)` (`brInv`), `y = cantorReal e`.  `Q(x) = a + c y` is a rational
  affine image of a quarter-Cantor point, so not normal (`not_isNormal_rat_affine_cantorReal`).
* **Maps**: `G_P(y) = P(Q⁻¹(a + c y))` (`GP`) is analytic near the window and
  `G_P'' = c² · W_P(x) / Q'(x)³`, `W_P = P''Q' − P'Q''` (`wPoly`).  `W_P ≡ 0` iff
  `(P'/Q')' ≡ 0` iff `P ∈ span_ℚ(1, Q)` (`wPoly_ne_zero_of_not_affineIn`).
* **Cut**: `|G_P''(y)| ≥ L^{-(N+3)} Π_{z ∈ Z} |y − z|` with `|Z| ≤ N = deg W_P` and `L`
  depending only on `Q` (`deriv2_GP_lower`), fed to the cylinder cut made uniform in `N`
  (`pushFourier_le_of_deriv2_lower_unif`).
* **Derandomize**: the zero count `N` is unbounded over `P`, so the decay exponent `δ_N` shrinks;
  `FamilyDerandomize.exists_computable_absNormal_family_var` (proved) takes a per-index
  exponent, paying only `Kc 1 δ ≤ 32/δ²` (`Kc_one_le_of_le_one`, proved).

**Sibling control.**  For `P ∈ span_ℚ(1, Q)` the mechanism must fail, and does: `G_P` is
rational affine near the window (`GP_eq_of_affineIn`), so the cut's hypothesis is unsatisfiable
(`not_deriv2_lower_GP_of_affineIn`), and Wall makes `P(x)` non-normal
(`not_isAbsNormal_of_affineIn`).

Cited inputs: only `BakerBanajiUniformQuarterCantor` (computable form) and
`BakerBanajiAnalyticQuarterCantor` (a.e. form), both already refereed in `ExplicitOmegaK`.
-/

open MeasureTheory Filter Topology Polynomial

namespace NormalNumbers.ExplicitPQ

open ExplicitSquare ExplicitOmegaK

/-! ### The dichotomy condition -/

/-- `P` is a rational affine function of `Q`: `P ∈ span_ℚ(1, Q)`. -/
def AffineIn (P Q : ℤ[X]) : Prop :=
  ∃ α β : ℚ, P.map (Int.castRingHom ℚ) = C α * Q.map (Int.castRingHom ℚ) + C β

/-- The numerator of `(P ∘ Q⁻¹)''`: `W_P = P''Q' − P'Q''`. -/
noncomputable def wPoly (P Q : ℤ[X]) : ℤ[X] :=
  derivative (derivative P) * derivative Q - derivative P * derivative (derivative Q)

theorem aeval_eq_of_affineIn {P Q : ℤ[X]} {α β : ℚ}
    (h : P.map (Int.castRingHom ℚ) = C α * Q.map (Int.castRingHom ℚ) + C β) (x : ℝ) :
    aeval x P = (α : ℝ) * aeval x Q + β := by
  have := congrArg (aeval x) h
  rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap,
    map_add, map_mul, aeval_map_algebraMap, aeval_C, aeval_C] at this
  simpa using this

/-- Zero is not normal in base 2 (its digit sequence never contains `1`). -/
theorem not_isNormal_two_zero : ¬ IsNormal 2 0 := by
  intro h
  have hcount : ∀ l : List ℕ, (∀ d ∈ l, d = 0) → countOccurrences [1] l = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ha : a = 0 := hl a (List.mem_cons_self ..)
      have ih' := ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
      unfold countOccurrences at ih' ⊢
      rw [List.tails_cons, List.countP_cons, ih', ha]
      rfl
  have hdig : ∀ i, digitOf 2 (Int.fract (0 : ℝ)) i = 0 := by
    intro i; simp [digitOf]
  have ht := h [1] (by simp) (by simp)
  have h0 : (fun n : ℕ => (countOccurrences [1] ((List.range n).map
      (digitOf 2 (Int.fract (0 : ℝ)))) : ℝ) / n) = fun _ => 0 := by
    funext n
    rw [hcount _ (fun d hd => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hd; exact hdig i)]
    simp
  rw [h0] at ht
  have := tendsto_nhds_unique ht tendsto_const_nhds
  norm_num at this

/-- A rational is not normal in base 2 (Wall moves it to `0`). -/
theorem not_isNormal_two_ratCast (β : ℚ) : ¬ IsNormal 2 (β : ℝ) := by
  intro h
  have := isNormal_rat_mul_add 2 le_rfl _ 1 (-β) one_ne_zero h
  apply not_isNormal_two_zero
  convert this using 1
  push_cast; ring

/-- **Sharpness (Wall).**  An affine-in-`Q` polynomial inherits non-normality from `Q(x)`
(`α = 0` gives a rational).  Proved. -/
theorem not_isAbsNormal_of_affineIn {P Q : ℤ[X]} (h : AffineIn P Q) {x : ℝ}
    (hx : ¬ IsNormal 2 (aeval x Q)) : ¬ IsAbsNormal (aeval x P) := by
  obtain ⟨α, β, hαβ⟩ := h
  intro hP
  have h2 := hP 2 le_rfl
  rw [aeval_eq_of_affineIn hαβ] at h2
  by_cases hα : α = 0
  · subst hα
    apply not_isNormal_two_ratCast β
    simpa using h2
  · apply hx
    have := isNormal_rat_mul_add 2 le_rfl _ α⁻¹ (-(β / α)) (inv_ne_zero hα) h2
    convert this using 1
    have hα' : (α : ℝ) ≠ 0 := by exact_mod_cast hα
    push_cast
    field_simp
    ring

/-- **Guard (content locator): `Q = Xᵏ` recovers `Ω_k`.**  Every `p` with `1 ≤ deg p < k` is
outside `span_ℚ(1, Xᵏ)`, so the headline at `Q = Xᵏ` contains `exists_computable_mem_Omega`'s
normality half.  Proved. -/
theorem not_affineIn_X_pow (k : ℕ) (p : ℤ[X]) (h1 : 1 ≤ p.natDegree) (hk : p.natDegree < k) :
    ¬ AffineIn p (X ^ k) := by
  rintro ⟨α, β, h⟩
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hdeg : (p.map (Int.castRingHom ℚ)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective hinj p
  have hk0 : k ≠ 0 := by omega
  have hck := congrArg (fun r => r.coeff k) h
  simp only [Polynomial.map_pow, map_X, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one,
    coeff_C, if_neg hk0, add_zero] at hck
  rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)] at hck
  rw [← hck, C_0, zero_mul, zero_add] at h
  have := congrArg natDegree h
  rw [natDegree_C, hdeg] at this
  omega

/-- `p'q = pq'` with `q ≠ 0` forces `p = αq` over `ℚ`: put `α = p(x₀)/q(x₀)` and compare root
multiplicities of `p − αq` at `x₀`.  Proved. -/
theorem wronsk_const (p q : ℚ[X]) (hq : q ≠ 0)
    (h : derivative p * q = p * derivative q) : ∃ α : ℚ, p = C α * q := by
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℚ, q.eval x0 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (eq_zero_of_infinite_isRoot q (by
      convert Set.infinite_univ (α := ℚ); ext x; simp [hall x]))
  refine ⟨p.eval x0 / q.eval x0, ?_⟩
  set r := p - C (p.eval x0 / q.eval x0) * q with hr
  have hr' : derivative r * q = r * derivative q := by
    rw [hr, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
    linear_combination h
  have hrx : r.eval x0 = 0 := by
    rw [hr, eval_sub, eval_mul, eval_C]; field_simp; ring
  by_contra hne
  have hr0 : r ≠ 0 := fun h0 => hne (by rw [← sub_eq_zero]; exact h0)
  obtain ⟨s, hs, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr0 x0
  have hk : 0 < r.rootMultiplicity x0 := (rootMultiplicity_pos hr0).2 hrx
  obtain ⟨j, hj⟩ : ∃ j, r.rootMultiplicity x0 = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
  rw [hj] at hs
  have hsx : s.eval x0 ≠ 0 := by
    intro h0; exact hnd (dvd_iff_isRoot.2 h0)
  have key : (X - C x0) ^ j * (C ((j : ℚ) + 1) * s * q +
      (X - C x0) * (derivative s * q - s * derivative q)) = (X - C x0) ^ j * 0 := by
    rw [hs, derivative_mul, derivative_X_sub_C_pow] at hr'
    simp only [Nat.add_sub_cancel] at hr'
    rw [mul_zero]
    have : ((↑(j + 1) : ℚ[X])) = C ((j : ℚ) + 1) := by simp
    rw [← sub_eq_zero] at hr'
    rw [← hr']
    push_cast
    simp only [map_add, map_natCast, C_1]
    ring
  have key2 := mul_left_cancel₀ (pow_ne_zero j (X_sub_C_ne_zero x0)) key
  have := congrArg (eval x0) key2
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero,
    eval_zero] at this
  have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  exact hsx (by
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hj1
      · exact h
    · exact absurd h hx0)

/-- **`W_P ≢ 0` off the span.**

Confidence 93%.  English proof: over `ℚ`, `W_P = 0` says `P''Q' = P'Q''`, i.e.
`(P'/Q')' = 0` as rational functions (`Q' ≠ 0` since `deg Q ≥ 1`), so `P' = αQ'` with `α ∈ ℚ`
(a rational function with zero derivative in characteristic 0 is constant), and integrating,
`P = αQ + β`.  Contrapositive. -/
theorem wPoly_ne_zero_of_not_affineIn {P Q : ℤ[X]} (hQ : 0 < Q.natDegree) (hP : ¬ AffineIn P Q) :
    wPoly P Q ≠ 0 := by
  intro hW
  apply hP
  set f := Int.castRingHom ℚ
  have hinj : Function.Injective f := Int.cast_injective
  have hWq := congrArg (Polynomial.map f) hW
  simp only [wPoly, Polynomial.map_sub, Polynomial.map_mul, ← derivative_map, Polynomial.map_zero]
    at hWq
  have hq : derivative (Q.map f) ≠ 0 := by
    intro h
    have := derivative_eq_zero.1 h
    rw [natDegree_map_eq_of_injective hinj] at this; omega
  obtain ⟨α, hα⟩ := wronsk_const _ _ hq (by rw [← sub_eq_zero]; exact hWq)
  have hd : derivative (P.map f - C α * Q.map f) = 0 := by
    rw [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, hα, sub_self]
  refine ⟨α, (P.map f - C α * Q.map f).coeff 0, ?_⟩
  rw [← eq_C_of_natDegree_eq_zero (derivative_eq_zero.1 hd), add_sub_cancel]

/-! ### The branch and the maps -/

/-- A branch start: `|Q'| ≥ 1` on `[u, ∞)`. -/
def IsBranch (Q : ℤ[X]) (u : ℕ) : Prop :=
  ∀ x : ℝ, (u : ℝ) ≤ x → 1 ≤ |aeval x (derivative Q)|

/-- `a = 2Q(u+1) − Q(u+2)`. -/
noncomputable def aQ (Q : ℤ[X]) (u : ℕ) : ℤ := 2 * Q.eval ((u : ℤ) + 1) - Q.eval ((u : ℤ) + 2)

/-- `c = 2(Q(u+2) − Q(u+1))`, so `y ↦ a + c y` maps `[1/2, 1]` onto `[Q(u+1), Q(u+2)]`. -/
noncomputable def cQ (Q : ℤ[X]) (u : ℕ) : ℤ := 2 * (Q.eval ((u : ℤ) + 2) - Q.eval ((u : ℤ) + 1))

/-- The branch inverse of `Q` on `(u, ∞)`. -/
noncomputable def brInv (Q : ℤ[X]) (u : ℕ) (w : ℝ) : ℝ :=
  Function.invFunOn (fun x : ℝ => aeval x Q) (Set.Ioi (u : ℝ)) w

/-- `G_P(y) = P(Q⁻¹(a + c y))`. -/
noncomputable def GP (Q : ℤ[X]) (u : ℕ) (P : ℤ[X]) (y : ℝ) : ℝ :=
  aeval (brInv Q u ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y)) P

/-- The witness `x = Q⁻¹(a + c · cantorReal e)`. -/
noncomputable def xPQ (Q : ℤ[X]) (u : ℕ) (e : ℕ → Bool) : ℝ :=
  brInv Q u ((aQ Q u : ℝ) + (cQ Q u : ℝ) * cantorReal e)

theorem GP_cantorReal (Q : ℤ[X]) (u : ℕ) (P : ℤ[X]) (e : ℕ → Bool) :
    GP Q u P (cantorReal e) = aeval (xPQ Q u e) P := rfl

/-- **A branch exists.**

Confidence 95%.  English proof: `Q' ≠ 0` has integer leading coefficient `ℓ`, `|ℓ| ≥ 1`, and
degree `d − 1`.  With `B = Σ_j |coeff_j Q'|`, for `x ≥ B + 1` we get
`|Q'(x)| ≥ |ℓ| x^{d−1} − (B − |ℓ|) x^{d−2} ≥ x^{d−2}(x − B) ≥ 1` (for `d = 1`, `Q' = ℓ`). -/
theorem exists_isBranch (Q : ℤ[X]) (hQ : 0 < Q.natDegree) : ∃ u : ℕ, IsBranch Q u := by
  set p : ℝ[X] := (derivative Q).map (Int.castRingHom ℝ) with hp
  have hev : ∀ x : ℝ, aeval x (derivative Q) = eval x p := fun x => by
    rw [hp, eval_map, aeval_def]; rfl
  have hQ' : derivative Q ≠ 0 := by
    intro h
    have := derivative_eq_zero.1 h
    omega
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  by_cases hd : 0 < p.degree
  · obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
      ((Polynomial.abs_tendsto_atTop p hd).eventually_ge_atTop 1)
    refine ⟨⌈B⌉₊, fun x hx => ?_⟩
    rw [hev]; exact hB x ((Nat.le_ceil B).trans hx)
  · push Not at hd
    have h0 : (derivative Q).natDegree = 0 := by
      have := natDegree_eq_zero_iff_degree_le_zero.2 hd
      rwa [hp, natDegree_map_eq_of_injective hinj] at this
    rw [natDegree_eq_zero] at h0
    obtain ⟨c, hc⟩ := h0
    have hc0 : c ≠ 0 := by rintro rfl; exact hQ' (by rw [← hc, C_0])
    refine ⟨0, fun x _ => ?_⟩
    rw [← hc, aeval_C]
    simp only [algebraMap_int_eq, eq_intCast]
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hc0

/-- On a branch `σQ` is expanding (`σ = ±1`): `t − s ≤ σQ(t) − σQ(s)` for `u ≤ s ≤ t`.  Proved
(IVT for the sign of `Q'`, then the mean value inequality). -/
theorem branch_expand {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ s t : ℝ, (u : ℝ) ≤ s → s ≤ t →
      t - s ≤ σ * aeval t Q - σ * aeval s Q := by
  have hc' : Continuous fun x : ℝ => aeval x (derivative Q) := by fun_prop
  have hsign : (∀ x : ℝ, (u : ℝ) ≤ x → 1 ≤ aeval x (derivative Q)) ∨
      (∀ x : ℝ, (u : ℝ) ≤ x → 1 ≤ -aeval x (derivative Q)) := by
    have key : ∀ x y : ℝ, (u : ℝ) ≤ x → (u : ℝ) ≤ y →
        ¬ (aeval x (derivative Q) < 0 ∧ 0 < aeval y (derivative Q)) := by
      rintro x y hx hy ⟨h1, h2⟩
      obtain ⟨z, hz, hz0⟩ := isPreconnected_Ici.intermediate_value hx hy hc'.continuousOn
        ⟨h1.le, h2.le⟩
      have := hu z hz
      simp only at hz0; rw [hz0] at this; norm_num at this
    have hu0 := hu u le_rfl
    rcases le_abs'.1 hu0 with h | h
    · right; intro x hx
      have := hu x hx
      rcases le_abs'.1 this with h' | h'
      · linarith
      · exact absurd ⟨by linarith, by linarith⟩ (key u x le_rfl hx)
    · left; intro x hx
      have := hu x hx
      rcases le_abs'.1 this with h' | h'
      · exact absurd ⟨by linarith, by linarith⟩ (key x u hx le_rfl)
      · linarith
  have hd : ∀ σ : ℝ, ∀ x, HasDerivAt (fun x : ℝ => σ * aeval x Q) (σ * aeval x (derivative Q)) x :=
    fun σ x => (Polynomial.hasDerivAt_aeval Q x).const_mul σ
  have go : ∀ σ : ℝ, (∀ x : ℝ, (u : ℝ) ≤ x → 1 ≤ σ * aeval x (derivative Q)) →
      ∀ s t : ℝ, (u : ℝ) ≤ s → s ≤ t → t - s ≤ σ * aeval t Q - σ * aeval s Q := by
    intro σ hσ s t hs hst
    have := (convex_Ici (u : ℝ)).mul_sub_le_image_sub_of_le_deriv (f := fun x => σ * aeval x Q)
      (by fun_prop) (fun x _ => (hd σ x).differentiableAt.differentiableWithinAt) (C := 1)
      (fun x hx => by
        rw [interior_Ici] at hx
        rw [(hd σ x).deriv]; exact hσ x (le_of_lt hx)) s hs t (le_trans hs hst) hst
    simpa using this
  rcases hsign with h | h
  · exact ⟨1, Or.inl rfl, go 1 (fun x hx => by simpa using h x hx)⟩
  · exact ⟨-1, Or.inr rfl, go (-1) (fun x hx => by simpa using h x hx)⟩

theorem aeval_intCast_eq (Q : ℤ[X]) (z : ℤ) : ((Q.eval z : ℤ) : ℝ) = aeval (z : ℝ) Q := by
  simp [aeval_def, eval₂_eq_eval_map]

/-- **The window and the branch inverse.**

Confidence 92%.  English proof: on `[u, ∞)`, `Q'` is continuous with `|Q'| ≥ 1`, so it has a
constant sign (IVT) and `Q` is strictly monotone there with `|Q(s) − Q(t)| ≥ |s − t|` (MVT).
Hence `c ≠ 0` (`|c| ≥ 2`), `Q` is injective on `[u+1, u+2]`, and for `y` in a small open
neighbourhood `U` of `[1/2, 1]` the value `a + c y` lies in `Q((u, ∞))` (an open interval by
IVT, containing `[Q(u+1), Q(u+2)]` in its interior); `invFunOn` then returns its unique preimage
in `(u, ∞)`, which lies in `[u+1, u+2]` when `y ∈ [1/2, 1]` (endpoints `y = 1/2 ↦ u+1`,
`y = 1 ↦ u+2`, monotonicity). -/
theorem branch_spec {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    cQ Q u ≠ 0 ∧ Set.InjOn (fun x : ℝ => aeval x Q) (Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2)) ∧
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (1 / 2 : ℝ) 1 ⊆ U ∧
      (∀ y ∈ U, aeval (brInv Q u ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y)) Q =
        (aQ Q u : ℝ) + (cQ Q u : ℝ) * y) ∧
      ∀ y ∈ Set.Icc (1 / 2 : ℝ) 1,
        brInv Q u ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y) ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2) := by
  obtain ⟨σ, hσ, hexp⟩ := branch_expand hu
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set g : ℝ → ℝ := fun x => σ * aeval x Q with hg
  have hmono : ∀ s t : ℝ, (u : ℝ) ≤ s → s < t → g s < g t := fun s t hs hst => by
    have := hexp s t hs hst.le; simp only [hg]; linarith
  have ha : (aQ Q u : ℝ) = 2 * aeval ((u : ℝ) + 1) Q - aeval ((u : ℝ) + 2) Q := by
    simp only [aQ]; push_cast
    rw [aeval_intCast_eq, aeval_intCast_eq]; push_cast; ring
  have hc : (cQ Q u : ℝ) = 2 * (aeval ((u : ℝ) + 2) Q - aeval ((u : ℝ) + 1) Q) := by
    simp only [cQ]; push_cast
    rw [aeval_intCast_eq, aeval_intCast_eq]; push_cast; ring
  set A := g ((u : ℝ) + 1) with hA
  set B := g ((u : ℝ) + 2) with hB
  have hAB : 1 ≤ B - A := by
    have := hexp ((u : ℝ) + 1) ((u : ℝ) + 2) (by linarith) (by linarith); simp only [hA, hB, hg]; linarith
  have hval : ∀ y : ℝ, σ * ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y) = A + (B - A) * (2 * y - 1) := by
    intro y; rw [ha, hc]; simp only [hA, hB, hg]; ring
  have hgu : g u ≤ A - 1 := by
    have := hexp (u : ℝ) ((u : ℝ) + 1) le_rfl (by linarith); simp only [hA, hg]; linarith
  have hgu3 : B + 1 ≤ g ((u : ℝ) + 3) := by
    have := hexp ((u : ℝ) + 2) ((u : ℝ) + 3) (by linarith) (by linarith); simp only [hB, hg]; linarith
  have hgcont : Continuous g := by simp only [hg]; fun_prop
  refine ⟨?_, ?_, {y | σ * ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y) ∈ Set.Ioo (g u) (g ((u : ℝ) + 3))},
    ?_, ?_, ?_, ?_⟩
  · intro h0
    have : (cQ Q u : ℝ) = 0 := by exact_mod_cast h0
    have h2 := hval 1; have h1 := hval 0
    rw [this] at h2 h1; linarith
  · intro s hs t ht hst
    simp only at hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hmono s t (by linarith [hs.1]) h; simp only [hg, hst] at this; linarith
    · have := hmono t s (by linarith [ht.1]) h; simp only [hg, hst] at this; linarith
  · exact isOpen_Ioo.preimage (by fun_prop)
  · intro y hy
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo, hval]
    constructor <;> nlinarith [hy.1, hy.2]
  · intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo (by linarith : (u : ℝ) ≤ (u : ℝ) + 3)
      hgcont.continuousOn hy
    have hex : ∃ x ∈ Set.Ioi (u : ℝ), aeval x Q = (aQ Q u : ℝ) + (cQ Q u : ℝ) * y := by
      refine ⟨x, hx.1, ?_⟩
      have := congrArg (σ * ·) hgx
      simp only [hg, ← mul_assoc, hσ2, one_mul] at this
      exact this
    exact Function.invFunOn_eq hex
  · intro y hy
    set w := (aQ Q u : ℝ) + (cQ Q u : ℝ) * y
    have hw1 : A ≤ σ * w := by rw [hval]; nlinarith [hy.1, hy.2]
    have hw2 : σ * w ≤ B := by rw [hval]; nlinarith [hy.1, hy.2]
    have hex : ∃ x ∈ Set.Ioi (u : ℝ), aeval x Q = w := by
      obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc (by linarith : (u : ℝ) + 1 ≤ (u : ℝ) + 2)
        hgcont.continuousOn ⟨hw1, hw2⟩
      refine ⟨x, by simp only [Set.mem_Ioi]; linarith [hx.1], ?_⟩
      have := congrArg (σ * ·) hgx
      simp only [hg, ← mul_assoc, hσ2, one_mul] at this
      exact this
    have hmem : brInv Q u w ∈ Set.Ioi (u : ℝ) := Function.invFunOn_mem hex
    have hQ : aeval (brInv Q u w) Q = w := Function.invFunOn_eq hex
    have hgx : g (brInv Q u w) = σ * w := by simp only [hg, hQ]
    simp only [Set.mem_Ioi] at hmem
    constructor
    · by_contra hlt; push Not at hlt
      have := hmono _ _ hmem.le hlt; linarith
    · by_contra hlt; push Not at hlt
      have := hmono _ _ (by linarith) hlt; linarith

/-! Branch inverse: injectivity on `(u, ∞)`, open image, analyticity (inverse function theorem). -/

theorem injOn_Ioi_of_isBranch {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    Set.InjOn (fun x : ℝ => aeval x Q) (Set.Ioi (u : ℝ)) := by
  obtain ⟨σ, hσ, hexp⟩ := branch_expand hu
  intro s hs t ht hst
  simp only at hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hexp s t (le_of_lt hs) h.le; rw [hst] at this; linarith
  · have := hexp t s (le_of_lt ht) h.le; rw [hst] at this; linarith

theorem analyticAt_brInv {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {w₀ : ℝ}
    (hev : ∀ᶠ w in 𝓝 w₀, brInv Q u w ∈ Set.Ioi (u : ℝ) ∧ aeval (brInv Q u w) Q = w) :
    AnalyticAt ℝ (brInv Q u) w₀ := by
  set f : ℝ → ℝ := fun x => aeval x Q with hf
  obtain ⟨h0mem, h0eq⟩ := hev.self_of_nhds
  set x₀ := brInv Q u w₀
  have hfa : AnalyticAt ℝ f x₀ := analyticAt_id.aeval_polynomial Q
  have hd : deriv f x₀ ≠ 0 := by
    rw [(Polynomial.hasDerivAt_aeval Q x₀).deriv]
    intro h; have := hu x₀ (le_of_lt h0mem); rw [h] at this; norm_num at this
  have hr := hfa.analyticAt_localInverse hd
  set r := hfa.hasStrictDerivAt.localInverse _ _ _ hd
  have hfx : f x₀ = w₀ := h0eq
  rw [hfx] at hr
  have hrx : r w₀ = x₀ := by
    rw [← hfx]; exact HasStrictFDerivAt.localInverse_apply_image ..
  have hrc : ContinuousAt r w₀ := hr.continuousAt
  have hright : ∀ᶠ w in 𝓝 w₀, f (r w) = w := by
    have := HasStrictDerivAt.eventually_right_inverse hfa.hasStrictDerivAt hd
    rwa [hfx] at this
  have hrin : ∀ᶠ w in 𝓝 w₀, r w ∈ Set.Ioi (u : ℝ) :=
    hrc.eventually (by rw [hrx]; exact isOpen_Ioi.mem_nhds h0mem)
  refine hr.congr ?_
  filter_upwards [hev, hright, hrin] with w hw h1 h2
  exact injOn_Ioi_of_isBranch hu h2 hw.1 (h1.trans hw.2.symm)

theorem isOpen_image_Ioi {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    IsOpen ((fun x : ℝ => aeval x Q) '' Set.Ioi (u : ℝ)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hd : aeval x (derivative Q) ≠ 0 := by
    intro h; have := hu x (le_of_lt hx); rw [h] at this; norm_num at this
  rw [← ((Polynomial.hasStrictDerivAt_aeval Q x).map_nhds_eq hd)]
  exact Filter.image_mem_map (isOpen_Ioi.mem_nhds hx)

theorem brInv_spec {Q : ℤ[X]} {u : ℕ} {w : ℝ}
    (hw : w ∈ (fun x : ℝ => aeval x Q) '' Set.Ioi (u : ℝ)) :
    brInv Q u w ∈ Set.Ioi (u : ℝ) ∧ aeval (brInv Q u w) Q = w := by
  obtain ⟨x, hx, hxw⟩ := hw
  have hex : ∃ x ∈ Set.Ioi (u : ℝ), aeval x Q = w := ⟨x, hx, hxw⟩
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

/-- **`G_P` is analytic near the window, uniformly in `P`.**

Confidence 85%.  English proof: `Q` restricted to `(u, ∞)` has nonvanishing derivative, so it is
a local analytic diffeomorphism and its inverse is analytic
(`OpenPartialHomeomorph.analyticAt_symm`, from `HasStrictDerivAt.toOpenPartialHomeomorph`); on
`branch_spec`'s `U`, `brInv` agrees with that inverse, and `G_P` is a polynomial in it composed
with the affine `y ↦ a + c y`.  `U` does not depend on `P`. -/
theorem analyticOnNhd_GP {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (1 / 2 : ℝ) 1 ⊆ U ∧
      ∀ P : ℤ[X], AnalyticOnNhd ℝ (GP Q u P) U := by
  obtain ⟨-, -, U₀, -, hsub₀, hinv, hmem⟩ := branch_spec hu
  set W := (fun x : ℝ => aeval x Q) '' Set.Ioi (u : ℝ) with hW
  have hWo : IsOpen W := isOpen_image_Ioi hu
  refine ⟨(fun y : ℝ => (aQ Q u : ℝ) + (cQ Q u : ℝ) * y) ⁻¹' W,
    hWo.preimage (by fun_prop), fun y hy => ?_, fun P y hy => ?_⟩
  · refine ⟨_, ?_, hinv y (hsub₀ hy)⟩
    have := (hmem y hy).1
    simp only [Set.mem_Ioi]; linarith
  · have hbr : AnalyticAt ℝ (brInv Q u) ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y) :=
      analyticAt_brInv hu (by
        filter_upwards [hWo.mem_nhds hy] with w hw using brInv_spec hw)
    have haff : AnalyticAt ℝ (fun y : ℝ => (aQ Q u : ℝ) + (cQ Q u : ℝ) * y) y :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact (AnalyticAt.comp (g := brInv Q u) (f := fun y : ℝ => (aQ Q u : ℝ) + (cQ Q u : ℝ) * y) (x := y) hbr haff).aeval_polynomial P

/-! Calculus of `G_P`: `G_P' = c P'(x)/Q'(x)`, `G_P'' = c² W_P(x)/Q'(x)³`, `x = Xf y`. -/

/-- The open set of `y` with `a + c y ∈ Q((u, ∞))`. -/
def Vset (Q : ℤ[X]) (u : ℕ) : Set ℝ :=
  (fun y : ℝ => (aQ Q u : ℝ) + (cQ Q u : ℝ) * y) ⁻¹' ((fun x : ℝ => aeval x Q) '' Set.Ioi (u : ℝ))

/-- `x(y) = Q⁻¹(a + c y)`. -/
noncomputable def Xf (Q : ℤ[X]) (u : ℕ) (y : ℝ) : ℝ :=
  brInv Q u ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y)

theorem GP_eq_Xf (Q : ℤ[X]) (u : ℕ) (P : ℤ[X]) : GP Q u P = fun y => aeval (Xf Q u y) P := rfl

theorem isOpen_Vset {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) : IsOpen (Vset Q u) :=
  (isOpen_image_Ioi hu).preimage (by fun_prop)

theorem window_sub_Vset {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    Set.Icc (1 / 2 : ℝ) 1 ⊆ Vset Q u := by
  obtain ⟨-, -, U₀, -, hsub₀, hinv, hmem⟩ := branch_spec hu
  intro y hy
  refine ⟨_, ?_, hinv y (hsub₀ hy)⟩
  have := (hmem y hy).1
  simp only [Set.mem_Ioi]; linarith

theorem Xf_mem_Icc {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {y : ℝ}
    (hy : y ∈ Set.Icc (1 / 2 : ℝ) 1) : Xf Q u y ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2) := by
  obtain ⟨-, -, -, -, -, -, h⟩ := branch_spec hu
  exact h y hy

theorem Xf_spec {Q : ℤ[X]} {u : ℕ} {y : ℝ} (hy : y ∈ Vset Q u) :
    Xf Q u y ∈ Set.Ioi (u : ℝ) ∧ aeval (Xf Q u y) Q = (aQ Q u : ℝ) + (cQ Q u : ℝ) * y :=
  brInv_spec hy

theorem aeval_derivative_ne_zero {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {x : ℝ}
    (hx : x ∈ Set.Ioi (u : ℝ)) : aeval x (derivative Q) ≠ 0 := by
  intro h; have := hu x (le_of_lt hx); rw [h] at this; norm_num at this

theorem hasDerivAt_Xf {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {y : ℝ} (hy : y ∈ Vset Q u) :
    HasDerivAt (Xf Q u) ((cQ Q u : ℝ) / aeval (Xf Q u y) (derivative Q)) y := by
  set w := (aQ Q u : ℝ) + (cQ Q u : ℝ) * y
  have hW : IsOpen ((fun x : ℝ => aeval x Q) '' Set.Ioi (u : ℝ)) := isOpen_image_Ioi hu
  have hev : ∀ᶠ v in 𝓝 w, brInv Q u v ∈ Set.Ioi (u : ℝ) ∧ aeval (brInv Q u v) Q = v := by
    filter_upwards [hW.mem_nhds hy] with v hv using brInv_spec hv
  have hb : HasDerivAt (brInv Q u) (aeval (brInv Q u w) (derivative Q))⁻¹ w :=
    HasDerivAt.of_local_left_inverse (analyticAt_brInv hu hev).continuousAt
      (Polynomial.hasDerivAt_aeval Q _) (aeval_derivative_ne_zero hu (Xf_spec hy).1)
      (hev.mono fun v hv => hv.2)
  have haff : HasDerivAt (fun y : ℝ => (aQ Q u : ℝ) + (cQ Q u : ℝ) * y) (cQ Q u : ℝ) y := by
    simpa using ((hasDerivAt_id y).const_mul (cQ Q u : ℝ)).const_add (aQ Q u : ℝ)
  have := HasDerivAt.comp (h₂ := brInv Q u) (h := fun y : ℝ => (aQ Q u : ℝ) + (cQ Q u : ℝ) * y)
    y hb haff
  exact this.congr_deriv (by rw [div_eq_inv_mul]; rfl)

theorem hasDerivAt_GP {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) (P : ℤ[X]) {y : ℝ}
    (hy : y ∈ Vset Q u) :
    HasDerivAt (GP Q u P) ((cQ Q u : ℝ) * aeval (Xf Q u y) (derivative P) /
      aeval (Xf Q u y) (derivative Q)) y := by
  rw [GP_eq_Xf]
  have := (Polynomial.hasDerivAt_aeval P (Xf Q u y)).comp y (hasDerivAt_Xf hu hy)
  exact this.congr_deriv (by ring)

theorem deriv2_GP_eq {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) (P : ℤ[X]) {y : ℝ}
    (hy : y ∈ Vset Q u) :
    deriv (deriv (GP Q u P)) y = (cQ Q u : ℝ) ^ 2 * aeval (Xf Q u y) (wPoly P Q) /
      aeval (Xf Q u y) (derivative Q) ^ 3 := by
  set c := (cQ Q u : ℝ)
  have hd : deriv (GP Q u P) =ᶠ[𝓝 y] fun y => c * aeval (Xf Q u y) (derivative P) /
      aeval (Xf Q u y) (derivative Q) := by
    filter_upwards [(isOpen_Vset hu).mem_nhds hy] with v hv using (hasDerivAt_GP hu P hv).deriv
  rw [hd.deriv_eq]
  have hX := hasDerivAt_Xf hu hy
  have h1 := ((Polynomial.hasDerivAt_aeval (derivative P) (Xf Q u y)).comp y hX).const_mul c
  have h2 := (Polynomial.hasDerivAt_aeval (derivative Q) (Xf Q u y)).comp y hX
  have hne := aeval_derivative_ne_zero hu (Xf_spec hy).1
  have := h1.div h2 hne
  have e : deriv (fun y => c * aeval (Xf Q u y) (derivative P) /
      aeval (Xf Q u y) (derivative Q)) y = _ := this.deriv
  rw [e]
  simp only [Function.comp]
  simp only [wPoly, map_sub, map_mul]
  field_simp
  ring

/-! Coefficient-mass bounds for `P`, `P'`, `P''` on `|x| ≤ B`. -/

/-- Truncated coefficient mass `Σ_{j<N} |p_j|`. -/
noncomputable def cs (p : ℤ[X]) (N : ℕ) : ℝ := ∑ j ∈ Finset.range N, |(p.coeff j : ℝ)|

theorem cs_nonneg (p : ℤ[X]) (N : ℕ) : 0 ≤ cs p N :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_aeval_le_cs (p : ℤ[X]) {N : ℕ} (hN : p.natDegree < N) {x B : ℝ} (hB : 1 ≤ B)
    (hx : |x| ≤ B) : |aeval x p| ≤ cs p N * B ^ (N - 1) := by
  rw [aeval_eq_sum_range' hN, cs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj' : j ≤ N - 1 := by have := Finset.mem_range.1 hj; omega
  rw [zsmul_eq_mul, abs_mul, abs_pow]
  gcongr
  calc |x| ^ j ≤ B ^ j := pow_le_pow_left₀ (abs_nonneg x) hx j
    _ ≤ B ^ (N - 1) := pow_le_pow_right₀ hB hj'

theorem cs_derivative_le (p : ℤ[X]) (N : ℕ) :
    cs (derivative p) N ≤ N * cs p (N + 1) := by
  rw [cs, cs, Finset.sum_range_succ', mul_add, Finset.mul_sum]
  have h0 : 0 ≤ (N : ℝ) * |(p.coeff 0 : ℝ)| := by positivity
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun j hj => ?_) h0
  rw [coeff_derivative]
  push_cast
  rw [abs_mul, mul_comm]
  have : |((j : ℝ) + 1)| ≤ N := by
    rw [abs_of_nonneg (by positivity)]
    have := Finset.mem_range.1 hj; exact_mod_cast this
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

theorem cs_eq_hgt (p : ℤ[X]) : cs p (p.natDegree + 1) = hgt p := by
  rw [cs, hgt_cast]

theorem cs_succ_of_lt (p : ℤ[X]) {N : ℕ} (h : p.natDegree < N) : cs p (N + 1) = cs p N := by
  rw [cs, cs, Finset.sum_range_succ, coeff_eq_zero_of_natDegree_lt h]; simp

theorem succ_sq_le_four_pow (d : ℕ) : ((d : ℝ) + 1) ^ 2 ≤ 4 ^ d := by
  have h : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  have : ((d + 1) ^ 2 : ℕ) ≤ 4 ^ d := by
    calc (d + 1) ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left h 2
      _ = 4 ^ d := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  exact_mod_cast this

theorem abs_aeval_deriv_le (P : ℤ[X]) {x B : ℝ} (hB : 1 ≤ B) (hx : |x| ≤ B) :
    |aeval x P| ≤ hgt P * B ^ P.natDegree ∧
    |aeval x (derivative P)| ≤ ((P.natDegree : ℝ) + 1) * hgt P * B ^ P.natDegree ∧
    |aeval x (derivative (derivative P))| ≤
      ((P.natDegree : ℝ) + 1) ^ 2 * hgt P * B ^ P.natDegree := by
  set d := P.natDegree
  have h1 : (derivative P).natDegree < d + 1 :=
    lt_of_le_of_lt (natDegree_derivative_le P) (by omega)
  have h2 : (derivative (derivative P)).natDegree < d + 1 :=
    lt_of_le_of_lt (natDegree_derivative_le _) (by omega)
  have hc1 : cs (derivative P) (d + 1) ≤ ((d : ℝ) + 1) * hgt P := by
    have := cs_derivative_le P (d + 1)
    rw [cs_succ_of_lt P (by omega), cs_eq_hgt] at this; push_cast at this; exact this
  have hc2 : cs (derivative (derivative P)) (d + 1) ≤ ((d : ℝ) + 1) ^ 2 * hgt P := by
    have := cs_derivative_le (derivative P) (d + 1)
    rw [cs_succ_of_lt _ h1] at this; push_cast at this
    calc _ ≤ _ := this
      _ ≤ ((d : ℝ) + 1) * (((d : ℝ) + 1) * hgt P) := by gcongr
      _ = _ := by ring
  have hBd : 0 ≤ B ^ d := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have := abs_aeval_le_cs P (Nat.lt_succ_self d) hB hx
    rw [cs_eq_hgt] at this; simpa using this
  · have := abs_aeval_le_cs _ h1 hB hx
    rw [Nat.add_sub_cancel] at this
    exact this.trans (by gcongr)
  · have := abs_aeval_le_cs _ h2 hB hx
    rw [Nat.add_sub_cancel] at this
    exact this.trans (by gcongr)

/-- Clamp to the branch window `[u+1, u+2]`. -/
noncomputable def clampW (u : ℕ) (σ : ℝ) : ℝ := max ((u : ℝ) + 1) (min σ ((u : ℝ) + 2))

theorem clampW_mem (u : ℕ) (σ : ℝ) : clampW u σ ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2) :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem abs_sub_clampW_le (u : ℕ) {x : ℝ} (hx : x ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2))
    (σ : ℝ) : |x - clampW u σ| ≤ |x - σ| := by
  unfold clampW
  rcases le_total σ ((u : ℝ) + 2) with h | h
  · rw [min_eq_left h]
    rcases le_total ((u : ℝ) + 1) σ with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h', abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith [hx.1])]
      linarith
  · rw [min_eq_right h, max_eq_right (by linarith), abs_of_nonpos (by linarith [hx.2]),
      abs_of_nonpos (by linarith [hx.2])]
    linarith

/-- **Lower bound for `G_P''` by a product of distances, explicit in the zero count.**

Confidence 88%.  English proof: on the window, `G_P''(y) = c² W_P(x)/Q'(x)³` with
`x = brInv(a + c y) ∈ [u+1, u+2]` (implicit differentiation, `branch_spec`).  Write
`W_P = ℓ Π (X − ρ_i)` over `ℂ`, `|ℓ| ≥ 1`, `N = deg W_P` roots.  For real `x`,
`|x − ρ| ≥ |x − Re ρ|`.  The map `y ↦ x` is monotone with `|dx/dy| = |c|/|Q'(x)| ≥ 1/M`,
`M = 1 + max_{[u+1,u+2]} |Q'|`, so with `τ(σ)` the `y`-preimage of `σ` when `σ ∈ [u+1, u+2]`
and the nearer window endpoint otherwise, `|x − σ| ≥ |y − τ(σ)|/M`.  So
`|G_P''(y)| ≥ c² M^{-3} M^{-N} Π |y − τ_i| ≥ M^{-(N+3)} Π |y − τ_i|` (`c² ≥ 1`).  `L = M`
depends only on `Q` and `u`. -/
theorem deriv2_GP_lower {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ P : ℤ[X], wPoly P Q ≠ 0 →
      ∃ Z : Multiset ℝ, Z.card ≤ (wPoly P Q).natDegree ∧ ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
        ((L : ℝ) ^ ((wPoly P Q).natDegree + 3))⁻¹ * (Z.map fun z => |t - z|).prod ≤
          |deriv (deriv (GP Q u P)) t| := by
  set B : ℝ := (u : ℝ) + 2 with hBdef
  have hB : 1 ≤ B := by rw [hBdef]; linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
  set a : ℝ := (aQ Q u : ℝ)
  set c : ℝ := (cQ Q u : ℝ) with hcdef
  have hc1 : 1 ≤ |c| := by
    rw [hcdef, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs (branch_spec hu).1
  have hc0 : c ≠ 0 := fun h => by rw [h, abs_zero] at hc1; norm_num at hc1
  set M : ℝ := ((Q.natDegree : ℝ) + 1) * hgt Q * B ^ Q.natDegree + 1 with hM
  have hM1 : 1 ≤ M := by
    have : (0:ℝ) ≤ ((Q.natDegree : ℝ) + 1) * hgt Q * B ^ Q.natDegree := by positivity
    rw [hM]; linarith
  have hM0 : 0 < M := by linarith
  have hWin : ∀ x ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2), |aeval x (derivative Q)| ≤ M := by
    intro x hx
    have hxB : |x| ≤ B := by
      rw [abs_of_nonneg (by linarith [hx.1, (Nat.cast_nonneg u : (0 : ℝ) ≤ u)])]; exact hx.2
    have := (abs_aeval_deriv_le Q hB hxB).2.1
    rw [hM]; linarith
  have hLip : ∀ x ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2), ∀ x' ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2),
      |aeval x Q - aeval x' Q| ≤ M * |x - x'| := by
    intro x hx x' hx'
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x : ℝ => aeval x Q)
      (fun z _ => (Polynomial.hasDerivAt_aeval Q z).differentiableAt)
      (fun z hz => by rw [(Polynomial.hasDerivAt_aeval Q z).deriv]; exact hWin z hz)
      (convex_Icc _ _) hx' hx
    simpa [Real.norm_eq_abs] using this
  set τ : ℝ → ℝ := fun σ => (aeval (clampW u σ) Q - a) / c with hτ
  have hτ_le : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, |t - τ σ| ≤ M * |Xf Q u t - σ| := by
    intro t ht σ
    have hx := Xf_mem_Icc hu ht
    have hQx : aeval (Xf Q u t) Q = a + c * t := (Xf_spec (window_sub_Vset hu ht)).2
    have e : t - τ σ = (aeval (Xf Q u t) Q - aeval (clampW u σ) Q) / c := by
      rw [hτ, hQx]; field_simp; ring
    rw [e, abs_div]
    calc |aeval (Xf Q u t) Q - aeval (clampW u σ) Q| / |c|
        ≤ |aeval (Xf Q u t) Q - aeval (clampW u σ) Q| :=
          div_le_self (abs_nonneg _) hc1
      _ ≤ M * |Xf Q u t - clampW u σ| := hLip _ hx _ (clampW_mem u σ)
      _ ≤ M * |Xf Q u t - σ| := mul_le_mul_of_nonneg_left (abs_sub_clampW_le u hx σ) hM0.le
  refine ⟨⌈M⌉₊, ?_, fun P hW => ?_⟩
  · exact_mod_cast (Nat.one_le_cast.1 (hM1.trans (Nat.le_ceil _)) : 1 ≤ ⌈M⌉₊)
  set W := wPoly P Q
  set N := W.natDegree
  set Wc : ℂ[X] := W.map (algebraMap ℤ ℂ) with hWc
  have hWcd : Wc.natDegree = N := by
    rw [hWc, natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℂ))]
  have hWclc : Wc.leadingCoeff = ((W.leadingCoeff : ℤ) : ℂ) := by
    rw [hWc, leadingCoeff_map_of_injective (RingHom.injective_int (algebraMap ℤ ℂ))]; rfl
  have hlc : (1 : ℝ) ≤ ‖((W.leadingCoeff : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.2 hW)
  refine ⟨Wc.roots.map fun ρ => τ ρ.re, ?_, fun t ht => ?_⟩
  · rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hWcd]
  set x := Xf Q u t
  have hx := Xf_mem_Icc hu ht
  have hQl : 1 ≤ |aeval x (derivative Q)| := hu _ (by linarith [hx.1])
  have hQM := hWin x hx
  have hWe : ((aeval x W : ℝ) : ℂ) = ((W.leadingCoeff : ℤ) : ℂ) *
      (Wc.roots.map fun ρ => (x : ℂ) - ρ).prod := by
    have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := Wc))
    have : ((aeval x W : ℝ) : ℂ) = Wc.eval (x : ℂ) := by
      rw [hWc, eval_map_algebraMap, show (x : ℂ) = algebraMap ℝ ℂ x from rfl,
        aeval_algebraMap_apply]; rfl
    rw [this]
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, hWclc, Multiset.map_map]
    simp
  have hWabs : |aeval x W| = ‖((W.leadingCoeff : ℤ) : ℂ)‖ *
      (Wc.roots.map fun ρ => ‖(x : ℂ) - ρ‖).prod := by
    have := congrArg (fun z : ℂ => ‖z‖) hWe
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul] at this
    rw [this]; congr 1
    have := map_multiset_prod (normHom (α := ℂ)) (Wc.roots.map fun ρ => (x : ℂ) - ρ)
    simpa [Multiset.map_map, Function.comp_def] using this
  have hfac : ∀ ρ ∈ Wc.roots, M⁻¹ * |t - τ ρ.re| ≤ ‖(x : ℂ) - ρ‖ := by
    intro ρ _
    have h := hτ_le t ht ρ.re
    have hre : |x - ρ.re| ≤ ‖(x : ℂ) - ρ‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) - ρ); simpa using this
    rw [inv_mul_le_iff₀ hM0]; nlinarith
  have hprod := Multiset.prod_map_le_prod_map₀ _ _ (fun ρ _ => by positivity) hfac
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree, hWcd] at hprod
  set PP := (Wc.roots.map fun ρ => |t - τ ρ.re|).prod with hPP
  have hPP0 : 0 ≤ PP := Multiset.prod_nonneg fun z hz => by
    obtain ⟨_, _, rfl⟩ := Multiset.mem_map.1 hz; exact abs_nonneg _
  rw [Multiset.map_map]
  change _ * PP ≤ _
  have hRpos : 0 ≤ (Wc.roots.map fun ρ => ‖(x : ℂ) - ρ‖).prod := Multiset.prod_nonneg fun z hz => by
    obtain ⟨_, _, rfl⟩ := Multiset.mem_map.1 hz; exact norm_nonneg _
  have hML : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : 1 ≤ c ^ 2 := by rw [← sq_abs]; nlinarith
  have hQ3 : |aeval x (derivative Q)| ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hQM 3
  have hQ3p : 0 < |aeval x (derivative Q)| ^ 3 := by positivity
  rw [deriv2_GP_eq hu P (window_sub_Vset hu ht), abs_div, abs_mul, abs_pow, abs_pow, sq_abs,
    le_div_iff₀ hQ3p]
  have hWlow : (M ^ N)⁻¹ * PP ≤ |aeval x W| := by
    rw [hWabs]
    calc (M ^ N)⁻¹ * PP = M⁻¹ ^ N * PP := by rw [inv_pow]
      _ ≤ (Wc.roots.map fun ρ => ‖(x : ℂ) - ρ‖).prod := hprod
      _ ≤ _ := le_mul_of_one_le_left hRpos hlc
  calc ((⌈M⌉₊ : ℝ) ^ (N + 3))⁻¹ * PP * |aeval x (derivative Q)| ^ 3
      ≤ (M ^ (N + 3))⁻¹ * PP * M ^ 3 := by
        gcongr
      _ = (M ^ N)⁻¹ * PP := by rw [pow_add]; field_simp
      _ ≤ |aeval x W| := hWlow
      _ ≤ c ^ 2 * |aeval x W| := le_mul_of_one_le_left (abs_nonneg _) hc2


/-- **Sibling identity: `G_P` is rational affine near the window when `P ∈ span(1, Q)`.**
Proved from `branch_spec` (`Q(brInv w) = w` on `U`) and `aeval_eq_of_affineIn`. -/
theorem GP_eq_of_affineIn {Q P : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {α β : ℚ}
    (h : P.map (Int.castRingHom ℚ) = C α * Q.map (Int.castRingHom ℚ) + C β) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (1 / 2 : ℝ) 1 ⊆ U ∧ ∀ y ∈ U,
      GP Q u P y = (α : ℝ) * ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y) + β := by
  obtain ⟨-, -, U, hU, hsub, hinv, -⟩ := branch_spec hu
  refine ⟨U, hU, hsub, fun y hy => ?_⟩
  rw [GP, aeval_eq_of_affineIn h, hinv y hy]

/-- **Known-false sibling: the cut cannot run on `P ∈ span_ℚ(1, Q)`.**  `G_P` is affine on a
neighbourhood of the window, so `G_P'' ≡ 0` there and no lower bound `c Π |t − z|` holds
(`not_deriv2_lower_of_deriv2_eq_zero`).  Proved from `GP_eq_of_affineIn`. -/
theorem not_deriv2_lower_GP_of_affineIn {Q P : ℤ[X]} {u : ℕ} (hu : IsBranch Q u)
    (h : AffineIn P Q) {c : ℝ} (hc : 0 < c) (Z : Multiset ℝ) :
    ¬ ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c * (Z.map fun z => |t - z|).prod ≤
      |deriv (deriv (GP Q u P)) t| := by
  obtain ⟨α, β, hαβ⟩ := h
  obtain ⟨U, hU, hsub, hU'⟩ := GP_eq_of_affineIn hu hαβ
  refine not_deriv2_lower_of_deriv2_eq_zero _ (fun t ht => ?_) hc Z
  have hd : deriv (GP Q u P) =ᶠ[𝓝 t] fun _ => (α : ℝ) * (cQ Q u : ℝ) := by
    filter_upwards [hU.mem_nhds (hsub ht)] with s hs
    have hev : GP Q u P =ᶠ[𝓝 s] fun y => (α : ℝ) * ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y) + β := by
      filter_upwards [hU.mem_nhds hs] with y hy using hU' y hy
    rw [hev.deriv_eq]
    have : HasDerivAt (fun y => (α : ℝ) * ((aQ Q u : ℝ) + (cQ Q u : ℝ) * y) + β)
        ((α : ℝ) * (cQ Q u : ℝ)) s := by
      have := ((hasDerivAt_id s).const_mul (cQ Q u : ℝ)).const_add (aQ Q u : ℝ)
      simpa using (this.const_mul (α : ℝ)).add_const (β : ℝ)
    exact this.deriv
  rw [hd.deriv_eq, deriv_const]

set_option maxHeartbeats 1000000 in
/-- **Window bounds for `G_P`, `G_P'`, `G_P''` by the height.**

Confidence 90%.  English proof: `x ∈ [u+1, u+2]`, so `|P(x)| ≤ hgt P (u+2)^{deg P}`.
`G_P' = c P'(x)/Q'(x)` and `G_P'' = c²(P''Q' − P'Q'')(x)/Q'(x)³` with `|Q'(x)| ≥ 1`;
`|P^{(j)}(x)| ≤ (deg P)^j hgt P (u+2)^{deg P} ≤ 4^{deg P} hgt P (u+2)^{deg P}` for `j ≤ 2`,
and `|Q'|, |Q''|, |c|` are bounded on the window by a constant depending on `Q, u` only;
absorb everything into `L^{deg P + 1}` with `L ≥ 4(u+2) · (1 + |c|)² · (1 + max|Q'| + max|Q''|)`. -/
theorem GP_bounds {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ P : ℤ[X], ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      |GP Q u P t| ≤ (hgt P : ℝ) * ((u : ℝ) + 2) ^ P.natDegree ∧
      |deriv (GP Q u P) t| ≤ (L : ℝ) ^ (P.natDegree + 1) * hgt P ∧
      |deriv (deriv (GP Q u P)) t| ≤ (L : ℝ) ^ (P.natDegree + 1) * hgt P := by
  set B : ℝ := (u : ℝ) + 2 with hBdef
  have hB : 1 ≤ B := by rw [hBdef]; linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
  set c : ℝ := (cQ Q u : ℝ) with hcdef
  have hc1 : 1 ≤ |c| := by
    rw [hcdef, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs (branch_spec hu).1
  have hcc : |c| ≤ c ^ 2 := by rw [← sq_abs]; nlinarith
  have hc2 : 1 ≤ c ^ 2 := hc1.trans hcc
  set M : ℝ := ((Q.natDegree : ℝ) + 1) ^ 2 * hgt Q * B ^ Q.natDegree + 1 with hM
  have hM1 : 1 ≤ M := by
    have : (0:ℝ) ≤ ((Q.natDegree : ℝ) + 1) ^ 2 * hgt Q * B ^ Q.natDegree := by positivity
    rw [hM]; linarith
  refine ⟨⌈8 * c ^ 2 * M * B⌉₊, ?_, fun P t ht => ?_⟩
  · have : (1 : ℝ) ≤ 8 * c ^ 2 * M * B := by
      have h1 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc2 hM1) hB
      linarith
    exact_mod_cast (Nat.one_le_cast.1 (this.trans (Nat.le_ceil _)) : 1 ≤ ⌈8 * c ^ 2 * M * B⌉₊)
  set L : ℝ := ((⌈8 * c ^ 2 * M * B⌉₊ : ℕ) : ℝ)
  set d := P.natDegree
  have hL : 8 * c ^ 2 * M * B ≤ L := Nat.le_ceil _
  have hx := Xf_mem_Icc hu ht
  have hxB : |Xf Q u t| ≤ B := by
    rw [abs_of_nonneg (by linarith [hx.1, (Nat.cast_nonneg u : (0 : ℝ) ≤ u)])]; exact hx.2
  have hV := window_sub_Vset hu ht
  obtain ⟨hP0, hP1, hP2⟩ := abs_aeval_deriv_le P hB hxB
  obtain ⟨-, hQ1, hQ2⟩ := abs_aeval_deriv_le Q hB hxB
  have hQ1' : |aeval (Xf Q u t) (derivative Q)| ≤ M := by
    have : ((Q.natDegree : ℝ) + 1) * hgt Q * B ^ Q.natDegree ≤
        ((Q.natDegree : ℝ) + 1) ^ 2 * hgt Q * B ^ Q.natDegree := by
      gcongr; nlinarith
    rw [hM]; linarith
  have hQ2' : |aeval (Xf Q u t) (derivative (derivative Q))| ≤ M := by rw [hM]; linarith
  have hQl : 1 ≤ |aeval (Xf Q u t) (derivative Q)| := hu _ (by linarith [hx.1])
  have hH : (0 : ℝ) ≤ hgt P := Nat.cast_nonneg _
  have hBd : 0 ≤ B ^ d := by positivity
  set K := 2 * c ^ 2 * M * ((d : ℝ) + 1) ^ 2 * B ^ d * hgt P with hK
  have hKL : K ≤ L ^ (d + 1) * hgt P := by
    have h4 := succ_sq_le_four_pow d
    have hL4 : 4 * B ≤ L := by
      have h1 : 1 ≤ c ^ 2 * M := one_le_mul_of_one_le_of_one_le hc2 hM1
      have : 4 * B ≤ 8 * c ^ 2 * M * B := by nlinarith
      linarith
    have hLd : (4 * B) ^ d ≤ L ^ d := pow_le_pow_left₀ (by positivity) hL4 d
    have : 2 * c ^ 2 * M * ((d : ℝ) + 1) ^ 2 * B ^ d ≤ L ^ (d + 1) := by
      rw [pow_succ]
      calc 2 * c ^ 2 * M * ((d : ℝ) + 1) ^ 2 * B ^ d ≤ 2 * c ^ 2 * M * 4 ^ d * B ^ d := by gcongr
        _ ≤ 8 * c ^ 2 * M * B * (4 * B) ^ d := by
            rw [mul_pow]; have : 0 ≤ c ^ 2 * M * 4 ^ d * B ^ d := by positivity
            nlinarith
        _ ≤ L * L ^ d := by
            exact mul_le_mul hL hLd (by positivity) (by positivity)
        _ = L ^ d * L := by ring
    rw [hK]; gcongr
  refine ⟨?_, ?_, ?_⟩
  · rw [GP_eq_Xf]; exact hP0
  · rw [(hasDerivAt_GP hu P hV).deriv, abs_div, abs_mul]
    refine (div_le_of_le_mul₀ (by positivity) (by positivity) ?_).trans hKL
    calc |c| * |aeval (Xf Q u t) (derivative P)| ≤ c ^ 2 * (((d : ℝ) + 1) * hgt P * B ^ d) := by
          gcongr
      _ ≤ K * 1 := by
          rw [hK, mul_one]
          have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
          have : ((d : ℝ) + 1) ≤ 2 * M * ((d : ℝ) + 1) ^ 2 := by
            have := one_le_mul_of_one_le_of_one_le hM1 hd1
            nlinarith
          have h0 : 0 ≤ c ^ 2 * hgt P * B ^ d := by positivity
          calc c ^ 2 * (((d : ℝ) + 1) * hgt P * B ^ d) = (c ^ 2 * hgt P * B ^ d) * ((d : ℝ) + 1) := by
                ring
            _ ≤ (c ^ 2 * hgt P * B ^ d) * (2 * M * ((d : ℝ) + 1) ^ 2) :=
                mul_le_mul_of_nonneg_left this h0
            _ = _ := by ring
      _ ≤ K * |aeval (Xf Q u t) (derivative Q)| := by gcongr
  · rw [deriv2_GP_eq hu P hV, abs_div, abs_mul, abs_pow, abs_pow, sq_abs]
    refine (div_le_of_le_mul₀ (by positivity) (by positivity) ?_).trans hKL
    have hW : |aeval (Xf Q u t) (wPoly P Q)| ≤
        ((d : ℝ) + 1) ^ 2 * hgt P * B ^ d * M + ((d : ℝ) + 1) * hgt P * B ^ d * M := by
      simp only [wPoly, map_sub, map_mul]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul hP2 hQ1' (abs_nonneg _) (by positivity)
      · exact mul_le_mul hP1 hQ2' (abs_nonneg _) (by positivity)
    calc c ^ 2 * |aeval (Xf Q u t) (wPoly P Q)| ≤
        c ^ 2 * (((d : ℝ) + 1) ^ 2 * hgt P * B ^ d * M + ((d : ℝ) + 1) * hgt P * B ^ d * M) := by
          gcongr
      _ ≤ K * 1 := by
          rw [hK, mul_one]
          have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
          have : ((d : ℝ) + 1) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith
          have h0 : 0 ≤ c ^ 2 * hgt P * B ^ d * M := by positivity
          calc c ^ 2 * (((d : ℝ) + 1) ^ 2 * hgt P * B ^ d * M + ((d : ℝ) + 1) * hgt P * B ^ d * M)
              = (c ^ 2 * hgt P * B ^ d * M) * (((d : ℝ) + 1) ^ 2 + ((d : ℝ) + 1)) := by ring
            _ ≤ (c ^ 2 * hgt P * B ^ d * M) * (2 * ((d : ℝ) + 1) ^ 2) :=
                mul_le_mul_of_nonneg_left (by linarith) h0
            _ = _ := by ring
      _ ≤ K * |aeval (Xf Q u t) (derivative Q)| ^ 3 := by
          gcongr; exact one_le_pow₀ hQl


set_option maxHeartbeats 1000000 in
/-- **The cylinder cut, uniform in the zero count.**  `pushFourier_le_of_deriv2_lower` with its
constants made explicit in `N` (new lemma; the existing one is untouched).

Confidence 85%.  English proof: rerun `pushFourier_le_of_deriv2_lower`'s proof keeping track of
`N`.  With BB's `C, η, κ` (`pushFourier_le_of_deriv2_ge`), the depth exponent is
`ε = η / (4κ(N+2))`, the output exponent `δ = min(η/2, ε/2) ≥ δ₀/(N+1)` for
`δ₀ = min(η/2, η/(16κ))`, and the constant `K ≥ max(2⌈κ⌉, C 4^{κ+2} + 12N + 1)` is at most
`K₀ (N + 1)` for `K₀ = max(2⌈κ⌉, ⌈C 4^{κ+2}⌉ + 13)`.  Enlarging the exponent of `(1 + c⁻¹)` from
`2⌈κ⌉` to `K₀(N+1)` only weakens the bound. -/
theorem pushFourier_le_of_deriv2_lower_unif (hBB : BakerBanajiUniformQuarterCantor) :
    ∃ K₀ : ℕ, 0 < K₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ N : ℕ,
      ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 F U →
      ∀ c A : ℝ, 0 < c →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A) →
      ∀ Z : Multiset ℝ, Z.card ≤ N →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c * (Z.map fun z => |t - z|).prod ≤ |deriv (deriv F) t|) →
      ∀ ξ : ℝ, ξ ≠ 0 → ‖pushFourier F ξ‖ ≤
        (K₀ * (N + 1) : ℝ) * (1 + A) * (1 + c⁻¹) ^ (K₀ * (N + 1)) * |ξ| ^ (-(δ₀ / (N + 1))) := by
  obtain ⟨C, η, κ, hC, hη, hκ, hB⟩ := pushFourier_le_of_deriv2_ge hBB
  set D : ℝ := 2 * C * (2 + 4 ^ κ) with hD
  set K₀ : ℕ := 13 + ⌈D⌉₊ + 2 * ⌈κ⌉₊ with hK₀
  set δ₀ : ℝ := min 1 (min (η / 2) (η / (16 * κ))) with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  refine ⟨K₀, by omega, δ₀, hδ₀0, min_le_left _ _,
    fun N F U hU hsub hF c A hc hA1 hA2 Z hZ hlow ξ hξ => ?_⟩
  set ε : ℝ := η / (4 * κ * (N + 2)) with hεdef
  have hε : 0 < ε := by positivity
  have hεκ : ε * (N + 2) * κ = η / 4 := by rw [hεdef]; field_simp
  set δ : ℝ := δ₀ / (N + 1) with hδdef
  have hN1 : (1 : ℝ) ≤ N + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hδ : 0 < δ := by positivity
  have hδε : δ ≤ ε / 2 := by
    rw [hδdef, hεdef, div_le_iff₀ (by linarith)]
    have h1 : δ₀ ≤ η / (16 * κ) := (min_le_right _ _).trans (min_le_right _ _)
    calc δ₀ ≤ η / (16 * κ) := h1
      _ ≤ η / (4 * κ * (N + 2)) / 2 * (N + 1) := by
          rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have : (0 : ℝ) ≤ η * κ := by positivity
          nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hδη : δ ≤ η / 2 := by
    have h1 : δ₀ ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
    rw [hδdef, div_le_iff₀ (by linarith)]
    nlinarith
  set K : ℕ := K₀ * (N + 1) with hK
  set K : ℕ := K₀ * (N + 1) with hK
  suffices hmain : ‖pushFourier F ξ‖ ≤ K * (1 + A) * (1 + c⁻¹) ^ K * |ξ| ^ (-δ) by
    rw [hK, hδdef] at hmain; push_cast at hmain; exact hmain
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA1 1 ⟨by norm_num, le_rfl⟩)
  set X := |ξ| with hXdef
  have hX0 : 0 < X := abs_pos.2 hξ
  have hb1 : (1 : ℝ) ≤ 1 + c⁻¹ := by linarith [inv_pos.2 hc]
  set P : ℝ := (1 + c⁻¹) ^ ⌈κ⌉₊ with hP
  set Q : ℝ := (1 + c⁻¹) ^ K with hQ
  have hP1 : 1 ≤ P := one_le_pow₀ hb1
  have hQ1 : 1 ≤ Q := one_le_pow₀ hb1
  have hKκ : 2 * ⌈κ⌉₊ ≤ K := by rw [hK, hK₀]; nlinarith
  have hPQ : P * P ≤ Q := by
    rw [hP, hQ, ← pow_add]; exact pow_le_pow_right₀ hb1 (by omega)
  have hKr : (12 * N + D + 1 : ℝ) ≤ K := by
    have hKn : 13 * N + ⌈D⌉₊ + 1 ≤ K := by rw [hK, hK₀]; nlinarith
    have : (13 * N + ⌈D⌉₊ + 1 : ℝ) ≤ K := by exact_mod_cast hKn
    linarith [Nat.le_ceil D, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  rcases lt_or_ge X 1 with hX1 | hX1
  · have hu : 1 ≤ X ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hX0 hX1.le (by linarith)
    calc ‖pushFourier F ξ‖ ≤ 1 := norm_pushFourier_le_one F ξ
      _ ≤ (K : ℝ) * (1 + A) * Q * X ^ (-δ) := by
          have : (1 : ℝ) ≤ K := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
          have h1 : 1 ≤ (K : ℝ) * (1 + A) := by nlinarith
          have h2 : 1 ≤ (K : ℝ) * (1 + A) * Q := by nlinarith
          nlinarith
  obtain ⟨m, hm1, hm2⟩ := exists_pow4_bracket hX1 hε
  have hsplit := pushFourier_cut_split hB hC N F U hU hsub hF c A hc hA1 hA2 Z hZ hlow m ξ hξ
  set a : ℝ := c * (1 / 4 ^ m) ^ (N + 2) with ha
  have ha0 : 0 < a := by positivity
  set Y : ℝ := P * X ^ (η / 4) with hY
  have hXη4 : 1 ≤ X ^ (η / 4) := Real.one_le_rpow hX1 (by positivity)
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have haY : a ^ (-κ) ≤ Y := a_rpow_neg_le hX1 hκ hc N m hm1 hεκ
  have ha4 : (a / 4) ^ (-κ) = 4 ^ κ * a ^ (-κ) := by
    rw [Real.div_rpow ha0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    field_simp
  have h4κ : 0 < (4 : ℝ) ^ κ := by positivity
  have hbad := inv_two_pow_le hX1 m hm2
  have hu : X ^ (-(ε / 2)) ≤ X ^ (-δ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hw : X ^ (η / 4) * X ^ (η / 4) * X ^ (-η) ≤ X ^ (-δ) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hXη : 0 < X ^ (-η) := Real.rpow_pos_of_pos hX0 _
  have hXδ : 0 < X ^ (-δ) := Real.rpow_pos_of_pos hX0 _
  have hbad' : 6 * (N : ℝ) / 2 ^ m ≤ 12 * N * X ^ (-δ) := by
    rw [div_eq_mul_one_div]
    calc 6 * (N : ℝ) * (1 / 2 ^ m) ≤ 6 * N * (2 * X ^ (-(ε / 2))) := by gcongr
      _ ≤ 6 * N * (2 * X ^ (-δ)) := by gcongr
      _ = _ := by ring
  have hgood : C * (1 + 2 * A + (a / 4) ^ (-κ)) * (1 + a ^ (-κ)) * X ^ (-η) ≤
      D * (1 + A) * Q * X ^ (-δ) := by
    rw [ha4]
    have e1 : 1 + 2 * A + 4 ^ κ * a ^ (-κ) ≤ (2 + 4 ^ κ) * (1 + A) * Y := by
      have h1 : 4 ^ κ * a ^ (-κ) ≤ 4 ^ κ * Y := by gcongr
      have h2 : A ≤ A * Y := le_mul_of_one_le_right hA0 hY1
      have h3 : 0 ≤ 4 ^ κ * A * Y := by positivity
      have : (2 + 4 ^ κ) * (1 + A) * Y = 2 * Y + 2 * (A * Y) + 4 ^ κ * Y + 4 ^ κ * A * Y := by ring
      rw [this]; linarith
    have e2 : 1 + a ^ (-κ) ≤ 2 * Y := by linarith
    have hapos : 0 ≤ a ^ (-κ) := by positivity
    calc C * (1 + 2 * A + 4 ^ κ * a ^ (-κ)) * (1 + a ^ (-κ)) * X ^ (-η)
        ≤ C * ((2 + 4 ^ κ) * (1 + A) * Y) * (2 * Y) * X ^ (-η) := by gcongr
      _ = D * (1 + A) * (P * P) * (X ^ (η / 4) * X ^ (η / 4) * X ^ (-η)) := by
          rw [hD, hY]; ring
      _ ≤ D * (1 + A) * Q * X ^ (-δ) := by gcongr
  calc ‖pushFourier F ξ‖ ≤ _ := hsplit
    _ ≤ 12 * N * X ^ (-δ) + D * (1 + A) * Q * X ^ (-δ) := add_le_add hbad' hgood
    _ ≤ (12 * N + D + 1) * (1 + A) * Q * X ^ (-δ) := by
        have : 12 * (N : ℝ) * X ^ (-δ) ≤ 12 * N * ((1 + A) * Q) * X ^ (-δ) := by
          have : 1 ≤ (1 + A) * Q := by nlinarith
          have hN : (0 : ℝ) ≤ 12 * N := by positivity
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hN this) hXδ.le
        nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < 1 + A) (by linarith : (0 : ℝ) < Q)) hXδ]
    _ ≤ K * (1 + A) * Q * X ^ (-δ) := by gcongr

/-! ### The family over all `P ∉ span(1, Q)` -/

open Classical in
/-- Index `i` → the decoded polynomial when it lies off `span(1, Q)` (tested by `wPoly ≠ 0`),
and the default `X^{deg Q + 1}` otherwise. -/
noncomputable def polyOfCodeQ (Q : ℤ[X]) (i : ℕ) : ℤ[X] :=
  match (Encodable.decode i : Option (List ℤ)) with
  | some l => if wPoly (polyOfList l) Q ≠ 0 then polyOfList l else X ^ (Q.natDegree + 1)
  | none => X ^ (Q.natDegree + 1)

/-- The default is off the span: `deg X^{d+1} > deg(αQ + β)`.  Proved. -/
theorem not_affineIn_X_pow_succ (Q : ℤ[X]) : ¬ AffineIn (X ^ (Q.natDegree + 1)) Q := by
  rintro ⟨α, β, h⟩
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hdeg : (Q.map (Int.castRingHom ℚ)).natDegree = Q.natDegree :=
    natDegree_map_eq_of_injective hinj Q
  have hck := congrArg (fun r => r.coeff (Q.natDegree + 1)) h
  simp only [Polynomial.map_pow, map_X, coeff_X_pow_self, coeff_add, coeff_C_mul, coeff_C,
    if_neg (Nat.succ_ne_zero _), add_zero] at hck
  rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), mul_zero] at hck
  exact one_ne_zero hck

theorem exists_polyOfCodeQ_eq {Q : ℤ[X]} (hQ : 0 < Q.natDegree) {P : ℤ[X]}
    (hP : ¬ AffineIn P Q) : ∃ i, polyOfCodeQ Q i = P := by
  refine ⟨Encodable.encode ((List.range (P.natDegree + 1)).map P.coeff), ?_⟩
  simp only [polyOfCodeQ, Encodable.encodek, polyOfList_coeffs,
    if_pos (wPoly_ne_zero_of_not_affineIn hQ hP)]

theorem wPoly_polyOfCodeQ_ne_zero {Q : ℤ[X]} (hQ : 0 < Q.natDegree) (i : ℕ) :
    wPoly (polyOfCodeQ Q i) Q ≠ 0 := by
  classical
  unfold polyOfCodeQ
  split
  · split_ifs with h
    · exact h
    · exact wPoly_ne_zero_of_not_affineIn hQ (not_affineIn_X_pow_succ Q)
  · exact wPoly_ne_zero_of_not_affineIn hQ (not_affineIn_X_pow_succ Q)

/-- Normalising height: `|G_P| ≤ HQ − 1` on the window, `HQ ≥ 1`. -/
noncomputable def HQ (u : ℕ) (P : ℤ[X]) : ℕ := hgt P * (u + 2) ^ P.natDegree + 1

/-- The normalised family `(G_P(y) + H)/(2H) ∈ [0, 1]`, `P = polyOfCodeQ Q i`. -/
noncomputable def GPfam (Q : ℤ[X]) (u i : ℕ) (ω : ℕ → Bool) : ℝ :=
  (GP Q u (polyOfCodeQ Q i) (cantorReal ω) + HQ u (polyOfCodeQ Q i)) /
    (2 * HQ u (polyOfCodeQ Q i))

/-- Confidence 92%.  English proof: `GP Q u P` is continuous on `branch_spec`'s open `U`
(`analyticOnNhd_GP`), `cantorReal` is measurable with values in the window `⊆ U`
(`cantorReal_mem_window`), and a function continuous on an open set containing the range of a
measurable map composes measurably (restrict to the subtype, or replace `GP` by
`U.piecewise GP 0`, which agrees on the range). -/
theorem measurable_GPfam {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) (i : ℕ) :
    Measurable (GPfam Q u i) := by
  classical
  obtain ⟨U, hU, hsub, han⟩ := analyticOnNhd_GP hu
  set F := GP Q u (polyOfCodeQ Q i)
  have hGm : Measurable (U.piecewise F 0) :=
    ContinuousOn.measurable_piecewise (han _).continuousOn continuousOn_const hU.measurableSet
  have heq : (fun ω => F (cantorReal ω)) = fun ω => U.piecewise F 0 (cantorReal ω) := by
    funext ω; exact (Set.piecewise_eq_of_mem _ _ _ (hsub (cantorReal_mem_window ω))).symm
  have h2 : Measurable fun ω => F (cantorReal ω) := by
    rw [heq]; exact hGm.comp CantorSelfSimilar.measurable_cantorReal
  unfold GPfam
  exact (h2.add_const _).div_const _

/-! ### Refutation of the frozen `approx_GPfam`

A length-`D` prefix pins `y` only to `4^{-D}/6`, while `GPfam` has slope `c·P'(x)/(2 HQ·Q'(x))`,
which the normalisation `2 HQ` does not control: `Q'` can be small at the left window end while
`c = 2(Q(u+2) − Q(u+1))` is large.  For `Q = X + 512(X − 1)⁹`, `u = 0`, `P = X`, `D = 4`, the two
codes `0000 1111…` and `0000 0000…` share a prefix but their `GPfam` values differ by more than
`1/16`.  So no `A` can satisfy the bracket, whatever its computability. -/

section Refutation
open CantorSelfSimilar

theorem cantorReal_false : cantorReal (fun _ => false) = 1 / 2 := by
  have h : consB false (fun _ => false) = fun _ => false := by
    funext i; cases i <;> rfl
  have := cantorReal_consB false (fun _ => false)
  rw [h, psi] at this
  simp only [Bool.false_eq_true, if_false] at this
  linarith

theorem cantorReal_true : cantorReal (fun _ => true) = 2 / 3 := by
  have h : consB true (fun _ => true) = fun _ => true := by
    funext i; cases i <;> rfl
  have := cantorReal_consB true (fun _ => true)
  rw [h, psi] at this
  simp only [if_true] at this
  linarith

/-- The witness map: `Q = X + 512 (X − 1)⁹`, flat (`Q' = 1`) at the left window end `x = 1` but
with `Q(2) − Q(1) = 513`. -/
noncomputable def Qbad : ℤ[X] := X + C 512 * (X - 1) ^ 9

theorem aeval_Qbad (x : ℝ) : aeval x Qbad = x + 512 * (x - 1) ^ 9 := by
  simp [Qbad, map_ofNat]

theorem isBranch_Qbad : IsBranch Qbad 0 := by
  intro x _
  have : aeval x (derivative Qbad) = 1 + 4608 * (x - 1) ^ 8 := by
    simp [Qbad, derivative_mul, derivative_pow, map_ofNat]; ring
  rw [this, abs_of_nonneg (by positivity)]
  have : 0 ≤ (x - 1) ^ 8 := by positivity
  linarith

theorem natDegree_Qbad : Qbad.natDegree = 9 := by
  unfold Qbad
  have h1 : (X - 1 : ℤ[X]) = X - C 1 := by simp
  rw [h1, natDegree_add_eq_right_of_natDegree_lt]
  · rw [natDegree_C_mul (by norm_num), natDegree_pow, natDegree_X_sub_C]
  · rw [natDegree_C_mul (by norm_num), natDegree_pow, natDegree_X_sub_C, natDegree_X]; norm_num

theorem aQ_Qbad : aQ Qbad 0 = -512 := by
  simp [aQ, Qbad]

theorem cQ_Qbad : cQ Qbad 0 = 1026 := by
  simp [cQ, Qbad]

/-- The frozen statement of `approx_GPfam`, as a `Prop` (refuted by `not_approxGPfamClaim`). -/
def ApproxGPfamClaim : Prop :=
  ∀ (Q : ℤ[X]) (u : ℕ), IsBranch Q u → 0 < Q.natDegree →
    ∃ (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ) (A : ℕ → List Bool → ℝ),
      (Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
      (∀ i b m p, Ψ i b m p = ⌊A i p * (b : ℝ) ^ m⌋₊) ∧ (∀ i p, 0 ≤ A i p) ∧
      ∀ i ω D, A i (Derandomize.pre ω D) ≤ GPfam Q u i ω ∧
        GPfam Q u i ω ≤ A i (Derandomize.pre ω D) + (1 / 2 : ℝ) ^ D

theorem not_affineIn_X_Qbad : ¬ AffineIn X Qbad := by
  rintro ⟨α, β, h⟩
  have e := fun x : ℝ => aeval_eq_of_affineIn h x
  have e1 := e 1; have e2 := e 2; have e3 := e (3 / 2)
  simp only [aeval_X, aeval_Qbad] at e1 e2 e3
  norm_num at e1 e2 e3
  linarith

theorem not_approxGPfamClaim : ¬ ApproxGPfamClaim := by
  intro hC
  have hu := isBranch_Qbad
  have hQ : 0 < Qbad.natDegree := by rw [natDegree_Qbad]; norm_num
  obtain ⟨Ψ, A, -, -, -, hAG⟩ := hC Qbad 0 hu hQ
  obtain ⟨i, hi⟩ := exists_polyOfCodeQ_eq hQ not_affineIn_X_Qbad
  set ω' : ℕ → Bool := fun _ => false
  set ω : ℕ → Bool := consB false (consB false (consB false (consB false (fun _ => true))))
  have hpre : Derandomize.pre ω 4 = Derandomize.pre ω' 4 := rfl
  have hy' : cantorReal ω' = 1 / 2 := cantorReal_false
  have hy : cantorReal ω = 1 / 2 + 1 / 1536 := by
    simp only [ω, cantorReal_consB, cantorReal_true, psi]; norm_num
  have hfam : ∀ ν : ℕ → Bool, GPfam Qbad 0 i ν = (Xf Qbad 0 (cantorReal ν) + 3) / 6 := by
    intro ν
    have hH : HQ 0 X = 3 := by simp [HQ, hgt_X]
    simp only [GPfam, hi, hH, GP_eq_Xf, aeval_X]
    push_cast; ring
  have hwin : ∀ ν : ℕ → Bool, aeval (Xf Qbad 0 (cantorReal ν)) Qbad =
      -512 + 1026 * cantorReal ν := by
    intro ν
    have := (Xf_spec (window_sub_Vset hu (cantorReal_mem_window ν))).2
    rw [this, aQ_Qbad, cQ_Qbad]; push_cast; ring
  have hx' : Xf Qbad 0 (cantorReal ω') = 1 := by
    have hm := Xf_mem_Icc hu (cantorReal_mem_window ω')
    obtain ⟨-, hinj, -⟩ := branch_spec hu
    refine hinj hm ⟨by norm_num, by norm_num⟩ ?_
    simp only
    rw [hwin, hy', aeval_Qbad]; norm_num
  have hx : 11 / 8 < Xf Qbad 0 (cantorReal ω) := by
    have hm := Xf_mem_Icc hu (cantorReal_mem_window ω)
    have hQx := hwin ω
    rw [aeval_Qbad] at hQx
    by_contra hle
    push Not at hle
    have h0 : 0 ≤ Xf Qbad 0 (cantorReal ω) - 1 := by
      have := hm.1; push_cast at this; linarith
    have h9 : (Xf Qbad 0 (cantorReal ω) - 1) ^ 9 ≤ (3 / 8 : ℝ) ^ 9 :=
      pow_le_pow_left₀ h0 (by linarith) 9
    have h38 : (3 / 8 : ℝ) ^ 9 = 19683 / 134217728 := by norm_num
    rw [h38] at h9
    linarith
  have h1 := (hAG i ω' 4).1
  have h2 := (hAG i ω 4).2
  rw [hpre] at h2
  rw [hfam] at h1 h2
  rw [hx'] at h1
  norm_num at h1 h2
  linarith

end Refutation

/-- **Computable lower approximations of the normalised family with exact primitive recursive
floors** (the analogue of `approx_Gfam`, with bisection for `Q⁻¹`).

**FALSE** (`not_approxGPfamClaim`, proved): the slope of `GPfam` is not bounded by the prefix
resolution, so the frozen precision `2^{-D}` from a length-`D` prefix is unattainable.  The
English proof below overlooked that `A` may read only `D` coins.  Original confidence 85%.  English proof: a length-`D` prefix fixes `y` up to `4^{-D}/6`, and `|GPfam'| ≤
L^{deg P+1} hgt P / (2 HQ)` on the window (`GP_bounds`), so `GPfam` moves by at most
`2^{-D}/3 · 2^{-(deg P + 1) log₂ L}`-scaled amounts; take `D' = D + (deg P + 1)⌈log₂ L⌉ + 3`
coin digits instead.  Compute `x_lo = brInv(a + c y_lo)` to precision `2^{-M}` by `M` steps of
bisection on `[u+1, u+2]` using exact integer evaluation of `Q` at dyadics (valid by
monotonicity, `branch_spec`), then `P(x_lo)` exactly as a dyadic, with `|P'| ≤ L^{deg P+1} hgt P`
on the window controlling the error.  As in `approx_Gfam`, `A = max 0 (R − 2^{-D}/2)` is a
rational with primitive recursive numerator/denominator (all bounds primitive recursive in the
decoded coefficient list and the fixed data `Q, u, L`), which gives the two-sided bracket.
The validity test `wPoly (polyOfList l) Q ≠ 0` is a primitive recursive test on coefficient
lists. -/
theorem approx_GPfam {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) (hQ : 0 < Q.natDegree) :
    ∃ (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ) (A : ℕ → List Bool → ℝ),
      (Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
      (∀ i b m p, Ψ i b m p = ⌊A i p * (b : ℝ) ^ m⌋₊) ∧ (∀ i p, 0 ≤ A i p) ∧
      ∀ i ω D, A i (Derandomize.pre ω D) ≤ GPfam Q u i ω ∧
        GPfam Q u i ω ≤ A i (Derandomize.pre ω D) + (1 / 2 : ℝ) ^ D := by
  sorry

/-! Index bookkeeping for the family: primitive recursive height and degree bounds. -/

theorem length_le_encode : ∀ l : List ℤ, l.length ≤ Encodable.encode l
  | [] => by simp
  | a :: l => by
    have h2 := length_le_encode l
    have h3 := Nat.right_le_pair (Encodable.encode a) (Encodable.encode l)
    show _ ≤ Nat.pair (Encodable.encode a) (Encodable.encode l) + 1
    simp; omega

theorem natDegree_polyOfList_le (l : List ℤ) : (polyOfList l).natDegree ≤ l.length := by
  unfold polyOfList
  exact natDegree_sum_le_of_forall_le _ _ fun j hj =>
    (natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_range.1 hj).le

theorem hgt_X_pow (n : ℕ) : hgt (X ^ n : ℤ[X]) = 1 := by
  simp only [hgt, natDegree_X_pow, Finset.sum_range_succ, coeff_X_pow]
  rw [Finset.sum_eq_zero fun j hj => by rw [if_neg (Finset.mem_range.1 hj).ne]; rfl]; rfl

/-- Primitive recursive degree bound for the family. -/
def degBoundQ (Q : ℤ[X]) (i : ℕ) : ℕ := Encodable.encode (Encodable.decode (α := List ℤ) i) + Q.natDegree + 1

theorem primrec_degBoundQ (Q : ℤ[X]) : Primrec (degBoundQ Q) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.encdec (α := List ℤ)) (Primrec.const _))
    (Primrec.const 1)

theorem polyOfCodeQ_bounds (Q : ℤ[X]) (i : ℕ) :
    hgt (polyOfCodeQ Q i) ≤ hgtBound i ∧ (polyOfCodeQ Q i).natDegree ≤ degBoundQ Q i := by
  classical
  unfold polyOfCodeQ hgtBound degBoundQ
  rcases h : (Encodable.decode i : Option (List ℤ)) with _ | l
  · simp [hgt_X_pow]
  · simp only
    have : Encodable.encode (some l) = Encodable.encode l + 1 := rfl
    rw [this]
    split_ifs
    · have := hgt_polyOfList_le l; have := sum_natAbs_le_encode l
      have := natDegree_polyOfList_le l; have := length_le_encode l
      constructor <;> omega
    · rw [hgt_X_pow, natDegree_X_pow]; constructor <;> omega

theorem natDegree_wPoly_le (P Q : ℤ[X]) :
    (wPoly P Q).natDegree ≤ P.natDegree + Q.natDegree := by
  unfold wPoly
  have h1 := natDegree_derivative_le P
  have h2 := natDegree_derivative_le (derivative P)
  have h3 := natDegree_derivative_le Q
  have h4 := natDegree_derivative_le (derivative Q)
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_) <;>
    refine natDegree_mul_le.trans ?_ <;> omega

theorem integral_ee_GPfam (Q : ℤ[X]) (u i : ℕ) (ξ : ℝ) :
    ∫ ω, DecayAeNormal.ee (ξ * GPfam Q u i ω) ∂Derandomize.coins =
      DecayAeNormal.ee (ξ / 2) *
        pushFourier (GP Q u (polyOfCodeQ Q i)) (ξ / (2 * HQ u (polyOfCodeQ Q i))) := by
  have hH : (HQ u (polyOfCodeQ Q i) : ℝ) ≠ 0 := by
    have : 1 ≤ HQ u (polyOfCodeQ Q i) := Nat.le_add_left 1 _
    have : (1 : ℝ) ≤ HQ u (polyOfCodeQ Q i) := by exact_mod_cast this
    positivity
  have hHc : ((HQ u (polyOfCodeQ Q i) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hH
  unfold pushFourier
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [DecayAeNormal.ee, GPfam, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **Uniform decay data for the family: primitive recursive constants, per-index exponent.**

Confidence 85%.  English proof: for index `i` with `P = polyOfCodeQ Q i`, put
`N_i = (decoded list length) + deg Q` (primitive recursive, `≥ deg W_P` since
`deg W_P ≤ deg P + deg Q − 3`).  `pushFourier_le_of_deriv2_lower_unif` with `N = N_i`,
`c = L^{-(N_i+3)}` (`deriv2_GP_lower`, using `wPoly_polyOfCodeQ_ne_zero`),
`A = L^{deg P + 1} hgt P` (`GP_bounds`), `U` from `analyticOnNhd_GP`, gives
`‖pushFourier (GP Q u P) ξ‖ ≤ K₀(N_i+1)(1 + A)(1 + L^{N_i+3})^{K₀(N_i+1)} |ξ|^{-δ₀/(N_i+1)}`.
Normalising as in `decay_Gfam` (`∫ e(ξ GPfam) = e(ξ/2) pushFourier GP (ξ/(2H))`, `coins =
coinMeasure`) costs a factor `2H`, `H = HQ u P ≤` the primitive recursive `hgtBound`-type bound,
and `|ξ| < 1` is covered by adding `1`.  So `δ i = δ₀/(N_i + 1) ≤ 1`, `c i` is primitive
recursive, and `κ i = 32 ⌈δ₀⁻¹⌉² (N_i+1)²` bounds `Kc 1 (δ i)` (`Kc_one_le_of_le_one`). -/
theorem decay_GPfam (hBB : BakerBanajiUniformQuarterCantor) {Q : ℤ[X]} {u : ℕ}
    (hu : IsBranch Q u) (hQ : 0 < Q.natDegree) :
    ∃ c : ℕ → ℕ, Primrec c ∧ ∃ δ : ℕ → ℝ, (∀ i, 0 < δ i) ∧ ∃ κ : ℕ → ℕ, Primrec κ ∧
      (∀ i, ComputableNormal.Kc 1 (δ i) ≤ κ i) ∧ ∀ i, ∀ ξ : ℝ, ξ ≠ 0 →
        ‖∫ ω, DecayAeNormal.ee (ξ * GPfam Q u i ω) ∂Derandomize.coins‖ ≤ c i * |ξ| ^ (-δ i) := by
  obtain ⟨K₀, hK₀, δ₀, hδ₀, hδ₀1, hcut⟩ := pushFourier_le_of_deriv2_lower_unif hBB
  obtain ⟨L, hL, hlow⟩ := deriv2_GP_lower hu
  obtain ⟨LB, hLB, hbd⟩ := GP_bounds hu
  obtain ⟨U, hU, hsub, han⟩ := analyticOnNhd_GP hu
  set e := Q.natDegree
  set Dg := degBoundQ Q
  set Nn : ℕ → ℕ := fun i => Dg i + e with hNn
  set Hb : ℕ → ℕ := fun i => hgtBound i * (u + 2) ^ Dg i + 1 with hHb
  set Ab : ℕ → ℕ := fun i => LB ^ (Dg i + 1) * hgtBound i with hAb
  set Kn : ℕ → ℕ := fun i => K₀ * (Nn i + 1) with hKn
  set m := ⌈δ₀⁻¹⌉₊
  have hDg := primrec_degBoundQ Q
  have hNnp : Primrec Nn := Primrec.nat_add.comp hDg (Primrec.const e)
  have hHbp : Primrec Hb := Primrec.nat_add.comp (Primrec.nat_mul.comp primrec_hgtBound
    (ComputableNormal.primrec_pow.comp (Primrec.const (u + 2)) hDg)) (Primrec.const 1)
  have hAbp : Primrec Ab := Primrec.nat_mul.comp (ComputableNormal.primrec_pow.comp
    (Primrec.const LB) (Primrec.nat_add.comp hDg (Primrec.const 1))) primrec_hgtBound
  have hKnp : Primrec Kn := Primrec.nat_mul.comp (Primrec.const K₀)
    (Primrec.nat_add.comp hNnp (Primrec.const 1))
  refine ⟨fun i => Kn i * (1 + Ab i) * (1 + L ^ (Nn i + 3)) ^ Kn i * (2 * Hb i) + 2 * Hb i, ?_,
    fun i => δ₀ / (Nn i + 1), fun i => by positivity,
    fun i => 32 * m ^ 2 * (Nn i + 1) ^ 2, ?_, ?_, fun i ξ hξ => ?_⟩
  · have h2H : Primrec fun i => 2 * Hb i := Primrec.nat_mul.comp (Primrec.const 2) hHbp
    refine Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp
      hKnp (Primrec.nat_add.comp (Primrec.const 1) hAbp)) (ComputableNormal.primrec_pow.comp
        (Primrec.nat_add.comp (Primrec.const 1) (ComputableNormal.primrec_pow.comp
          (Primrec.const L) (Primrec.nat_add.comp hNnp (Primrec.const 3)))) hKnp)) h2H) h2H
  · exact Primrec.nat_mul.comp (Primrec.const _) (ComputableNormal.primrec_pow.comp
      (Primrec.nat_add.comp hNnp (Primrec.const 1)) (Primrec.const 2))
  · intro i
    have hN1 : (1 : ℝ) ≤ (Nn i : ℝ) + 1 := by linarith [(Nat.cast_nonneg (Nn i) : (0 : ℝ) ≤ _)]
    have hδi : δ₀ / ((Nn i : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    refine (FamilyDerandomize.Kc_one_le_of_le_one (by positivity) hδi).trans ?_
    have hm : δ₀⁻¹ ≤ (m : ℝ) := Nat.le_ceil _
    rw [div_pow, div_div_eq_mul_div]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ (m : ℝ) * δ₀ := by
      have := mul_le_mul_of_nonneg_right hm hδ₀.le
      rwa [inv_mul_cancel₀ hδ₀.ne'] at this
    have h2 : 1 ≤ ((m : ℝ) * δ₀) ^ 2 := one_le_pow₀ h1
    have h3 : (0 : ℝ) ≤ 32 * ((Nn i : ℝ) + 1) ^ 2 := by positivity
    nlinarith
  -- the decay bound
  set P := polyOfCodeQ Q i with hP
  obtain ⟨hhgt, hdeg⟩ := polyOfCodeQ_bounds Q i
  set d := P.natDegree
  have hW := wPoly_polyOfCodeQ_ne_zero hQ i
  obtain ⟨Z, hZ, hZlow⟩ := hlow P hW
  have hWd := natDegree_wPoly_le P Q
  set N := Nn i with hN
  have hdN : (wPoly P Q).natDegree ≤ N := by
    have h1 : Dg i = degBoundQ Q i := rfl
    have h2 : d = P.natDegree := rfl
    have h3 : e = Q.natDegree := rfl
    show _ ≤ Dg i + e; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set c0 : ℝ := ((L : ℝ) ^ (N + 3))⁻¹ with hc0
  have hc0p : 0 < c0 := by positivity
  have hlow' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c0 * (Z.map fun z => |t - z|).prod ≤
      |deriv (deriv (GP Q u P)) t| := by
    intro t ht
    refine le_trans ?_ (hZlow t ht)
    apply mul_le_mul_of_nonneg_right _ (Multiset.prod_nonneg fun x hx => by
      obtain ⟨_, _, rfl⟩ := Multiset.mem_map.1 hx; exact abs_nonneg _)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega))
  set H : ℝ := (HQ u P : ℝ) with hHdef
  have hH1 : 1 ≤ H := by rw [hHdef]; exact_mod_cast (Nat.le_add_left 1 _ : 1 ≤ HQ u P)
  have hHB : H ≤ (Hb i : ℝ) := by
    rw [hHdef]; simp only [HQ, hHb]; push_cast
    have h2 : (1 : ℝ) ≤ (u : ℝ) + 2 := by linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
    have : ((u : ℝ) + 2) ^ d ≤ ((u : ℝ) + 2) ^ Dg i := pow_le_pow_right₀ h2 hdeg
    have h' : (hgt P : ℝ) ≤ hgtBound i := by exact_mod_cast hhgt
    gcongr
  set A : ℝ := (Ab i : ℝ) with hAdef
  have hA : (LB : ℝ) ^ (d + 1) * hgt P ≤ A := by
    rw [hAdef]; simp only [hAb]; push_cast
    have hLB1 : (1 : ℝ) ≤ LB := by exact_mod_cast hLB
    have h' : (hgt P : ℝ) ≤ hgtBound i := by exact_mod_cast hhgt
    gcongr
  set δ' := δ₀ / ((N : ℝ) + 1) with hδ'
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ _)]
  have hδ'0 : 0 < δ' := by positivity
  have hδ'1 : δ' ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  change _ ≤ _ * |ξ| ^ (-δ')
  set ζ := ξ / (2 * H) with hζ
  have hζ0 : ζ ≠ 0 := div_ne_zero hξ (by positivity)
  have hX0 : 0 < |ξ| := abs_pos.2 hξ
  rw [integral_ee_GPfam, norm_mul]
  have hee : ‖DecayAeNormal.ee (ξ / 2)‖ = 1 := by
    unfold DecayAeNormal.ee
    rw [show 2 * Real.pi * Complex.I * ((ξ / 2 : ℝ) : ℂ) = ((2 * Real.pi * (ξ / 2) : ℝ) : ℂ) *
      Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [hee, one_mul]
  set W : ℝ := (1 + (L : ℝ) ^ (N + 3)) ^ Kn i with hW
  have hWr : (1 + c0⁻¹) ^ (K₀ * (N + 1)) = W := by rw [hc0, inv_inv, hW]
  have hpush : ((Kn i * (1 + Ab i) * (1 + L ^ (Nn i + 3)) ^ Kn i * (2 * Hb i) + 2 * Hb i : ℕ) : ℝ) =
      (Kn i : ℝ) * (1 + A) * W * (2 * Hb i) + 2 * Hb i := by
    rw [hW, hAdef]; push_cast; ring
  rw [hpush]
  have hXδ : 0 < |ξ| ^ (-δ') := Real.rpow_pos_of_pos hX0 _
  have hA0 : 0 ≤ A := by positivity
  have hWpos : (1 : ℝ) ≤ W := by rw [hW]; exact one_le_pow₀ (by linarith [(by positivity : (0:ℝ) ≤ (L : ℝ) ^ (N + 3))])
  have hBr : (1 : ℝ) ≤ Hb i := hH1.trans hHB
  have hKnr : ((Kn i : ℕ) : ℝ) = (K₀ * (N + 1) : ℝ) := by simp only [hKn, hN]; push_cast; ring
  rcases lt_or_ge |ζ| 1 with hz | hz
  · have hξH : |ξ| ≤ 2 * H := by
      rw [hζ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * H), div_lt_one (by positivity)] at hz
      exact hz.le
    have e1 : (2 * H) ^ (-δ') ≤ |ξ| ^ (-δ') := Real.rpow_le_rpow_of_nonpos hX0 hξH (by linarith)
    have e2 : (2 * H)⁻¹ ≤ (2 * H) ^ (-δ') := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e3 : 1 ≤ 2 * (Hb i : ℝ) * |ξ| ^ (-δ') := by
      calc (1 : ℝ) = 2 * H * (2 * H)⁻¹ := by field_simp
        _ ≤ 2 * Hb i * |ξ| ^ (-δ') := by gcongr; exact e2.trans e1
    have e4 : 0 ≤ (Kn i : ℝ) * (1 + A) * W * (2 * Hb i) * |ξ| ^ (-δ') := by positivity
    calc _ ≤ (1 : ℝ) := norm_pushFourier_le_one _ _
      _ ≤ _ := by nlinarith
  · have hcb := hcut N (GP Q u P) U hU hsub ((han P).contDiffOn hU.uniqueDiffOn) c0 A hc0p
      (fun t ht => ((hbd P t ht).2.1).trans hA) (fun t ht => ((hbd P t ht).2.2).trans hA)
      Z (hZ.trans hdN) hlow' ζ hζ0
    rw [hWr] at hcb
    have e2 : |ζ| ^ (-δ') ≤ 2 * H * |ξ| ^ (-δ') := by
      rw [hζ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * H),
        Real.div_rpow hX0.le (by positivity), Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * H),
        div_inv_eq_mul, mul_comm]
      gcongr
      calc (2 * H) ^ δ' ≤ (2 * H) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hδ'1
        _ = 2 * H := Real.rpow_one _
    rw [← hKnr] at hcb
    have hK0 : (0 : ℝ) ≤ (Kn i : ℝ) * (1 + A) * W := by positivity
    calc _ ≤ (Kn i : ℝ) * (1 + A) * W * |ζ| ^ (-δ') := hcb
      _ ≤ (Kn i : ℝ) * (1 + A) * W * (2 * H * |ξ| ^ (-δ')) := by gcongr
      _ ≤ (Kn i : ℝ) * (1 + A) * W * (2 * Hb i * |ξ| ^ (-δ')) := by gcongr
      _ ≤ _ := by nlinarith [mul_pos (by positivity : (0 : ℝ) < 2 * Hb i) hXδ]


/-- **Simultaneous derandomization: one computable `e` making every `G_P(y)`,
`P ∉ span(1, Q)`, normal in every base.**  Wiring proved: the per-index derandomizer on the
normalised family, then every `P` has an index and Wall undoes the normalisation. -/
theorem exists_computable_isAbsNormal_GP (hBB : BakerBanajiUniformQuarterCantor) {Q : ℤ[X]}
    {u : ℕ} (hu : IsBranch Q u) (hQ : 0 < Q.natDegree) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ P : ℤ[X], ¬ AffineIn P Q →
      IsAbsNormal (GP Q u P (cantorReal e)) := by
  obtain ⟨Ψ, A, hΨp, hΨ, hA0, hAG⟩ := approx_GPfam hu hQ
  obtain ⟨c, hc, δ, hδ, κ, hκ, hκδ, hdec⟩ := decay_GPfam hBB hu hQ
  obtain ⟨e, hce, hn⟩ := FamilyDerandomize.exists_computable_absNormal_family_var Ψ hΨp A hΨ
    hA0 (GPfam Q u) (measurable_GPfam hu) hAG c hc δ hδ κ hκ hκδ hdec
  refine ⟨e, hce, fun P hP b hb => ?_⟩
  obtain ⟨i, hi⟩ := exists_polyOfCodeQ_eq hQ hP
  have hq : ((2 * HQ u P : ℕ) : ℚ) ≠ 0 := by
    have : 1 ≤ HQ u P := Nat.le_add_left 1 _
    exact_mod_cast (show 2 * HQ u P ≠ 0 by omega)
  have h := isNormal_rat_mul_add b hb _ ((2 * HQ u P : ℕ) : ℚ) (-(HQ u P : ℚ)) hq (hn i b hb)
  have hH : (0 : ℝ) < HQ u P := by exact_mod_cast Nat.succ_pos _
  convert h using 1
  simp only [GPfam, hi]
  push_cast
  field_simp
  ring

/-- **`x` is a computable real.**

Confidence 85%.  English proof: `e` computable gives dyadic approximations of `y = cantorReal e`
(`4^{-D}` from a length-`D` prefix), hence of `w = a + c y`; bisection on `[u+1, u+2]` with exact
integer evaluation of `Q` at dyadics locates `Q⁻¹` to the matching precision (monotone branch,
`|Q'| ≥ 1`, so `|Q⁻¹(w) − Q⁻¹(w')| ≤ |w − w'|`). -/
theorem exists_computable_approx_xPQ {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {e : ℕ → Bool}
    (he : Computable e) :
    ∃ f : ℕ → ℤ, Computable f ∧ ∀ n : ℕ, |xPQ Q u e - f n / 2 ^ n| ≤ (1 / 2 : ℝ) ^ n := by
  sorry

/-! ### The headlines -/

/-- **Manai 2606.08325 §1.1, answered (computable form, sharp).**  For every non-constant
`Q ∈ ℤ[X]` there is one computable real `x`, on an explicit monotone branch of `Q`, with
`Q(x) = a + c · cantorReal e` (`e` computable, `a, c ∈ ℤ`, `c ≠ 0`) not normal in base 2, and for
every `P ∈ ℤ[X]`: `P(x)` is absolutely normal **iff** `P ∉ span_ℚ(1, Q)`.

Wiring proved: `exists_isBranch`, `branch_spec`, `exists_computable_isAbsNormal_GP`,
`exists_computable_approx_xPQ`, `not_isNormal_rat_affine_cantorReal`,
`not_isAbsNormal_of_affineIn`. -/
theorem exists_computable_PQ (hBB : BakerBanajiUniformQuarterCantor) (Q : ℤ[X])
    (hQ : 0 < Q.natDegree) :
    ∃ (u : ℕ) (a c : ℤ) (e : ℕ → Bool) (x : ℝ), Computable e ∧ c ≠ 0 ∧
      x ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2) ∧
      Set.InjOn (fun z : ℝ => aeval z Q) (Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2)) ∧
      aeval x Q = (a : ℝ) + c * cantorReal e ∧
      (∃ f : ℕ → ℤ, Computable f ∧ ∀ n : ℕ, |x - f n / 2 ^ n| ≤ (1 / 2 : ℝ) ^ n) ∧
      ¬ IsNormal 2 (aeval x Q) ∧
      ∀ P : ℤ[X], IsAbsNormal (aeval x P) ↔ ¬ AffineIn P Q := by
  obtain ⟨u, hu⟩ := exists_isBranch Q hQ
  obtain ⟨hc0, hinj, U, -, hsub, hinv, hmem⟩ := branch_spec hu
  obtain ⟨e, hce, hP⟩ := exists_computable_isAbsNormal_GP hBB hu hQ
  have hy := cantorReal_mem_window e
  have hQx : aeval (xPQ Q u e) Q = (aQ Q u : ℝ) + (cQ Q u : ℝ) * cantorReal e :=
    hinv _ (hsub hy)
  have hnn : ¬ IsNormal 2 (aeval (xPQ Q u e) Q) := by
    rw [hQx]
    have h := not_isNormal_rat_affine_cantorReal e (cQ Q u : ℚ) (aQ Q u : ℚ)
      (by exact_mod_cast hc0)
    intro h'; apply h
    convert h' using 1
    push_cast; ring
  refine ⟨u, aQ Q u, cQ Q u, e, xPQ Q u e, hce, hc0, hmem _ hy, hinj, hQx,
    exists_computable_approx_xPQ hu hce, hnn, fun P => ⟨fun hN hA => ?_, fun hA => ?_⟩⟩
  · exact not_isAbsNormal_of_affineIn hA hnn hN
  · exact hP P hA

/-- **The a.e. form**, from the analytic Baker–Banaji corollary (as `ae_mem_Omega`): almost every
quarter-Cantor `y` gives such an `x`.  Wiring proved: `analyticOnNhd_GP`, `deriv2_GP_lower` (for
`G_P'' ≢ 0` on the window), a countable intersection over `P`, `branch_spec`. -/
theorem exists_PQ_of_analytic (hBB : BakerBanajiAnalyticQuarterCantor) (Q : ℤ[X])
    (hQ : 0 < Q.natDegree) :
    ∃ x : ℝ, ¬ IsNormal 2 (aeval x Q) ∧ ∀ P : ℤ[X], ¬ AffineIn P Q → IsAbsNormal (aeval x P) := by
  obtain ⟨u, hu⟩ := exists_isBranch Q hQ
  obtain ⟨hc0, -, U₁, -, hsub₁, hinv, -⟩ := branch_spec hu
  obtain ⟨U, hU, hsub, han⟩ := analyticOnNhd_GP hu
  obtain ⟨L, hL, hlow⟩ := deriv2_GP_lower hu
  have hne : ∀ P : ℤ[X], ¬ AffineIn P Q →
      ∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv (GP Q u P)) t ≠ 0 := by
    intro P hP
    obtain ⟨Z, -, hZ⟩ := hlow P (wPoly_ne_zero_of_not_affineIn hQ hP)
    by_contra hall
    push Not at hall
    have hc : (0 : ℝ) < ((L : ℝ) ^ ((wPoly P Q).natDegree + 3))⁻¹ := by
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    exact not_deriv2_lower_of_deriv2_eq_zero _ hall hc Z hZ
  have hae : ∀ P : ℤ[X], ∀ᵐ ω ∂coinMeasure, ¬ AffineIn P Q →
      IsAbsNormal (GP Q u P (cantorReal ω)) := by
    intro P
    by_cases hP : AffineIn P Q
    · exact Eventually.of_forall fun ω h => absurd hP h
    · filter_upwards [hBB (GP Q u P) U hU hsub (han P) (hne P hP)] with ω hω
      exact fun _ => hω
  obtain ⟨ω, hω⟩ := (ae_all_iff.2 hae).exists
  have hy := cantorReal_mem_window ω
  refine ⟨xPQ Q u ω, ?_, fun P hP => hω P hP⟩
  rw [show aeval (xPQ Q u ω) Q = (aQ Q u : ℝ) + (cQ Q u : ℝ) * cantorReal ω from
    hinv _ (hsub₁ hy)]
  have h := not_isNormal_rat_affine_cantorReal ω (cQ Q u : ℚ) (aQ Q u : ℚ)
    (by exact_mod_cast hc0)
  intro h'; apply h
  convert h' using 1
  push_cast; ring

end NormalNumbers.ExplicitPQ
