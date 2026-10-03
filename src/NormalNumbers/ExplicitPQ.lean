/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitOmegaK
import NormalNumbers.FamilyDerandomizeVar

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
  sorry

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
  sorry

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

/-- **Computable lower approximations of the normalised family with exact primitive recursive
floors** (the analogue of `approx_Gfam`, with bisection for `Q⁻¹`).

Confidence 85%.  English proof: a length-`D` prefix fixes `y` up to `4^{-D}/6`, and `|GPfam'| ≤
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
  sorry

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
