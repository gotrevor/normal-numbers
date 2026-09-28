/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyAutomaton

/-!
# The class cocycle — the actual crux of Vandehey 2017, Theorem 1.1

`VandeheyAutomaton.lean` reduces Theorem 1.1 to a joint (window, state) frequency for the
det-`±D` transducer, *provided* the transducer has a synchronizing word.  A decidable probe
(`probes/cf_transducer_sync.py`, `probes/cf_transducer_class.py`,
`PROBE-2026-09-27-transducer-not-synchronizing.md`) shows **it does not**, and identifies
the obstruction exactly:

> mergeability of two transducer states is *equality of the row lattice `ℤ²M` up to
> scaling* — an invariant that ingest (`M ↦ M·B_a`) and emit (`M ↦ B_d⁻¹·M`) cannot change,
> because both act by matrices of determinant `±1`.

So the state space is an extension
`state = (class ∈ ℙ¹(ℤ/D)) × (fiber, which *is* mergeable inside a class)`, and the class
component is the mod-`D` reduction `c_i = c₀ · B_{a₁} ⋯ B_{a_i}` of the CF matrix product.
Each `B_a` is invertible mod `D`, so the class never forgets its past and **no word
synchronizes it**.  The missing ingredient is therefore exactly:

> **(Crux)** along a CF-normal orbit the class cocycle equidistributes, jointly with digit
> windows.

This is precisely the content Vandehey buys from the Pyatetskii-Shapiro criterion in the
Moshchevitin–Shkredov form — the step Airey–Mance refuted.  This module builds the
replacement, which needs no hot-spot criterion: a Cesàro average of the shift identity
`P_{i+k} = P_i · Q_i^{(k)}` (where `Q_i^{(k)}` depends only on the window at `i`) turns a
cocycle average into a *window* average, which CF-normality evaluates outright.

## This section: the engine

`cesaro_shift_bound` is the elementary inequality that does the work, and it is where the
non-synchronizing cocycle is tamed:

> `‖∑_{i<n} a i‖ ≤ ∑_{i<n} ‖(1/K) ∑_{k<K} a (i+k)‖ + 2 C K`   for `‖a‖ ≤ C`.

Averaging a bounded sequence against its own shifts costs only the `O(K)` boundary, so a
sum one cannot control termwise is dominated by a sum of *local* `K`-averages.  Applied with
`a i = f(window at i) · χ(P_i)` and `‖χ(P_i)‖ = 1`, the left side is the object we want and
the right side is a window average — exactly the shape `tendsto_window_mem_freq` eats.
-/

namespace NormalNumbers

open Filter Finset

namespace VandeheyCocycle

/-! ## The Cesàro shift engine -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Shifting the window of summation by `k` costs at most `2 C k`. -/
lemma norm_sum_shift_sub_le {a : ℕ → E} {C : ℝ} (hC : ∀ i, ‖a i‖ ≤ C) (n k : ℕ) :
    ‖(∑ i ∈ range n, a (i + k)) - ∑ i ∈ range n, a i‖ ≤ 2 * C * k := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hshift : ∑ i ∈ range n, a (i + k) = ∑ i ∈ Finset.Ico k (n + k), a i := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have hsplit₁ : (∑ i ∈ Finset.Ico 0 k, a i) + ∑ i ∈ Finset.Ico k (n + k), a i
      = ∑ i ∈ Finset.Ico 0 (n + k), a i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega)
  have hsplit₂ : (∑ i ∈ Finset.Ico 0 n, a i) + ∑ i ∈ Finset.Ico n (n + k), a i
      = ∑ i ∈ Finset.Ico 0 (n + k), a i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le n) (by omega)
  have hrange : ∀ m : ℕ, ∑ i ∈ Finset.Ico 0 m, a i = ∑ i ∈ range m, a i := by
    intro m; rw [Finset.range_eq_Ico]
  have hkey : (∑ i ∈ range n, a (i + k)) - ∑ i ∈ range n, a i
      = (∑ i ∈ Finset.Ico n (n + k), a i) - ∑ i ∈ Finset.Ico 0 k, a i := by
    rw [hshift]
    rw [hrange] at hsplit₂
    linear_combination (norm := abel) hsplit₁ - hsplit₂
  rw [hkey]
  have h1 : ‖∑ i ∈ Finset.Ico n (n + k), a i‖ ≤ C * k := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ C fun i _ => hC i) ?_
    simp [mul_comm]
  have h2 : ‖∑ i ∈ Finset.Ico 0 k, a i‖ ≤ C * k := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ C fun i _ => hC i) ?_
    simp [mul_comm]
  calc ‖(∑ i ∈ Finset.Ico n (n + k), a i) - ∑ i ∈ Finset.Ico 0 k, a i‖
      ≤ ‖∑ i ∈ Finset.Ico n (n + k), a i‖ + ‖∑ i ∈ Finset.Ico 0 k, a i‖ :=
        norm_sub_le _ _
    _ ≤ C * k + C * k := add_le_add h1 h2
    _ = 2 * C * k := by ring

/-- **The Cesàro shift engine.**  A bounded sequence's partial sum is dominated by the sum
of its own local `K`-averages, up to an `O(K)` boundary term.

This is the whole reason a *non-synchronizing* cocycle can still be handled: the local
`K`-average of `a i = f(window) · χ(P_i)` factors as `χ(P_i)` (a unit) times a quantity
depending only on the length-`(K + |window|)` window at `i`, so the right-hand side is a
plain window average — which CF-normality evaluates. -/
theorem cesaro_shift_bound {a : ℕ → E} {C : ℝ} (hC : ∀ i, ‖a i‖ ≤ C) (n : ℕ) {K : ℕ}
    (hK : 0 < K) :
    ‖∑ i ∈ range n, a i‖
      ≤ (∑ i ∈ range n, ‖(K : ℝ)⁻¹ • ∑ k ∈ range K, a (i + k)‖) + 2 * C * K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set S : E := ∑ i ∈ range n, a i with hS
  set T : ℕ → E := fun k => ∑ i ∈ range n, a (i + k) with hT
  set A : E := (K : ℝ)⁻¹ • ∑ k ∈ range K, T k with hA
  -- `A` is the sum of the local `K`-averages
  have havg : A = ∑ i ∈ range n, (K : ℝ)⁻¹ • ∑ k ∈ range K, a (i + k) := by
    rw [hA, hT, Finset.sum_comm, Finset.smul_sum]
  -- `A` is close to `S`
  have hdiff : ‖A - S‖ ≤ 2 * C * K := by
    have hsum : ∑ k ∈ range K, (T k - S) = (∑ k ∈ range K, T k) - (K : ℕ) • S := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hKS : (K : ℝ)⁻¹ • ((K : ℕ) • S) = S := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (ne_of_gt hKR), one_smul]
    have hrw : A - S = (K : ℝ)⁻¹ • ∑ k ∈ range K, (T k - S) := by
      rw [hsum, smul_sub, hKS, hA]
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hb : ‖∑ k ∈ range K, (T k - S)‖ ≤ (K : ℝ) * (2 * C * K) := by
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * C * K) fun k hk => ?_) ?_
      · refine le_trans (norm_sum_shift_sub_le hC n k) ?_
        have hkK : (k : ℝ) ≤ K := by exact_mod_cast le_of_lt (Finset.mem_range.mp hk)
        nlinarith
      · simp [Finset.card_range, nsmul_eq_mul]
    calc (K : ℝ)⁻¹ * ‖∑ k ∈ range K, (T k - S)‖
        ≤ (K : ℝ)⁻¹ * ((K : ℝ) * (2 * C * K)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * C * K := by field_simp
  have hSA : S = A - (A - S) := by abel
  calc ‖S‖ = ‖A - (A - S)‖ := by rw [← hSA]
    _ ≤ ‖A‖ + ‖A - S‖ := norm_sub_le _ _
    _ ≤ (∑ i ∈ range n, ‖(K : ℝ)⁻¹ • ∑ k ∈ range K, a (i + k)‖) + 2 * C * K := by
        refine add_le_add ?_ hdiff
        rw [havg]
        exact norm_sum_le _ _

/-! ## Van der Corput: the correlation form, where the cocycle cancels

`cesaro_shift_bound` leaves a sum of local `K`-averages, and bounding those in `L¹` is a
*variance* statement.  One Cauchy–Schwarz converts it into the **correlation** form, which
asks instead only for decay of `⟪a (i+k), a (i+k')⟫` in the gap `k' − k`.

⚠️ **What this does NOT give.**  For a *scalar* cocycle `a i = f(win_i) · χ(P_i)` the cocycle
cancels outright, `a (i+k) · conj (a i) = f f' · χ(Q_i^{(k)})`, because a 1-dimensional
character commutes — and then the correlations see no hidden state at all.  That cancellation
is **unavailable here**: the class group is `PGL₂(ℤ/D)`, which for `D = 2` is `S₃` acting on
the three points of `ℙ¹(𝔽₂)`, so its scalar characters (only the sign) cannot detect
equidistribution on `X`; the 2-dimensional irrep is needed, and for a higher-dimensional `π`,
`⟪π(Q) z, π(Q') z⟫` still depends on `z = π(P_i) w`.

What survives is nevertheless the decisive gain: `z` ranges over the **finite** orbit
`{π(g) w}`, so the correlation is `f f' · Φ(increment, c_{i+k})` with a harmless finite hidden
parameter, and the obligation drops from a *variance* to a *first-moment decay in the gap*:

> `𝔼_γ [ f(win_0) · f(win_m) · (1[d · W_m = d'] − 1/|X|) ] → 0`   as `m → ∞`, uniformly in `d, d'`,

i.e. the class walk's distribution after `m` steps is asymptotically uniform even when
conditioned on the first `|q|` digits and read jointly with the digits at `m`.  That is a
Markov convergence statement for the class walk, and its two inputs are both in reach: the
digit walk's ψ-mixing (`philipp_psi_mixing_holds`, already in the repo) and
aperiodicity + transitivity of the walk on the finite group generated by the `B_a mod D`. -/

section VanDerCorput

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The squared norm of a finite sum, expanded into inner products. -/
lemma norm_sum_sq_eq (v : ℕ → H) (K : ℕ) :
    ‖∑ k ∈ range K, v k‖ ^ 2
      = ∑ k ∈ range K, ∑ k' ∈ range K, (inner ℝ (v k) (v k')) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  exact Finset.sum_congr rfl fun k _ => inner_sum _ _ _

/-- **The van der Corput bound.**  A bounded sum is controlled by its own *correlations*,
which for a cocycle no longer see the cocycle at all.  Derived from `cesaro_shift_bound` by
one Cauchy–Schwarz. -/
theorem vanDerCorput_bound {a : ℕ → H} {C : ℝ} (hC : ∀ i, ‖a i‖ ≤ C) (n : ℕ) {K : ℕ}
    (hK : 0 < K) :
    ‖∑ i ∈ range n, a i‖
      ≤ Real.sqrt (n * ((K : ℝ)⁻¹ ^ 2 * ∑ k ∈ range K, ∑ k' ∈ range K,
            ∑ i ∈ range n, (inner ℝ (a (i + k)) (a (i + k')))))
        + 2 * C * K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  set b : ℕ → H := fun i => (K : ℝ)⁻¹ • ∑ k ∈ range K, a (i + k) with hb
  have hstep := cesaro_shift_bound hC n hK
  -- expand `‖b i‖²`
  have hexp : ∀ i, ‖b i‖ ^ 2 = (K : ℝ)⁻¹ ^ 2 *
      ∑ k ∈ range K, ∑ k' ∈ range K, (inner ℝ (a (i + k)) (a (i + k'))) := by
    intro i
    rw [hb]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (K:ℝ)⁻¹),
      mul_pow]
    rw [norm_sum_sq_eq]
  -- Cauchy–Schwarz over `i`
  have hcs : (∑ i ∈ range n, ‖b i‖) ^ 2 ≤ n * ∑ i ∈ range n, ‖b i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range n) (f := fun i => ‖b i‖)
    simpa [Finset.card_range] using this
  have hswap : ∑ i ∈ range n, ‖b i‖ ^ 2
      = (K : ℝ)⁻¹ ^ 2 * ∑ k ∈ range K, ∑ k' ∈ range K,
          ∑ i ∈ range n, (inner ℝ (a (i + k)) (a (i + k'))) := by
    rw [Finset.sum_congr rfl fun i _ => hexp i, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  have hsqrt : (∑ i ∈ range n, ‖b i‖)
      ≤ Real.sqrt (n * ((K : ℝ)⁻¹ ^ 2 * ∑ k ∈ range K, ∑ k' ∈ range K,
            ∑ i ∈ range n, (inner ℝ (a (i + k)) (a (i + k'))))) := by
    rw [← hswap]
    have hx : (0 : ℝ) ≤ ∑ i ∈ range n, ‖b i‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    calc ∑ i ∈ range n, ‖b i‖ = Real.sqrt ((∑ i ∈ range n, ‖b i‖) ^ 2) :=
          (Real.sqrt_sq hx).symm
      _ ≤ Real.sqrt (n * ∑ i ∈ range n, ‖b i‖ ^ 2) := Real.sqrt_le_sqrt hcs
  exact le_trans hstep (add_le_add hsqrt (le_refl _))

end VanDerCorput

/-! ## The cocycle along the CF expansion

The transducer's class component is `c_i = c₀ · g(a₁) ⋯ g(a_i)` for `g` sending a CF digit
to the image of `B_a = [[0,1],[1,a]]` in the finite group `PGL₂(ℤ/D)` — only `a mod D`
matters, as the probe's tables show.  Everything below is stated for an arbitrary monoid so
that the concrete `PGL₂(ℤ/D)` instance is a plug-in, and so the Wall-side automata of
`WallCrux.lean` can reuse it.
-/

variable {G : Type*} [Monoid G]

/-- The cocycle after `i` CF digits of `x`: `g(a₁) ⋯ g(a_i)`. -/
noncomputable def cocycleOf (g : ℕ → G) (x : ℝ) (i : ℕ) : G :=
  ((VandeheyAut.cfWord x i).map g).prod

/-- The cocycle increment over the digits at positions `i, …, i+k−1`.  This is a function of
the **window** alone — which is the entire point. -/
noncomputable def windowProd (g : ℕ → G) (x : ℝ) (i k : ℕ) : G :=
  ((VandeheyAut.cfWindow x i k).map g).prod

@[simp] lemma cocycleOf_zero (g : ℕ → G) (x : ℝ) : cocycleOf g x 0 = 1 := by
  simp [cocycleOf, VandeheyAut.cfWord]

@[simp] lemma windowProd_zero (g : ℕ → G) (x : ℝ) (i : ℕ) : windowProd g x i 0 = 1 := by
  simp [windowProd]

/-- `windowProd` depends only on the window, as a list of digits. -/
lemma windowProd_eq_of_window_eq {g : ℕ → G} {x y : ℝ} {i j k : ℕ}
    (h : VandeheyAut.cfWindow x i k = VandeheyAut.cfWindow y j k) :
    windowProd g x i k = windowProd g y j k := by
  simp [windowProd, h]

/-- **The shift identity.**  `P_{i+k} = P_i · Q_i^{(k)}`, with the increment a function of
the length-`k` window at `i`.  This is what makes `cesaro_shift_bound` bite: averaging the
cocycle against its own shifts replaces a global product by a *local* one. -/
theorem cocycleOf_add (g : ℕ → G) (x : ℝ) (i k : ℕ) :
    cocycleOf g x (i + k) = cocycleOf g x i * windowProd g x i k := by
  rw [cocycleOf, cocycleOf, windowProd, VandeheyAut.cfWord_add, List.map_append,
    List.prod_append]

/-- The increment splits along a subdivision of the window. -/
theorem windowProd_add (g : ℕ → G) (x : ℝ) (i k l : ℕ) :
    windowProd g x i (k + l) = windowProd g x i k * windowProd g x (i + k) l := by
  rw [windowProd, windowProd, windowProd, VandeheyAut.cfWindow_add, List.map_append,
    List.prod_append]

/-- The cocycle depends on the digit map only through the digits it reads. -/
lemma cocycleOf_congr {g h : ℕ → G} {x : ℝ} {i : ℕ}
    (hgh : ∀ j < i, g (cfDigit x j) = h (cfDigit x j)) :
    cocycleOf g x i = cocycleOf h x i := by
  simp only [cocycleOf, VandeheyAut.cfWord, List.map_map]
  refine congrArg List.prod (List.map_congr_left ?_)
  intro j hj
  exact hgh j (List.mem_range.mp hj)

/-! ## The reduction: a joint-frequency deviation is dominated by a WINDOW average

This is where the corrected route replaces the synchronizing one.  The old route needed the
state at `i` to be a function of the window at `i` — false, by the row-lattice obstruction.
What *is* true is the plain cocycle identity `stateAt (i+k) = runState (stateAt i) (window)`.
So the local `K`-average of the joint deviation is a function of the (bounded, finitely many)
window at `i` **and the hidden state at `i`** — and taking the worst case over the finitely
many hidden states leaves a function of the window alone.  Combined with
`cesaro_shift_bound`, the whole joint frequency is then controlled by a window average, which
`VandeheyAut.tendsto_window_mem_freq` evaluates against `γ`.

Crucially the reference value `L` is a free parameter here: the analytic leaf below gets to
*choose* it, and because the leaf speaks only about `γ`, the `L` it produces is automatically
independent of `x` — which is exactly the `VandeheyUniformFreq` contract.
-/

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The deviation of the joint (window, state) event at position `i` from a reference
value `L`. -/
noncomputable def jointDev (δ : X → ℕ → X) (s₀ t : X) (q : List ℕ) (L : ℝ) (x : ℝ) (i : ℕ) :
    ℝ :=
  (if q = VandeheyAut.cfWindow x i q.length then (1 : ℝ) else 0) *
    ((if VandeheyAut.stateAt δ s₀ x i = t then (1 : ℝ) else 0) - L)

/-- The local `K`-average of `jointDev`, read off a window `W` and a hidden state `d`. -/
noncomputable def localAvg (δ : X → ℕ → X) (t : X) (q : List ℕ) (L : ℝ) (K : ℕ)
    (d : X) (W : List ℕ) : ℝ :=
  (K : ℝ)⁻¹ * ∑ k ∈ range K,
    (if q = (W.drop k).take q.length then (1 : ℝ) else 0) *
      ((if VandeheyAut.runState δ d (W.take k) = t then (1 : ℝ) else 0) - L)

/-- The worst case of `localAvg` over the hidden state: **a function of the window alone**.
The state set is finite, so this costs nothing, and it is what removes the unbounded memory
that the row-lattice obstruction forces on the transducer. -/
noncomputable def windowBound (δ : X → ℕ → X) (t : X) (q : List ℕ) (L : ℝ) (K : ℕ)
    (W : List ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun d => |localAvg δ t q L K d W|

omit [Fintype X] [Nonempty X] in
lemma abs_jointDev_le (δ : X → ℕ → X) (s₀ t : X) (q : List ℕ) (L : ℝ) (x : ℝ) (i : ℕ) :
    |jointDev δ s₀ t q L x i| ≤ 1 + |L| := by
  rw [jointDev, abs_mul]
  have h1 : |(if q = VandeheyAut.cfWindow x i q.length then (1 : ℝ) else 0)| ≤ 1 := by
    split <;> simp
  have h2 : |(if VandeheyAut.stateAt δ s₀ x i = t then (1 : ℝ) else 0) - L| ≤ 1 + |L| := by
    refine le_trans (abs_sub _ _) (add_le_add ?_ (le_refl _))
    split <;> simp
  calc |(if q = VandeheyAut.cfWindow x i q.length then (1 : ℝ) else 0)|
        * |(if VandeheyAut.stateAt δ s₀ x i = t then (1 : ℝ) else 0) - L|
      ≤ 1 * (1 + |L|) :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 + |L| := one_mul _

/-- **The local average is read off the window.**  `jointDev` at `i + k`, averaged over
`k < K`, equals `localAvg` at the hidden state `stateAt … i` and the length-`(K + |q|)`
window at `i`. -/
theorem localAvg_eq (δ : X → ℕ → X) (s₀ t : X) (q : List ℕ) (L : ℝ) (x : ℝ) (i K : ℕ) :
    (K : ℝ)⁻¹ * ∑ k ∈ range K, jointDev δ s₀ t q L x (i + k)
      = localAvg δ t q L K (VandeheyAut.stateAt δ s₀ x i)
          (VandeheyAut.cfWindow x i (K + q.length)) := by
  rw [localAvg]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkK : k < K := Finset.mem_range.mp hk
  have hwin : VandeheyAut.cfWindow x (i + k) q.length
      = ((VandeheyAut.cfWindow x i (K + q.length)).drop k).take q.length :=
    (VandeheyAut.cfWindow_drop_take x i (K + q.length) k q.length (by omega)).symm
  have hst : VandeheyAut.stateAt δ s₀ x (i + k)
      = VandeheyAut.runState δ (VandeheyAut.stateAt δ s₀ x i)
          ((VandeheyAut.cfWindow x i (K + q.length)).take k) := by
    rw [VandeheyAut.stateAt_add,
      VandeheyAut.cfWindow_take x i (K + q.length) k (by omega)]
  rw [jointDev, hwin, hst]

/-- **The reduction.**  The joint (window, state) count deviates from `L·n` by at most a sum
of *window* bounds plus an `O(K)` boundary term.  The right-hand side no longer mentions the
initial state `s₀` at all, and mentions `x` only through its digit windows — which is exactly
the leverage CF-normality provides. -/
theorem abs_sum_jointDev_le (δ : X → ℕ → X) (s₀ t : X) (q : List ℕ) (L : ℝ) (x : ℝ)
    (n : ℕ) {K : ℕ} (hK : 0 < K) :
    |∑ i ∈ range n, jointDev δ s₀ t q L x i|
      ≤ (∑ i ∈ range n,
            windowBound δ t q L K (VandeheyAut.cfWindow x i (K + q.length)))
        + 2 * (1 + |L|) * K := by
  have hb := cesaro_shift_bound (a := fun i => jointDev δ s₀ t q L x i)
    (C := 1 + |L|) (abs_jointDev_le δ s₀ t q L x) n hK
  simp only [Real.norm_eq_abs, smul_eq_mul] at hb
  refine le_trans hb (add_le_add (Finset.sum_le_sum fun i _ => ?_) (le_refl _))
  rw [localAvg_eq, windowBound]
  exact Finset.le_sup' (fun d => |localAvg δ t q L K d
    (VandeheyAut.cfWindow x i (K + q.length))|) (Finset.mem_univ _)

/-- `windowBound` is bounded by `1 + |L|`, uniformly. -/
lemma windowBound_le (δ : X → ℕ → X) (t : X) (q : List ℕ) (L : ℝ) {K : ℕ} (hK : 0 < K)
    (W : List ℕ) : windowBound δ t q L K W ≤ 1 + |L| := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  rw [windowBound]
  refine Finset.sup'_le _ _ fun d _ => ?_
  rw [localAvg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (K : ℝ)⁻¹)]
  have hterm : ∀ k ∈ range K,
      |(if q = (W.drop k).take q.length then (1 : ℝ) else 0) *
        ((if VandeheyAut.runState δ d (W.take k) = t then (1 : ℝ) else 0) - L)| ≤ 1 + |L| := by
    intro k _
    rw [abs_mul]
    have h1 : |(if q = (W.drop k).take q.length then (1 : ℝ) else 0)| ≤ 1 := by
      split <;> simp
    have h2 : |(if VandeheyAut.runState δ d (W.take k) = t then (1 : ℝ) else 0) - L|
        ≤ 1 + |L| := by
      refine le_trans (abs_sub _ _) (add_le_add ?_ (le_refl _))
      split <;> simp
    calc _ ≤ 1 * (1 + |L|) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 + |L| := one_mul _
  have hsum : |∑ k ∈ range K,
      (if q = (W.drop k).take q.length then (1 : ℝ) else 0) *
        ((if VandeheyAut.runState δ d (W.take k) = t then (1 : ℝ) else 0) - L)|
      ≤ K * (1 + |L|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (1 + |L|) hterm) ?_
    rw [Finset.card_range, nsmul_eq_mul]
  calc (K : ℝ)⁻¹ * |∑ k ∈ range K, _| ≤ (K : ℝ)⁻¹ * (K * (1 + |L|)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 + |L| := by field_simp

/-! ## The corrected transfer principle

`ClassEquidistribution` is the crux of Vandehey 2017 Theorem 1.1, isolated as one named
`Prop`.  It says: there is a reference weight `L` — mentioning neither the initial state nor
`x` — whose `windowBound` averages are eventually uniformly small over **all** CF-normal
points.  For the det-`±D` transducer `L` should be `1/|ℙ¹(ℤ/D)|` on a transitive class
component, and the content is the cancellation in the class cocycle
(`PROBE-2026-09-27-transducer-not-synchronizing.md`, step 4).

Everything else is now unconditional: `tendsto_jointCount_of_classEquidistribution` delivers
exactly the `x`-independent joint frequency that `VandeheyUniformFreq` asks for, and it
replaces `VandeheyAut.exists_jointFreq_limit`, whose `Synchronizing` hypothesis the probe
showed is unsatisfiable. -/
def ClassEquidistribution (δ : X → ℕ → X) (t : X) (q : List ℕ) : Prop :=
  ∃ L : ℝ, ∀ ε > 0, ∃ K : ℕ, 0 < K ∧ ∀ x : ℝ, IsCFNormal x →
    ∀ᶠ n in atTop,
      (∑ i ∈ range n, windowBound δ t q L K (VandeheyAut.cfWindow x i (K + q.length)))
        ≤ ε * n

/-- `jointDev` summed is the joint count minus `L` times the window count. -/
theorem sum_jointDev_eq (δ : X → ℕ → X) (s₀ t : X) (q : List ℕ) (L : ℝ) (x : ℝ) (n : ℕ) :
    ∑ i ∈ range n, jointDev δ s₀ t q L x i
      = (VandeheyAut.jointCount δ s₀ t q x n : ℝ)
        - L * ((range n).filter fun i => q = VandeheyAut.cfWindow x i q.length).card := by
  classical
  have hpt : ∀ i, jointDev δ s₀ t q L x i
      = (if q = VandeheyAut.cfWindow x i q.length ∧ VandeheyAut.stateAt δ s₀ x i = t
            then (1 : ℝ) else 0)
        - L * (if q = VandeheyAut.cfWindow x i q.length then (1 : ℝ) else 0) := by
    intro i
    rw [jointDev]
    by_cases h1 : q = VandeheyAut.cfWindow x i q.length
    · by_cases h2 : VandeheyAut.stateAt δ s₀ x i = t
      · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]; ring
      · have hnot : ¬(q = VandeheyAut.cfWindow x i q.length
            ∧ VandeheyAut.stateAt δ s₀ x i = t) := fun h => h2 h.2
        rw [if_pos h1, if_neg h2, if_neg hnot]; ring
    · have hnot : ¬(q = VandeheyAut.cfWindow x i q.length
          ∧ VandeheyAut.stateAt δ s₀ x i = t) := fun h => h1 h.1
      rw [if_neg h1, if_neg hnot]; ring
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, VandeheyAut.jointCount_eq_card, VandeheyAut.jointSet]

/-- **The corrected transfer principle.**  Granted `ClassEquidistribution`, the joint
(window, state) frequency along any CF-normal `x` converges to `L · γ(I_q)` — a value that
mentions neither `x` nor the initial state.  This is the replacement for
`VandeheyAut.exists_jointFreq_limit`. -/
theorem tendsto_jointCount_of_classEquidistribution {δ : X → ℕ → X} {t : X} {q : List ℕ}
    (hce : ClassEquidistribution δ t q) (hq : q ≠ []) (hqpos : ∀ a ∈ q, 1 ≤ a) :
    ∃ L : ℝ, ∀ (s₀ : X) (x : ℝ), IsCFNormal x →
      Tendsto (fun n => (VandeheyAut.jointCount δ s₀ t q x n : ℝ) / n) atTop
        (nhds (L * (gaussMeasure (cfCylinder q)).toReal)) := by
  obtain ⟨L, hL⟩ := hce
  refine ⟨L, fun s₀ x hx => ?_⟩
  set γq : ℝ := (gaussMeasure (cfCylinder q)).toReal with hγq
  -- the window frequency
  have hwin : Tendsto (fun n => (((range n).filter
      fun i => q = VandeheyAut.cfWindow x i q.length).card : ℝ) / n) atTop (nhds γq) :=
    VandeheyAut.tendsto_windowFreq hx q hq hqpos
  -- the deviation is eventually `≤ ε` for every `ε`
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK, hKle⟩ := hL (ε / 3) (by positivity)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  -- the boundary term and the window-frequency error are eventually small
  have hbdry : Tendsto (fun n : ℕ => 2 * (1 + |L|) * K / n) atTop (nhds 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (2 * (1 + |L|) * K)
  rw [Metric.tendsto_atTop] at hwin hbdry
  obtain ⟨N₁, hN₁⟩ := hwin (ε / (3 * (1 + |L|))) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hbdry (ε / 3) (by positivity)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (hKle x hx)
  refine ⟨max (max (max N₁ N₂) N₃) 1, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hn
  have hn₃ : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  set Bn : ℝ := (((range n).filter
    fun i => q = VandeheyAut.cfWindow x i q.length).card : ℝ) with hBn
  set An : ℝ := (VandeheyAut.jointCount δ s₀ t q x n : ℝ) with hAn
  -- step 1: `|An - L * Bn| ≤ (ε/3) n + 2(1+|L|)K`
  have hstep1 : |An - L * Bn| ≤ (ε / 3) * n + 2 * (1 + |L|) * K := by
    have h := abs_sum_jointDev_le δ s₀ t q L x n hK
    rw [sum_jointDev_eq] at h
    exact le_trans h (add_le_add (hN₃ n hn₃) (le_refl _))
  -- step 2: divide by `n`
  have hstep2 : |An / n - L * (Bn / n)| ≤ ε / 3 + 2 * (1 + |L|) * K / n := by
    have : An / n - L * (Bn / n) = (An - L * Bn) / n := by field_simp
    rw [this, abs_div, abs_of_pos hnR]
    rw [div_le_iff₀ hnR]
    calc |An - L * Bn| ≤ (ε / 3) * n + 2 * (1 + |L|) * K := hstep1
      _ = (ε / 3 + 2 * (1 + |L|) * K / n) * n := by field_simp
  -- step 3: replace `Bn / n` by `γq`
  have hL1 : (0 : ℝ) < 1 + |L| := by positivity
  have hstep3 : |L * (Bn / n) - L * γq| ≤ ε / 3 := by
    rw [← mul_sub, abs_mul]
    have hb := hN₁ n hn₁
    rw [Real.dist_eq] at hb
    calc |L| * |Bn / n - γq| ≤ (1 + |L|) * (ε / (3 * (1 + |L|))) := by
          refine mul_le_mul (by linarith [abs_nonneg L]) (le_of_lt hb) (abs_nonneg _)
            (le_of_lt hL1)
      _ = ε / 3 := by field_simp
  have hstep4 : 2 * (1 + |L|) * K / n < ε / 3 := by
    have := hN₂ n hn₂
    rw [Real.dist_eq, sub_zero] at this
    calc 2 * (1 + |L|) * K / n ≤ |2 * (1 + |L|) * K / n| := le_abs_self _
      _ < ε / 3 := this
  rw [Real.dist_eq]
  calc |An / n - L * γq|
      ≤ |An / n - L * (Bn / n)| + |L * (Bn / n) - L * γq| := abs_sub_le _ _ _
    _ ≤ (ε / 3 + 2 * (1 + |L|) * K / n) + ε / 3 := add_le_add hstep2 hstep3
    _ < (ε / 3 + ε / 3) + ε / 3 := by linarith
    _ = ε := by ring

/-! ## Non-vacuity anchor

`ClassEquidistribution` must not be a condition nobody can meet.  The one-state automaton
meets it with `L = 1`, and the transfer principle then reproduces plain CF-normality on
windows — so the statement is calibrated correctly (the hypothesis is satisfiable and the
conclusion is the expected one, not something degenerate). -/

theorem classEquidistribution_unit (q : List ℕ) :
    ClassEquidistribution (fun (_ : Unit) (_ : ℕ) => ()) () q := by
  refine ⟨1, fun ε hε => ⟨1, Nat.one_pos, fun x _ => .of_forall fun n => ?_⟩⟩
  have hzero : ∀ W : List ℕ,
      windowBound (fun (_ : Unit) (_ : ℕ) => ()) () q 1 1 W = 0 := by
    intro W
    simp [windowBound, localAvg]
  rw [Finset.sum_congr rfl fun i _ => hzero _, Finset.sum_const, smul_zero]
  positivity

/-- The anchor's conclusion: the transfer principle applied to the one-state automaton is
exactly CF-normality's window statement. -/
theorem tendsto_jointCount_unit {q : List ℕ} (hq : q ≠ []) (hqpos : ∀ a ∈ q, 1 ≤ a) :
    ∃ L : ℝ, ∀ (s₀ : Unit) (x : ℝ), IsCFNormal x →
      Tendsto (fun n => (VandeheyAut.jointCount (fun (_ : Unit) (_ : ℕ) => ()) s₀ () q x n : ℝ)
        / n) atTop (nhds (L * (gaussMeasure (cfCylinder q)).toReal)) :=
  tendsto_jointCount_of_classEquidistribution (classEquidistribution_unit q) hq hqpos

end VandeheyCocycle

end NormalNumbers
