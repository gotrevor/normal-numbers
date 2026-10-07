/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Prime.Int

/-!
# Sparse identities `tᵟ·U = V` and pairs of sparse points on an orbit mod `3^A − 1`

Ren, 2026-10-07 (repetition review lap 7).  The copy zone of `CantorRepetition` needs: along an
orbit `y_n = c·tⁿ mod 3^A − 1`, few `n` give a residue whose cyclic ternary word has few digit
changes ("sparse" residues; these are exactly the residues where the cyclic Riesz product
`cycProd` is large).  The previous laps posed this as `TOrbitCyclicDecay` (a power saving, an open
digits-of-powers problem in the wrap regime).  The assembly only needs a saving summable along
`sched` (polylogarithmic suffices), and that follows from a **pair argument**:

* `cyclic_pair_identity` (elementary): if `y` and `T·y mod 3^A − 1` are both sparse and `A` is
  large compared with `K log T`, then rotating the cyclic word to put a long empty arc at the
  wrap point turns the congruence into an exact integer identity `T·U = V` between two sparse
  integers, with `U ≠ 0` unless `2y ≡ 0`.
* `SparseIdentityBound t` (from Baker-type input, `sparseIdentityBound_of_matveev`): an identity
  `tᵟ·U = V` between `K`-sparse integers with `U ≠ 0` forces `δ ≤ exp(C(K+1)²)`.

So two sparse points of one orbit at distance `δ ≤ D ≈ A/(2K log₃ t)` are at distance
`≤ L_K := exp(C(K+1)²)`, and sparse points occur in clusters of diameter `≤ L_K` separated by
`> D`.  For the runs of `CantorRepetition` (`A = a_k`, orbit length `≈ (k+2)a_k`) this bounds the
sparse points per orbit by `O(K k L_K)`, independent of `A`.

Sibling checks (recorded as theorems): `t = 9` (a power of 3) has `9ᵟ·1 = 3^{2δ}`, so
`SparseIdentityBound 9` is false (`not_sparseIdentityBound_nine`), as it must be, since `x ∈ K`
is never normal to base 9.  `t = 1` likewise (`not_sparseIdentityBound_one`).  Degenerate case
`K ≤ 1`: only `δ ≤ 1` (`pow_le_two_of_sparse_one`).
-/

open Finset

namespace NormalNumbers.SparseIdentity

/-- `X` is a signed sum of at most `K` distinct powers of 3 with coefficients in `{±1, ±2}`. -/
def IsSparse3 (K : ℕ) (X : ℤ) : Prop :=
  ∃ (S : Finset ℕ) (c : ℕ → ℤ), S.card ≤ K ∧ (∀ e ∈ S, c e ≠ 0 ∧ |c e| ≤ 2) ∧
    X = ∑ e ∈ S, c e * 3 ^ e

/-- `y` is `K`-sparse **cyclically** modulo `3^A − 1`: `2y` is congruent to a signed sum of at
most `K` distinct powers `3^e`, `e < A`, with coefficients in `{±1, ±2}`.  A residue whose cyclic
ternary word has `K` digit changes is `K`-sparse: `2y = 3y − y ≡ Σᵢ (a_{i−1} − aᵢ) 3ⁱ`. -/
def CycSparse (A K : ℕ) (y : ℤ) : Prop :=
  ∃ (S : Finset ℕ) (c : ℕ → ℤ), S ⊆ range A ∧ S.card ≤ K ∧ (∀ e ∈ S, c e ≠ 0 ∧ |c e| ≤ 2) ∧
    2 * y ≡ ∑ e ∈ S, c e * 3 ^ e [ZMOD (3 ^ A - 1)]

/-- **Literature (cited, referee needed): Matveev's lower bound for three logarithms of positive
rationals**, in a weak form.  E. M. Matveev, *An explicit lower bound for a homogeneous rational
linear form in logarithms of algebraic numbers II*, Izv. Math. 64 (2000) 1217–1269,
Corollary 2.3: for algebraic `α₁, …, αₙ` in a field of degree `D`, integers `bᵢ` with
`Λ = Σ bᵢ log αᵢ ≠ 0`, `log |Λ| > −1.4·30^{n+3} n^{4.5} D² (1 + log D)(1 + log B) A₁⋯Aₙ`,
`B ≥ max |bᵢ|`, `Aᵢ ≥ max(D h(αᵢ), |log αᵢ|, 0.16)`.
Transcription (faithful or weaker): `n = 3`, `D = 1`, `α₁ = t`, `α₂ = 3`, `α₃ = u/v`, `b₃ = 1`.
Then `A₁ = log t`, `A₂ = log 3`, `A₃ ≤ 1 + log max(u, v)` (the height of `u/v` and `|log(u/v)|` are
both `≤ log max(u, v)`), `B ≤ max(|b₁|, |b₂|) + 1`; the constant `1.4·30⁶·3^{4.5}·log t·log 3` is
absorbed into `C`.  (Baker–Wüstholz 1993 gives the same shape.)  Source not opened this lap (no
egress); the statement is quoted from memory of the standard form and needs a referee check of
the `A₃` normalisation (the only step that could matter: any `A₃ ≪ 1 + log max(u,v)` works). -/
def Literature.MatveevThreeLogs : Prop :=
  ∀ t : ℕ, 2 ≤ t → ∃ C : ℝ, 0 < C ∧ ∀ (b₁ b₂ : ℤ) (u v : ℕ), 1 ≤ u → 1 ≤ v →
    (b₁ : ℝ) * Real.log t + b₂ * Real.log 3 + Real.log ((u : ℝ) / v) ≠ 0 →
    Real.exp (-(C * (1 + Real.log (((max |b₁| |b₂| : ℤ) : ℝ) + 1)) *
        (1 + Real.log (max u v : ℕ)))) ≤
      |(b₁ : ℝ) * Real.log t + b₂ * Real.log 3 + Real.log ((u : ℝ) / v)|

/-- **Sparse identities have bounded exponent.**  An identity `tᵟ·U = V` between `K`-sparse
integers with `U ≠ 0` forces `δ ≤ exp(C(K+1)²)`. -/
def SparseIdentityBound (t : ℕ) : Prop :=
  ∃ C : ℝ, ∀ (K δ : ℕ) (U V : ℤ), IsSparse3 K U → IsSparse3 K V → U ≠ 0 →
    (t : ℤ) ^ δ * U = V → (δ : ℝ) ≤ Real.exp (C * (K + 1) ^ 2)

/-- **Sparse identities from Matveev (believed, 90%; the Diophantine leaf of the copy zone).**

English proof.  Write `T = tᵟ`, `λ = log₃ T`, and give each term of `U` the level `e + λ` and each
term of `V` the level `f` (all levels distinct: `λ` is irrational).  Order the at most `m = 2K`
terms by level, `ℓ₁ > ℓ₂ > ⋯`.  By strong induction on `m` we may assume no proper top part
splits off exactly (`T U_top = V_top` with the rest a smaller identity, `U_top ≠ 0`).  Cut below
the `j` top terms: `T U_top − V_top = V_bot − T U_bot`, the right side `≤ 2·3^{ℓ_{j+1}+1}`.  If
the top part has only `U`-terms or only `V`-terms, or `T U_top`, `V_top` have opposite signs, the
left side is `≥ 3^{ℓ_j − 1}`; otherwise it is `|V_top|·|e^Λ − 1|` with
`Λ = δ log t + (e_low − f_low) log 3 + log(U'/V')`, `U', V'` the top parts divided by their lowest
powers of 3 (so `max(|U'|, |V'|) ≤ 3^{s_j + 2}`, `s_j = ℓ₁ − ℓ_j`), and Matveev gives
`|Λ| ≥ exp(−C(1 + log B)(s_j + 3))`, `B ≲ δ + s_j + K`.  Hence the gaps obey
`ℓ_j − ℓ_{j+1} ≤ c₀ + c₁(1 + log B)(s_j + 3)`, so `s_m + 3 ≤ (c₂(1 + log B))^m`.  Finally
`V = T U` with `U ≠ 0` and `v₃(U) = v₃(V)` gives `λ ≤ s_m + 1`.  Solving
`δ log₃ t ≤ (c₂ log(δ + s_m))^{2K}` gives `δ ≤ exp(O(K log K)) ≤ exp(C(K+1)²)`.

Evidence (`scratch` probe `cluster_probe.py`, `t = 2`): with at most 2 changes the occurring `δ`
are `{1, 2, 3}` at `A = 30` and at `A = 40` (stable in `A`, as the lemma predicts); `t = 5`: `{1}`.
With 4 changes, `t = 2`: `δ ∈ {1..8}` at `A = 40` and `A = 56` (probe cut at `δ = 8`). -/
theorem sparseIdentityBound_of_matveev (hM : Literature.MatveevThreeLogs) {t : ℕ} (ht : 2 ≤ t)
    (h3 : ¬ 3 ∣ t) : SparseIdentityBound t := by
  sorry

/-- **Guard: base `9` (a power of 3) admits unbounded sparse identities** (`9ᵟ·1 = 3^{2δ}`). -/
theorem not_sparseIdentityBound_nine : ¬ SparseIdentityBound 9 := by
  rintro ⟨C, hC⟩
  obtain ⟨δ, hδ⟩ := exists_nat_gt (Real.exp (C * (1 + 1) ^ 2))
  have h1 : IsSparse3 1 1 := ⟨{0}, fun _ => 1, by simp, by simp, by simp⟩
  have h2 : IsSparse3 1 ((3 : ℤ) ^ (2 * δ)) :=
    ⟨{2 * δ}, fun _ => 1, by simp, by simp, by simp⟩
  have := hC 1 δ 1 _ h1 h2 one_ne_zero (by rw [pow_mul]; norm_num)
  push_cast at this
  linarith

/-- **Guard: `t = 1` admits unbounded sparse identities** (`1ᵟ·1 = 1`). -/
theorem not_sparseIdentityBound_one : ¬ SparseIdentityBound 1 := by
  rintro ⟨C, hC⟩
  obtain ⟨δ, hδ⟩ := exists_nat_gt (Real.exp (C * (1 + 1) ^ 2))
  have h1 : IsSparse3 1 1 := ⟨{0}, fun _ => 1, by simp, by simp, by simp⟩
  have := hC 1 δ 1 1 h1 h1 one_ne_zero (by simp)
  push_cast at this
  linarith

theorem not_three_dvd_of_abs_le_two {c : ℤ} (h0 : c ≠ 0) (h2 : |c| ≤ 2) : ¬ (3 : ℤ) ∣ c := by
  rintro ⟨k, rfl⟩
  have : k ≠ 0 := by rintro rfl; simp at h0
  have : 1 ≤ |k| := Int.one_le_abs this
  rw [abs_mul] at h2; norm_num at h2; linarith

theorem sparse_one_eq {X : ℤ} (hX : IsSparse3 1 X) (h0 : X ≠ 0) :
    ∃ c e, c ≠ 0 ∧ |c| ≤ 2 ∧ X = c * 3 ^ e := by
  obtain ⟨S, c, hS, hc, rfl⟩ := hX
  rcases Finset.card_le_one_iff_subset_singleton.1 hS with ⟨e, he⟩
  rcases Finset.subset_singleton_iff.1 he with rfl | rfl
  · simp at h0
  · exact ⟨c e, e, (hc e (by simp)).1, (hc e (by simp)).2, by simp⟩

/-- **Degenerate case `K ≤ 1` (proved, elementary).**  A single-term identity
`tᵟ·c·3ᵉ = c'·3^{e'}` with `3 ∤ t` forces `tᵟ ≤ 2`. -/
theorem pow_le_two_of_sparse_one {t δ : ℕ} (h3 : ¬ 3 ∣ t) {U V : ℤ} (hU : IsSparse3 1 U)
    (hV : IsSparse3 1 V) (hU0 : U ≠ 0) (hid : (t : ℤ) ^ δ * U = V) : t ^ δ ≤ 2 := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at h3
  have hV0 : V ≠ 0 := by rw [← hid]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht0)) hU0
  obtain ⟨c, e, hc0, hc2, rfl⟩ := sparse_one_eq hU hU0
  obtain ⟨c', e', hc0', hc2', rfl⟩ := sparse_one_eq hV hV0
  have h3t : ¬ (3 : ℤ) ∣ (t : ℤ) ^ δ := by
    intro h
    exact h3 (by exact_mod_cast Int.Prime.dvd_pow' Nat.prime_three h)
  have hp : Prime (3 : ℤ) := Int.prime_three
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exfalso
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have : (t : ℤ) ^ δ * c = c' * 3 ^ (j + 1) := by
      have h3e : (3 : ℤ) ^ e ≠ 0 := pow_ne_zero _ (by norm_num)
      apply mul_right_cancel₀ h3e
      rw [show e + j + 1 = (j + 1) + e by ring, pow_add] at hid; linarith [hid]
    have : (3 : ℤ) ∣ (t : ℤ) ^ δ * c := this ▸ Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
    rcases hp.dvd_or_dvd this with h | h
    · exact h3t h
    · exact not_three_dvd_of_abs_le_two hc0 hc2 h
  · subst heq
    have h3e : (3 : ℤ) ^ e ≠ 0 := pow_ne_zero _ (by norm_num)
    have : (t : ℤ) ^ δ * c = c' := mul_right_cancel₀ h3e (by rw [← hid]; ring)
    have h1 : (t : ℤ) ^ δ * |c| ≤ 2 := by
      rw [← abs_of_nonneg (by positivity : (0 : ℤ) ≤ (t : ℤ) ^ δ), ← abs_mul, this]; exact hc2'
    have h2 : 1 ≤ |c| := Int.one_le_abs hc0
    have : (t : ℤ) ^ δ ≤ 2 := by nlinarith [(by positivity : (0 : ℤ) ≤ (t : ℤ) ^ δ)]
    exact_mod_cast this
  · exfalso
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have : (t : ℤ) ^ δ * c * 3 ^ (j + 1) = c' := by
      have h3e : (3 : ℤ) ^ e' ≠ 0 := pow_ne_zero _ (by norm_num)
      apply mul_right_cancel₀ h3e
      rw [show e' + j + 1 = (j + 1) + e' by ring, pow_add] at hid; linarith [hid]
    exact not_three_dvd_of_abs_le_two hc0' hc2' (this ▸ Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _)

theorem three_pow_modEq_mod (A n : ℕ) : (3 : ℤ) ^ n ≡ 3 ^ (n % A) [ZMOD (3 ^ A - 1)] := by
  have h1 : (3 : ℤ) ^ A ≡ 1 [ZMOD (3 ^ A - 1)] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  conv_lhs => rw [← Nat.div_add_mod n A, pow_add, pow_mul]
  calc ((3 : ℤ) ^ A) ^ (n / A) * 3 ^ (n % A) ≡ 1 ^ (n / A) * 3 ^ (n % A) [ZMOD (3 ^ A - 1)] :=
        (h1.pow _).mul_right _
    _ = 3 ^ (n % A) := by simp

/-- A rotation avoiding a final arc. -/
theorem exists_rot {A g : ℕ} (hA : 1 ≤ A) (P : Finset ℕ)
    (hcard : P.card * g < A) : ∃ r < A, ∀ e ∈ P, (e + r) % A < A - g := by
  by_contra hcon
  push Not at hcon
  have hsub : range A ⊆ P.biUnion fun e => (range A).filter fun r => A - g ≤ (e + r) % A := by
    intro r hr
    obtain ⟨e, he, hle⟩ := hcon r (mem_range.1 hr)
    exact mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨hr, hle⟩⟩
  have hb : ∀ e ∈ P, ((range A).filter fun r => A - g ≤ (e + r) % A).card ≤ g := by
    intro e he
    have hinj : Set.InjOn (fun r => (e + r) % A) ((range A).filter fun r => A - g ≤ (e + r) % A) := by
      intro r₁ h₁ r₂ h₂ h
      simp only [coe_filter, mem_range] at h₁ h₂
      have := Nat.ModEq.add_left_cancel' e (show e + r₁ ≡ e + r₂ [MOD A] from h)
      exact Nat.ModEq.eq_of_lt_of_lt this h₁.1 h₂.1
    have := card_le_card_of_injOn _ (fun r hr => by
      simp only [coe_filter, mem_range] at hr
      exact Finset.mem_coe.2 (Finset.mem_Ico.2 ⟨hr.2, Nat.mod_lt _ (by omega)⟩) : Set.MapsTo (fun r => (e + r) % A) _ (Ico (A - g) A : Set ℕ)) hinj
    rw [Nat.card_Ico] at this; omega
  have := (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum hb))
  rw [card_range, sum_const, smul_eq_mul] at this
  nlinarith

theorem rot_inv {A e r : ℕ} (he : e < A) (hr : r < A) : ((e + r) % A + (A - r)) % A = e := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show e + r + (A - r) = e + A by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt he]

/-- Rotating a cyclic sparse representation. -/
theorem rot_sparse {A K r : ℕ} (hr : r < A) {S : Finset ℕ} {c : ℕ → ℤ} (hS : S ⊆ range A)
    (hK : S.card ≤ K) (hc : ∀ e ∈ S, c e ≠ 0 ∧ |c e| ≤ 2) :
    IsSparse3 K (∑ e ∈ S, c e * 3 ^ ((e + r) % A)) := by
  have hinj : Set.InjOn (fun e => (e + r) % A) S := by
    intro e₁ h₁ e₂ h₂ h
    have h1 := mem_range.1 (hS h₁); have h2 := mem_range.1 (hS h₂)
    rw [← rot_inv h1 hr, ← rot_inv h2 hr]; simp only at h; rw [h]
  refine ⟨S.image fun e => (e + r) % A, fun j => c ((j + (A - r)) % A),
    card_image_le.trans hK, ?_, ?_⟩
  · intro j hj
    obtain ⟨e, he, rfl⟩ := mem_image.1 hj
    dsimp only
    rw [rot_inv (mem_range.1 (hS he)) hr]; exact hc e he
  · rw [sum_image hinj]
    refine sum_congr rfl fun e he => ?_
    dsimp only
    rw [rot_inv (mem_range.1 (hS he)) hr]

theorem abs_sum_le_geom {n : ℕ} {S : Finset ℕ} {c : ℕ → ℤ} (hS : S ⊆ range n)
    (hc : ∀ e ∈ S, |c e| ≤ 2) : |∑ e ∈ S, c e * 3 ^ e| ≤ 3 ^ n - 1 := by
  calc |∑ e ∈ S, c e * 3 ^ e| ≤ ∑ e ∈ S, |c e * 3 ^ e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ S, 2 * (3 : ℤ) ^ e := sum_le_sum fun e he => by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ e)]
        exact mul_le_mul_of_nonneg_right (hc e he) (by positivity)
    _ ≤ ∑ e ∈ range n, 2 * (3 : ℤ) ^ e :=
        sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => by positivity
    _ = 3 ^ n - 1 := by
        rw [← mul_sum]
        have := geom_sum_mul (3 : ℤ) n
        linarith

/-- **Pairs of sparse points give a sparse identity (elementary; the combinatorial leaf of the
copy zone).**  If `y` and `y' ≡ T·y` are both cyclically `K`-sparse modulo `3^A − 1` and
`T + 2 ≤ 3^{⌊A/(2K+1)⌋}`, then `T·U = V` for some `K`-sparse integers `U, V`, with `U ≠ 0` unless
`3^A − 1 ∣ 2y`.

English proof.  The `≤ 2K` exponents of the two representations sit on the cycle `ℤ/A`; each
blocks `g = ⌊A/(2K+1)⌋` rotations, and `2K g < A`, so some rotation `r` moves all of them into
`[0, A − g)`.  Multiplying by `3^r` (`3^A ≡ 1`) gives integers `U ≡ 2·3^r y`, `V ≡ 2·3^r y'` with
`|U|, |V| < 3^{A−g}`, and `T U − V ≡ 0` with `|T U − V| < (T + 1)3^{A−g} ≤ 3^A − 1`, so
`T U = V`.  If `U = 0` then `2·3^r y ≡ 0`, and `3` is a unit mod `3^A − 1`. -/
theorem cyclic_pair_identity {A K T : ℕ} (hA : 1 ≤ A) {y y' : ℤ} (hy : CycSparse A K y)
    (hy' : CycSparse A K y') (hmod : y' ≡ T * y [ZMOD (3 ^ A - 1)])
    (hgap : T + 2 ≤ 3 ^ (A / (2 * K + 1))) :
    ∃ U V : ℤ, IsSparse3 K U ∧ IsSparse3 K V ∧ (T : ℤ) * U = V ∧
      (U = 0 → (3 ^ A - 1 : ℤ) ∣ 2 * y) := by
  obtain ⟨S, c, hS, hSK, hc, hyS⟩ := hy
  obtain ⟨S', c', hS', hSK', hc', hyS'⟩ := hy'
  set g := A / (2 * K + 1) with hg
  have hgA : g ≤ A := Nat.div_le_self _ _
  have hcard : (S ∪ S').card * g < A := by
    have h1 : (S ∪ S').card ≤ 2 * K := (card_union_le _ _).trans (by omega)
    have h2 : (2 * K + 1) * g ≤ A := by rw [hg]; exact Nat.mul_div_le A (2 * K + 1)
    rcases Nat.eq_zero_or_pos g with h3 | h3
    · rw [h3]; omega
    · have : (S ∪ S').card * g ≤ 2 * K * g := Nat.mul_le_mul_right _ h1
      nlinarith
  obtain ⟨r, hrA, hr⟩ := exists_rot hA (S ∪ S') hcard
  set U := ∑ e ∈ S, c e * 3 ^ ((e + r) % A)
  set V := ∑ e ∈ S', c' e * 3 ^ ((e + r) % A)
  have hmodU : U ≡ 3 ^ r * (2 * y) [ZMOD (3 ^ A - 1)] := by
    have : 3 ^ r * (2 * y) ≡ 3 ^ r * ∑ e ∈ S, c e * 3 ^ e [ZMOD (3 ^ A - 1)] := hyS.mul_left _
    refine Int.ModEq.trans ?_ this.symm
    rw [mul_sum]
    refine Int.ModEq.sum fun e _ => ?_
    rw [show (3 : ℤ) ^ r * (c e * 3 ^ e) = c e * 3 ^ (e + r) by ring]
    exact ((three_pow_modEq_mod A (e + r)).symm).mul_left _
  have hmodV : V ≡ 3 ^ r * (2 * y') [ZMOD (3 ^ A - 1)] := by
    have : 3 ^ r * (2 * y') ≡ 3 ^ r * ∑ e ∈ S', c' e * 3 ^ e [ZMOD (3 ^ A - 1)] := hyS'.mul_left _
    refine Int.ModEq.trans ?_ this.symm
    rw [mul_sum]
    refine Int.ModEq.sum fun e _ => ?_
    rw [show (3 : ℤ) ^ r * (c' e * 3 ^ e) = c' e * 3 ^ (e + r) by ring]
    exact ((three_pow_modEq_mod A (e + r)).symm).mul_left _
  -- bounds via the rotated representations
  have hbound : ∀ (P : Finset ℕ) (d : ℕ → ℤ), P ⊆ S ∪ S' → (∀ e ∈ P, |d e| ≤ 2) →
      |∑ e ∈ P, d e * 3 ^ ((e + r) % A)| ≤ 3 ^ (A - g) - 1 := by
    intro P d hP hd
    have hPA : P ⊆ range A := hP.trans (union_subset hS hS')
    have hinj : Set.InjOn (fun e => (e + r) % A) P := by
      intro e₁ h₁ e₂ h₂ h
      have h1 := mem_range.1 (hPA h₁); have h2 := mem_range.1 (hPA h₂)
      rw [← rot_inv h1 hrA, ← rot_inv h2 hrA]; simp only at h; rw [h]
    have e1 : ∑ e ∈ P, d e * 3 ^ ((e + r) % A) =
        ∑ j ∈ P.image (fun e => (e + r) % A), d ((j + (A - r)) % A) * 3 ^ j := by
      rw [sum_image hinj]
      refine sum_congr rfl fun e he => ?_
      rw [rot_inv (mem_range.1 (hPA he)) hrA]
    rw [e1]
    refine abs_sum_le_geom (fun j hj => ?_) (fun j hj => ?_)
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hj
      exact mem_range.2 (hr e (hP he))
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hj
      rw [rot_inv (mem_range.1 (hPA he)) hrA]; exact hd e he
  have hU := hbound S c subset_union_left fun e he => (hc e he).2
  have hV := hbound S' c' subset_union_right fun e he => (hc' e he).2
  have hid : (T : ℤ) * U = V := by
    have hdvd : (3 ^ A - 1 : ℤ) ∣ (T : ℤ) * U - V := by
      have : (T : ℤ) * U - V ≡ T * (3 ^ r * (2 * y)) - 3 ^ r * (2 * y') [ZMOD (3 ^ A - 1)] :=
        (hmodU.mul_left _).sub hmodV
      have h2 : (T : ℤ) * (3 ^ r * (2 * y)) - 3 ^ r * (2 * y') ≡ 0 [ZMOD (3 ^ A - 1)] := by
        have : 3 ^ r * (2 * y') ≡ 3 ^ r * (2 * (T * y)) [ZMOD (3 ^ A - 1)] :=
          (hmod.mul_left 2).mul_left _
        have h3 := (Int.ModEq.refl ((T : ℤ) * (3 ^ r * (2 * y)))).sub this
        rw [show (T : ℤ) * (3 ^ r * (2 * y)) - 3 ^ r * (2 * (T * y)) = 0 by ring] at h3
        exact h3
      exact Int.ModEq.dvd ((this.trans h2).symm) |>.trans (by simp)
    have hlt : |(T : ℤ) * U - V| < 3 ^ A - 1 := by
      have hT0 : (0 : ℤ) ≤ T := by positivity
      have h1 : |(T : ℤ) * U - V| ≤ T * (3 ^ (A - g) - 1) + (3 ^ (A - g) - 1) := by
        calc |(T : ℤ) * U - V| ≤ |(T : ℤ) * U| + |V| := abs_sub _ _
          _ = T * |U| + |V| := by rw [abs_mul, abs_of_nonneg hT0]
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hU hT0) hV
      have hg3 : ((T : ℤ) + 2) ≤ 3 ^ g := by exact_mod_cast hgap
      have hAg : (3 : ℤ) ^ A = 3 ^ g * 3 ^ (A - g) := by rw [← pow_add]; congr 1; omega
      have hpos : (1 : ℤ) ≤ 3 ^ (A - g) := one_le_pow₀ (by norm_num)
      nlinarith
    exact Int.eq_zero_of_abs_lt_dvd hdvd hlt |> fun h => by linarith
  refine ⟨U, V, rot_sparse hrA hS hSK hc, rot_sparse hrA hS' hSK' hc', hid, fun hU0 => ?_⟩
  have h1 : (3 ^ A - 1 : ℤ) ∣ 3 ^ r * (2 * y) := by
    have := hmodU.symm; rw [hU0] at this; exact Int.ModEq.dvd this.symm |>.trans (by simp)
  have hcop : IsCoprime ((3 : ℤ) ^ r) (3 ^ A - 1) := by
    refine IsCoprime.pow_left ⟨3 ^ (A - 1), -1, ?_⟩
    rw [show (3 : ℤ) ^ (A - 1) * 3 = 3 ^ A by rw [← pow_succ]; congr 1; omega]; ring
  exact hcop.symm.dvd_of_dvd_mul_left h1

end NormalNumbers.SparseIdentity
