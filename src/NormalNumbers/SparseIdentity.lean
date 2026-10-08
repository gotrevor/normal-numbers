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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

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

theorem sum_ne_zero_of_nonempty {S : Finset ℕ} {c : ℕ → ℤ} (hc : ∀ e ∈ S, c e ≠ 0 ∧ |c e| ≤ 2)
    (hS : S.Nonempty) : ∑ e ∈ S, c e * 3 ^ e ≠ 0 := by
  intro h0
  set e0 := S.min' hS
  have he0 : e0 ∈ S := S.min'_mem hS
  have hrest : (3 : ℤ) ^ (e0 + 1) ∣ ∑ e ∈ S.erase e0, c e * 3 ^ e := by
    refine dvd_sum fun e he => Dvd.dvd.mul_left (pow_dvd_pow 3 ?_) _
    have := S.min'_le e (mem_of_mem_erase he)
    have := ne_of_mem_erase he
    omega
  rw [← add_sum_erase _ _ he0] at h0
  have : (3 : ℤ) ^ (e0 + 1) ∣ c e0 * 3 ^ e0 := by
    have : c e0 * 3 ^ e0 = -∑ e ∈ S.erase e0, c e * 3 ^ e := by linarith
    rw [this]; exact hrest.neg_right
  rw [pow_succ, mul_comm (c e0)] at this
  exact not_three_dvd_of_abs_le_two (hc e0 he0).1 (hc e0 he0).2
    ((mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).1 this)

theorem pow_dvd_sum {S : Finset ℕ} {c : ℕ → ℤ} {a : ℕ} (h : ∀ e ∈ S, a ≤ e) :
    (3 : ℤ) ^ a ∣ ∑ e ∈ S, c e * 3 ^ e :=
  dvd_sum fun e he => Dvd.dvd.mul_left (pow_dvd_pow 3 (h e he)) _

theorem abs_sum_le_rpow {S : Finset ℕ} {c : ℕ → ℤ} (hc : ∀ e ∈ S, |c e| ≤ 2) {x : ℝ}
    (h : ∀ e ∈ S, (e : ℝ) ≤ x) : ((|∑ e ∈ S, c e * 3 ^ e| : ℤ) : ℝ) ≤ (3 : ℝ) ^ (x + 1) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨e1, he1⟩
  · simp; positivity
  have hx : 0 ≤ x := le_trans (Nat.cast_nonneg _) (h e1 he1)
  have hsub : S ⊆ range (⌊x⌋₊ + 1) := fun e he =>
    mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor (h e he)))
  have h1 := abs_sum_le_geom hsub hc
  have h2 : ((|∑ e ∈ S, c e * 3 ^ e| : ℤ) : ℝ) ≤ (3 : ℝ) ^ (⌊x⌋₊ + 1) := by
    have : ((|∑ e ∈ S, c e * 3 ^ e| : ℤ) : ℝ) ≤ ((3 ^ (⌊x⌋₊ + 1) - 1 : ℤ) : ℝ) := Int.cast_le.2 h1
    rw [Int.cast_sub, Int.cast_pow] at this; push_cast at this ⊢; linarith
  calc ((|∑ e ∈ S, c e * 3 ^ e| : ℤ) : ℝ) ≤ (3 : ℝ) ^ (⌊x⌋₊ + 1) := h2
    _ = (3 : ℝ) ^ ((⌊x⌋₊ : ℝ) + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ (3 : ℝ) ^ (x + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith [Nat.floor_le hx])

theorem sub_ge_min_mul_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    min p q * |Real.log p - Real.log q| ≤ |p - q| := by
  rcases le_total q p with h | h
  · rw [min_eq_right h, abs_of_nonneg (by linarith [Real.log_le_log hq h]), abs_of_nonneg (by linarith)]
    have := Real.log_le_sub_one_of_pos (div_pos hp hq)
    rw [Real.log_div hp.ne' hq.ne'] at this
    have : q * (Real.log p - Real.log q) ≤ q * (p / q - 1) := mul_le_mul_of_nonneg_left this hq.le
    have e : q * (p / q - 1) = p - q := by field_simp
    linarith
  · rw [min_eq_left h, abs_of_nonpos (by linarith [Real.log_le_log hp h]), abs_of_nonpos (by linarith)]
    have := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at this
    have : p * (Real.log q - Real.log p) ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left this hp.le
    have e : p * (q / p - 1) = q - p := by field_simp
    linarith

/-- Endgame: `κx ≤ 2(3 + C + C log((1+κ)x+2))^m` forces `x ≤ exp(C'(m+1)²)`. -/
theorem endgame {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (m : ℕ) (x : ℝ), 0 ≤ x →
    κ * x ≤ 2 * (3 + C + C * Real.log ((1 + κ) * x + 2)) ^ m → x ≤ Real.exp (C' * (m + 1) ^ 2) := by
  set α0 := Real.log ((1 + κ) * (2 / κ) + 2)
  set α1 := Real.log (3 + C)
  have hα0' : 0 ≤ (1 + κ) * (2 / κ) := by positivity
  have hα0 : 0 ≤ α0 := Real.log_nonneg (by linarith)
  have hα1 : 0 ≤ α1 := Real.log_nonneg (by linarith)
  refine ⟨2 * (1 + α0 + α1) + 4, by positivity, fun m x hx h => ?_⟩
  set w := (1 + κ) * x + 2
  have hw' : 0 ≤ (1 + κ) * x := by positivity
  have hw : 2 ≤ w := by linarith
  set y := Real.log w
  have hy : 0 ≤ y := Real.log_nonneg (by linarith)
  have hfac : 3 + C + C * y ≤ (3 + C) * (1 + y) := by nlinarith
  have hx2 : x ≤ (2 / κ) * ((3 + C) * (1 + y)) ^ m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    calc x * κ ≤ 2 * (3 + C + C * y) ^ m := by linarith
      _ ≤ 2 * ((3 + C) * (1 + y)) ^ m := by
        gcongr
  have hM : 1 ≤ ((3 + C) * (1 + y)) ^ m := one_le_pow₀ (by nlinarith)
  have hw2 : w ≤ ((1 + κ) * (2 / κ) + 2) * ((3 + C) * (1 + y)) ^ m := by
    have : (1 + κ) * x ≤ (1 + κ) * ((2 / κ) * ((3 + C) * (1 + y)) ^ m) :=
      mul_le_mul_of_nonneg_left hx2 (by linarith)
    nlinarith
  have hylog : y ≤ α0 + m * α1 + m * Real.log (1 + y) := by
    have := Real.log_le_log (by linarith) hw2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_mul (by linarith) (by linarith)] at this
    linarith
  set z := Real.sqrt (1 + y)
  have hz : z ^ 2 = 1 + y := Real.sq_sqrt (by linarith)
  have hz0 : 0 < z := Real.sqrt_pos.2 (by linarith)
  have hlz : Real.log (1 + y) ≤ 2 * z := by
    rw [← hz, Real.log_pow]; push_cast
    have := Real.log_le_sub_one_of_pos hz0; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have key : y ≤ α0 + m * α1 + m * (2 * z) := by nlinarith
  have hz2 : z ^ 2 ≤ (2 * (1 + α0 + α1) + 4) * ((m : ℝ) + 1) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (m + 1) ^ 2 := by nlinarith
    have h2 : (m : ℝ) ≤ (m + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (z - 2 * m), mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 + α0),
      mul_le_mul_of_nonneg_left h2 hα1]
  calc x ≤ w := by nlinarith
    _ = Real.exp y := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (z ^ 2) := Real.exp_le_exp.2 (by linarith)
    _ ≤ _ := Real.exp_le_exp.2 hz2


theorem abs_ge_of_dvd {b : ℕ} {V : ℤ} (hV : V ≠ 0) (h : (3 : ℤ) ^ b ∣ V) :
    (3 : ℝ) ^ b ≤ |(V : ℝ)| := by
  have := Int.le_of_dvd (abs_pos.2 hV) ((dvd_abs _ _).2 h)
  have : ((3 ^ b : ℤ) : ℝ) ≤ ((|V| : ℤ) : ℝ) := Int.cast_le.2 this
  push_cast at this; exact this

/-- Lower bound for a nonzero top-part difference (Matveev step). -/
theorem top_lower {t δ : ℕ} {lam C : ℝ} (hlam : (3 : ℝ) ^ lam = ((t ^ δ : ℕ) : ℝ)) (hlam0 : 0 ≤ lam)
    (hC : 0 < C)
    (hM : ∀ (b₁ b₂ : ℤ) (u v : ℕ), 1 ≤ u → 1 ≤ v →
      (b₁ : ℝ) * Real.log t + b₂ * Real.log 3 + Real.log ((u : ℝ) / v) ≠ 0 →
      Real.exp (-(C * (1 + Real.log (((max |b₁| |b₂| : ℤ) : ℝ) + 1)) *
          (1 + Real.log (max u v : ℕ)))) ≤
        |(b₁ : ℝ) * Real.log t + b₂ * Real.log 3 + Real.log ((u : ℝ) / v)|)
    {S S' : Finset ℕ} {c c' : ℕ → ℤ} (hc : ∀ e ∈ S, c e ≠ 0 ∧ |c e| ≤ 2)
    (hc' : ∀ e ∈ S', c' e ≠ 0 ∧ |c' e| ≤ 2) {θ s : ℝ} (hθ : 0 ≤ θ) (hs : 0 ≤ s)
    (hS : ∀ e ∈ S, θ ≤ e + lam ∧ e + lam ≤ θ + s) (hS' : ∀ f ∈ S', θ ≤ f ∧ (f : ℝ) ≤ θ + s)
    (hD : ((t ^ δ : ℕ) : ℤ) * (∑ e ∈ S, c e * 3 ^ e) - ∑ f ∈ S', c' f * 3 ^ f ≠ 0) :
    (3 : ℝ) ^ θ * Real.exp (-(C * (1 + Real.log (δ + lam + 2)) * (1 + (s + 1) * Real.log 3))) ≤
      |((((t ^ δ : ℕ) : ℤ) * (∑ e ∈ S, c e * 3 ^ e) - ∑ f ∈ S', c' f * 3 ^ f : ℤ) : ℝ)| := by
  set T : ℕ := t ^ δ with hTdef
  set U := ∑ e ∈ S, c e * 3 ^ e
  set V := ∑ f ∈ S', c' f * 3 ^ f
  have hT : (0 : ℝ) < T := by rw [← hlam]; positivity
  set ε := Real.exp (-(C * (1 + Real.log (δ + lam + 2)) * (1 + (s + 1) * Real.log 3)))
  have hε1 : ε ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have : 0 ≤ Real.log (δ + lam + 2) := Real.log_nonneg (by have := (Nat.cast_nonneg δ : (0:ℝ) ≤ δ); linarith)
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have : 0 ≤ (s + 1) * Real.log 3 := by positivity
    positivity
  have h3θ : (0 : ℝ) < 3 ^ θ := by positivity
  set a := ⌈θ - lam⌉₊
  set b := ⌈θ⌉₊
  have ha : ∀ e ∈ S, a ≤ e := fun e he => Nat.ceil_le.2 (by linarith [(hS e he).1])
  have hb : ∀ f ∈ S', b ≤ f := fun f hf => Nat.ceil_le.2 (hS' f hf).1
  obtain ⟨u0, hu0⟩ := pow_dvd_sum (c := c) ha
  obtain ⟨v0, hv0⟩ := pow_dvd_sum (c := c') hb
  replace hu0 : U = 3 ^ a * u0 := hu0
  replace hv0 : V = 3 ^ b * v0 := hv0
  -- lower bounds for nonzero parts
  have hXlow : U ≠ 0 → 3 ^ θ ≤ |((T * U : ℤ) : ℝ)| := by
    intro hU
    have h1 := abs_ge_of_dvd hU ⟨u0, hu0⟩
    have h2 : (3 : ℝ) ^ θ ≤ T * 3 ^ a := by
      rw [← hlam, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Nat.le_ceil (θ - lam)])
    push_cast; rw [abs_mul, abs_of_pos hT]
    exact h2.trans (mul_le_mul_of_nonneg_left h1 hT.le)
  have hYlow : V ≠ 0 → 3 ^ θ ≤ |(V : ℝ)| := by
    intro hV
    have h1 := abs_ge_of_dvd hV ⟨v0, hv0⟩
    refine le_trans ?_ h1
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil θ)
  have hDc : ((((T : ℤ) * U - V : ℤ)) : ℝ) = ((T * U : ℤ) : ℝ) - (V : ℝ) := by push_cast; ring
  rw [hDc]
  have h3ε : (3 : ℝ) ^ θ * ε ≤ 3 ^ θ := mul_le_of_le_one_right h3θ.le hε1
  by_cases hU : U = 0
  · have hV : V ≠ 0 := by intro hV; apply hD; rw [hU, hV]; simp
    rw [hU]; simp only [mul_zero, Int.cast_zero, zero_sub, abs_neg]
    exact h3ε.trans (hYlow hV)
  by_cases hV : V = 0
  · rw [hV]; simp only [Int.cast_zero, sub_zero]
    exact h3ε.trans (hXlow hU)
  set X : ℝ := ((T * U : ℤ) : ℝ)
  set Y : ℝ := (V : ℝ)
  have hX := hXlow hU
  have hY := hYlow hV
  by_cases hXY : |X| = |Y|
  · have hne : X ≠ Y := by
      intro h; apply hD; rw [sub_eq_zero]; exact_mod_cast (show ((T * U : ℤ) : ℝ) = (V : ℝ) from h)
    rcases abs_eq_abs.1 hXY with h | h
    · exact absurd h hne
    · rw [h, show -Y - Y = -(2 * Y) by ring, abs_neg, abs_mul]
      norm_num; linarith [abs_nonneg Y]
  -- the Matveev case
  have hu0' : u0 ≠ 0 := by rintro rfl; simp at hu0; exact hU hu0
  have hv0' : v0 ≠ 0 := by rintro rfl; simp at hv0; exact hV hv0
  set u := u0.natAbs
  set v := v0.natAbs
  have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hu0')
  have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hv0')
  have hXe : |X| = T * 3 ^ a * u := by
    simp only [X]; rw [hu0]; push_cast
    rw [abs_mul, abs_mul, abs_of_pos hT, abs_of_pos (by positivity : (0:ℝ) < 3 ^ a)]
    simp [u, Nat.cast_natAbs, mul_assoc]
  have hYe : |Y| = 3 ^ b * v := by
    simp only [Y]; rw [hv0]; push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 ^ b)]
    simp [v, Nat.cast_natAbs]
  have hu1r : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hv1r : (1 : ℝ) ≤ v := by exact_mod_cast hv1
  have hlogT : Real.log T = δ * Real.log t := by rw [hTdef, Nat.cast_pow, Real.log_pow]
  set Λ : ℝ := (δ : ℤ) * Real.log t + ((a : ℤ) - b : ℤ) * Real.log 3 + Real.log ((u : ℝ) / v)
  have hΛ : Λ = Real.log |X| - Real.log |Y| := by
    have hTa : (0:ℝ) < T * 3 ^ a := by positivity
    simp only [Λ]
    rw [hXe, hYe, Real.log_mul hTa.ne' (by linarith), Real.log_mul hT.ne' (by positivity),
      Real.log_mul (by positivity) (by linarith), Real.log_div (by linarith) (by linarith), hlogT,
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have hXpos : 0 < |X| := lt_of_lt_of_le h3θ hX
  have hYpos : 0 < |Y| := lt_of_lt_of_le h3θ hY
  have hΛ0 : Λ ≠ 0 := by
    rw [hΛ, sub_ne_zero]; intro h
    exact hXY (Real.log_injOn_pos (Set.mem_Ioi.2 hXpos) (Set.mem_Ioi.2 hYpos) h)
  have hMat := hM δ (a - b) u v hu1 hv1 hΛ0
  -- bounds on the Matveev parameters
  have hab : |((a : ℤ) - b : ℤ)| ≤ (lam + 1 : ℝ) := by
    have h1 : (θ - lam : ℝ) ≤ a := Nat.le_ceil _
    have h2 : (a : ℝ) < max (θ - lam) 0 + 1 := by
      rcases le_total (θ - lam) 0 with h | h
      · rw [max_eq_right h]; simp [a, Nat.ceil_eq_zero.2 h]
      · rw [max_eq_left h]; exact Nat.ceil_lt_add_one h
    have h3 : (θ : ℝ) ≤ b := Nat.le_ceil _
    have h4 : (b : ℝ) < θ + 1 := Nat.ceil_lt_add_one hθ
    push_cast; rw [abs_le]
    constructor
    · linarith
    · rcases le_total (θ - lam) 0 with h | h
      · rw [max_eq_right h] at h2; linarith
      · rw [max_eq_left h] at h2; linarith
  have hB : (((max |(δ : ℤ)| |((a : ℤ) - b : ℤ)| : ℤ) : ℝ) + 1) ≤ δ + lam + 2 := by
    push_cast
    rcases le_total |(δ : ℝ)| |((a : ℝ) - b)| with h | h
    · rw [max_eq_right h]; have : (0:ℝ) ≤ δ := Nat.cast_nonneg _
      push_cast at hab; linarith
    · rw [max_eq_left h, abs_of_nonneg (Nat.cast_nonneg _)]; linarith
  have hUle : (u : ℝ) ≤ 3 ^ (s + 1) := by
    have h1 := abs_sum_le_rpow (c := c) (fun e he => (hc e he).2) (x := θ + s - lam)
      (fun e he => by linarith [(hS e he).2])
    change ((|U| : ℤ) : ℝ) ≤ _ at h1
    rw [hu0] at h1; push_cast at h1
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 ^ a)] at h1
    have h2 : |(u0 : ℝ)| = u := by simp [u, Nat.cast_natAbs]
    rw [h2] at h1
    have h3 : (3 : ℝ) ^ (θ + s - lam + 1) = 3 ^ (s + 1) * 3 ^ (θ - lam) := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    have h4 : (3 : ℝ) ^ (θ - lam) ≤ 3 ^ a := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    have h5 : (0 : ℝ) < 3 ^ a := by positivity
    nlinarith [(by positivity : (0:ℝ) < 3 ^ (s + 1))]
  have hVle : (v : ℝ) ≤ 3 ^ (s + 1) := by
    have h1 := abs_sum_le_rpow (c := c') (fun e he => (hc' e he).2) (x := θ + s)
      (fun e he => (hS' e he).2)
    change ((|V| : ℤ) : ℝ) ≤ _ at h1
    rw [hv0] at h1; push_cast at h1
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 ^ b)] at h1
    have h2 : |(v0 : ℝ)| = v := by simp [v, Nat.cast_natAbs]
    rw [h2] at h1
    have h3 : (3 : ℝ) ^ (θ + s + 1) = 3 ^ (s + 1) * 3 ^ θ := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    have h4 : (3 : ℝ) ^ θ ≤ 3 ^ b := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    have h5 : (0 : ℝ) < 3 ^ b := by positivity
    nlinarith [(by positivity : (0:ℝ) < 3 ^ (s + 1))]
  have hmax : Real.log ((max u v : ℕ) : ℝ) ≤ (s + 1) * Real.log 3 := by
    rw [← Real.log_rpow (by norm_num)]
    have hmv : (1:ℝ) ≤ ((max u v : ℕ) : ℝ) := by exact_mod_cast le_max_of_le_left hu1
    apply Real.log_le_log (by linarith)
    push_cast; exact max_le hUle hVle
  have hεΛ : ε ≤ |Λ| := by
    refine le_trans ?_ hMat
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    have hM0 : (0:ℝ) ≤ ((max |(δ : ℤ)| |((a : ℤ) - b : ℤ)| : ℤ) : ℝ) := by
      have : (0:ℤ) ≤ max |(δ : ℤ)| |((a : ℤ) - b : ℤ)| := le_max_of_le_left (abs_nonneg _)
      exact_mod_cast this
    have hl1 : Real.log (((max |(δ : ℤ)| |((a : ℤ) - b : ℤ)| : ℤ) : ℝ) + 1) ≤ Real.log (δ + lam + 2) :=
      Real.log_le_log (by linarith) hB
    have hl0 : 0 ≤ Real.log (((max |(δ : ℤ)| |((a : ℤ) - b : ℤ)| : ℤ) : ℝ) + 1) :=
      Real.log_nonneg (by linarith)
    have hm0 : 0 ≤ Real.log ((max u v : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast le_max_of_le_left hu1)
    have := mul_le_mul (add_le_add_left hl1 1) (add_le_add_left hmax 1) (by linarith) (by linarith)
    nlinarith
  calc (3 : ℝ) ^ θ * ε ≤ min |X| |Y| * |Λ| :=
        mul_le_mul (le_min hX hY) hεΛ (Real.exp_pos _).le (le_min hXpos.le hYpos.le)
    _ = min |X| |Y| * abs (Real.log |X| - Real.log |Y|) := by rw [hΛ]
    _ ≤ abs (|X| - |Y|) := sub_ge_min_mul_log hXpos hYpos
    _ ≤ |X - Y| := abs_abs_sub_abs_le_abs_sub X Y


theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le)

/-- **Gap step.**  Below a non-splitting top cut at level `θ`, the next level `ν` is within
`2 + C L (s + 2)` of `θ`. -/
theorem gap_step {t δ : ℕ} {lam C : ℝ} (hlam : (3 : ℝ) ^ lam = ((t ^ δ : ℕ) : ℝ)) (hlam0 : 0 ≤ lam)
    (hC : 0 < C)
    (hM : ∀ (b₁ b₂ : ℤ) (u v : ℕ), 1 ≤ u → 1 ≤ v →
      (b₁ : ℝ) * Real.log t + b₂ * Real.log 3 + Real.log ((u : ℝ) / v) ≠ 0 →
      Real.exp (-(C * (1 + Real.log (((max |b₁| |b₂| : ℤ) : ℝ) + 1)) *
          (1 + Real.log (max u v : ℕ)))) ≤
        |(b₁ : ℝ) * Real.log t + b₂ * Real.log 3 + Real.log ((u : ℝ) / v)|)
    {S S' : Finset ℕ} {c c' : ℕ → ℤ} (hc : ∀ e ∈ S, c e ≠ 0 ∧ |c e| ≤ 2)
    (hc' : ∀ e ∈ S', c' e ≠ 0 ∧ |c' e| ≤ 2)
    (hid : ((t ^ δ : ℕ) : ℤ) * (∑ e ∈ S, c e * 3 ^ e) = ∑ f ∈ S', c' f * 3 ^ f)
    {θ s ν : ℝ} (hθ : 0 ≤ θ) (hs : 0 ≤ s)
    (hS : ∀ e ∈ S, θ ≤ e + lam → e + lam ≤ θ + s) (hS' : ∀ f ∈ S', θ ≤ f → (f : ℝ) ≤ θ + s)
    (hSb : ∀ e ∈ S, e + lam < θ → e + lam ≤ ν) (hSb' : ∀ f ∈ S', (f : ℝ) < θ → (f : ℝ) ≤ ν)
    (hD : ((t ^ δ : ℕ) : ℤ) * (∑ e ∈ S.filter (fun e : ℕ => θ ≤ (e : ℝ) + lam), c e * 3 ^ e) -
      ∑ f ∈ S'.filter (fun f : ℕ => θ ≤ (f : ℝ)), c' f * 3 ^ f ≠ 0) :
    θ - ν ≤ 2 + C * (1 + Real.log (δ + lam + 2)) * (s + 2) := by
  set T : ℕ := t ^ δ with hTdef
  have hT : (0 : ℝ) < T := by rw [← hlam]; positivity
  have hlow := top_lower hlam hlam0 hC hM (S := S.filter (fun e : ℕ => θ ≤ (e : ℝ) + lam))
    (S' := S'.filter (fun f : ℕ => θ ≤ (f : ℝ))) (fun e he => hc e (mem_filter.1 he).1)
    (fun e he => hc' e (mem_filter.1 he).1) hθ hs
    (fun e he => ⟨(mem_filter.1 he).2, hS e (mem_filter.1 he).1 (mem_filter.1 he).2⟩)
    (fun f hf => ⟨(mem_filter.1 hf).2, hS' f (mem_filter.1 hf).1 (mem_filter.1 hf).2⟩) hD
  -- bottom parts
  have hUb := abs_sum_le_rpow (S := S.filter (fun e : ℕ => ¬ θ ≤ (e : ℝ) + lam)) (c := c)
    (fun e he => (hc e (mem_filter.1 he).1).2) (x := ν - lam)
    (fun e he => by have := hSb e (mem_filter.1 he).1 (not_le.1 (mem_filter.1 he).2); linarith)
  have hVb := abs_sum_le_rpow (S := S'.filter (fun f : ℕ => ¬ θ ≤ (f : ℝ))) (c := c')
    (fun e he => (hc' e (mem_filter.1 he).1).2) (x := ν)
    (fun f hf => hSb' f (mem_filter.1 hf).1 (not_le.1 (mem_filter.1 hf).2))
  have hsplit : (T : ℤ) * (∑ e ∈ S.filter (fun e : ℕ => θ ≤ (e : ℝ) + lam), c e * 3 ^ e) -
      ∑ f ∈ S'.filter (fun f : ℕ => θ ≤ (f : ℝ)), c' f * 3 ^ f =
      ∑ f ∈ S'.filter (fun f : ℕ => ¬ θ ≤ (f : ℝ)), c' f * 3 ^ f -
      (T : ℤ) * ∑ e ∈ S.filter (fun e : ℕ => ¬ θ ≤ (e : ℝ) + lam), c e * 3 ^ e := by
    have h1 := sum_filter_add_sum_filter_not S (fun e : ℕ => θ ≤ (e : ℝ) + lam) (fun e => c e * 3 ^ e)
    have h2 := sum_filter_add_sum_filter_not S' (fun f : ℕ => θ ≤ (f : ℝ)) (fun f => c' f * 3 ^ f)
    rw [← h1, ← h2] at hid
    linear_combination hid
  rw [hsplit] at hlow
  push_cast at hlow hUb hVb
  have hTb : (T : ℝ) * (3 : ℝ) ^ (ν - lam + 1) = 3 ^ (ν + 1) := by
    rw [← hlam, ← Real.rpow_add (by norm_num)]; ring_nf
  have hbot : (3 : ℝ) ^ θ * Real.exp (-(C * (1 + Real.log (δ + lam + 2)) * (1 + (s + 1) * Real.log 3)))
      ≤ 6 * 3 ^ ν := by
    refine hlow.trans ((abs_sub _ _).trans ?_)
    rw [abs_mul, abs_of_pos hT]
    have := mul_le_mul_of_nonneg_left hUb hT.le
    rw [hTb] at this
    have h3 : (3 : ℝ) ^ (ν + 1) = 3 * 3 ^ ν := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
    linarith
  -- take logs
  have hl := Real.log_le_log (by positivity) hbot
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_mul (by norm_num)
    (by positivity), Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hl
  have h6 : Real.log 6 ≤ 2 * Real.log 3 := by
    rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hL3 := one_le_log_three
  have hL0 : 0 ≤ Real.log (δ + lam + 2) := Real.log_nonneg (by
    have := (Nat.cast_nonneg δ : (0:ℝ) ≤ δ); linarith)
  set L := C * (1 + Real.log (δ + lam + 2))
  have hLpos : 0 ≤ L := by positivity
  -- (θ - ν) log 3 ≤ log 6 + L (1 + (s+1) log 3)
  have key : (θ - ν) * Real.log 3 ≤ (2 + L * (s + 2)) * Real.log 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hL3 hLpos]
  exact le_of_mul_le_mul_right key (by linarith)


/-- A top part that splits exactly forces `λ ≤` its level span: some `V`-exponent lies at or below
some `U`-exponent. -/
theorem exists_le_of_split {T : ℤ} (h3T : ¬ (3 : ℤ) ∣ T) {S S' : Finset ℕ} {c c' : ℕ → ℤ}
    (hc : ∀ e ∈ S, c e ≠ 0 ∧ |c e| ≤ 2) (hS : S.Nonempty)
    (hid : T * (∑ e ∈ S, c e * 3 ^ e) = ∑ f ∈ S', c' f * 3 ^ f) :
    ∃ e ∈ S, ∃ f ∈ S', f ≤ e := by
  by_contra hcon
  push Not at hcon
  set E := S.max' hS
  have hE : ∀ f ∈ S', E + 1 ≤ f := fun f hf => hcon E (S.max'_mem hS) f hf
  have h1 : (3 : ℤ) ^ (E + 1) ∣ T * ∑ e ∈ S, c e * 3 ^ e := hid ▸ pow_dvd_sum hE
  have hcop : IsCoprime ((3 : ℤ) ^ (E + 1)) T :=
    ((Int.prime_three.coprime_iff_not_dvd).2 h3T).pow_left
  have h2 := hcop.dvd_of_dvd_mul_left h1
  have hsub : S ⊆ range (E + 1) := fun e he => mem_range.2 (Nat.lt_succ_of_le (S.le_max' e he))
  have h3 := abs_sum_le_geom hsub (fun e he => (hc e he).2)
  have h4 : ∑ e ∈ S, c e * 3 ^ e = 0 :=
    Int.eq_zero_of_abs_lt_dvd h2 (by linarith)
  exact sum_ne_zero_of_nonempty hc hS h4

/-- **Sparse identities from Matveev (PROVED from the cited Prop; the Diophantine leaf of the copy zone).**

Proof (as formalized: `top_lower`, `gap_step`, `exists_le_of_split`, `endgame`; the split case
is handled by taking the *highest* exactly-splitting cut `θ*` instead of a strong induction).  Write `T = tᵟ`, `λ = log₃ T`, and give each term of `U` the level `e + λ` and each
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
  obtain ⟨C, hC, hCb⟩ := hM t ht
  have ht0 : (0 : ℝ) < t := by have : (2 : ℝ) ≤ t := by exact_mod_cast ht
                               linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogt : 0 < Real.log t := Real.log_pos (by have : (2 : ℝ) ≤ t := by exact_mod_cast ht
                                                  linarith)
  set κ := Real.log t / Real.log 3
  have hκ : 0 < κ := div_pos hlogt hlog3
  obtain ⟨C', hC', hend⟩ := endgame hκ hC.le
  refine ⟨4 * C', fun K δ U V hU hV hU0 hid => ?_⟩
  rcases Nat.eq_zero_or_pos δ with rfl | hδ
  · simp; positivity
  obtain ⟨S, c, hSK, hc, rfl⟩ := hU
  obtain ⟨S', c', hSK', hc', rfl⟩ := hV
  set lam : ℝ := δ * κ with hlamdef
  have hlam0 : 0 ≤ lam := by positivity
  have hlam : (3 : ℝ) ^ lam = ((t ^ δ : ℕ) : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num), hlamdef]
    push_cast
    rw [← Real.exp_log (pow_pos ht0 δ), Real.log_pow]
    congr 1; simp only [κ]; field_simp
  set T : ℕ := t ^ δ with hTdef
  have h3T : ¬ (3 : ℤ) ∣ (T : ℤ) := by
    intro h
    have h' : (3 : ℤ) ∣ (t : ℤ) ^ δ := by simpa [T] using h
    exact h3 (by exact_mod_cast Int.Prime.dvd_pow' Nat.prime_three h')
  have hid' : (T : ℤ) * (∑ e ∈ S, c e * 3 ^ e) = ∑ f ∈ S', c' f * 3 ^ f := by
    rw [← hid]; simp [T]
  -- the levels
  set Lv : Finset ℝ := S.image (fun e : ℕ => (e : ℝ) + lam) ∪ S'.image (fun f : ℕ => (f : ℝ))
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact absurd (by rw [h]; simp) hU0
    · exact h
  have hLne : Lv.Nonempty := (hSne.image _).mono subset_union_left
  have hLvcard : Lv.card ≤ 2 * K := by
    refine (card_union_le _ _).trans ?_
    have := card_image_le (s := S) (f := fun e : ℕ => (e : ℝ) + lam)
    have := card_image_le (s := S') (f := fun f : ℕ => (f : ℝ))
    omega
  have hLv0 : ∀ x ∈ Lv, 0 ≤ x := by
    intro x hx
    rcases mem_union.1 hx with h | h
    · obtain ⟨e, -, rfl⟩ := mem_image.1 h; positivity
    · obtain ⟨e, -, rfl⟩ := mem_image.1 h; positivity
  have hSmem : ∀ e ∈ S, (e : ℝ) + lam ∈ Lv := fun e he =>
    mem_union_left _ (mem_image_of_mem _ he)
  have hS'mem : ∀ f ∈ S', (f : ℝ) ∈ Lv := fun f hf =>
    mem_union_right _ (mem_image_of_mem (fun f : ℕ => (f : ℝ)) hf)
  set good : ℝ → Prop := fun θ => (T : ℤ) * (∑ e ∈ S.filter (fun e : ℕ => θ ≤ (e : ℝ) + lam),
      c e * 3 ^ e) - ∑ f ∈ S'.filter (fun f : ℕ => θ ≤ (f : ℝ)), c' f * 3 ^ f = 0
  classical
  set G := Lv.filter good
  have hGne : G.Nonempty := by
    refine ⟨Lv.min' hLne, mem_filter.2 ⟨Lv.min'_mem hLne, ?_⟩⟩
    simp only [good]
    rw [filter_true_of_mem (fun e he => Lv.min'_le _ (hSmem e he)),
      filter_true_of_mem (fun f hf => Lv.min'_le _ (hS'mem f hf)), hid', sub_self]
  set θs := G.max' hGne
  have hθs : θs ∈ Lv := (mem_filter.1 (G.max'_mem hGne)).1
  have hθsg : good θs := (mem_filter.1 (G.max'_mem hGne)).2
  set ℓ1 := Lv.max' hLne
  set L := 1 + Real.log (δ + lam + 2)
  have hL : 0 ≤ L := by
    have : 0 ≤ Real.log (δ + lam + 2) := Real.log_nonneg (by
      have := (Nat.cast_nonneg δ : (0:ℝ) ≤ δ); linarith)
    linarith
  set R := 3 + C * L
  have hR : 1 ≤ R := by have : 0 ≤ C * L := by positivity
                        linarith
  -- the chain
  have chain : ∀ n : ℕ, ∀ θ ∈ Lv, θs ≤ θ → (Lv.filter (fun x => θ < x)).card ≤ n →
      ℓ1 - θ + 2 ≤ 2 * R ^ n := by
    intro n
    induction n with
    | zero =>
      intro θ hθ _ hcard
      have : θ = ℓ1 := by
        refine le_antisymm (Lv.le_max' _ hθ) (not_lt.1 fun hlt => ?_)
        have : (Lv.filter (fun x => θ < x)).Nonempty := ⟨ℓ1, mem_filter.2 ⟨Lv.max'_mem hLne, hlt⟩⟩
        have := this.card_pos; omega
      rw [this]; simp
    | succ n ih =>
      intro θ hθ hθs' hcard
      by_cases heq : θ = ℓ1
      · rw [heq, sub_self, zero_add]
        have : 1 ≤ R ^ (n + 1) := one_le_pow₀ hR
        linarith
      have hlt : θ < ℓ1 := lt_of_le_of_ne (Lv.le_max' _ hθ) heq
      have hAne : (Lv.filter (fun x => θ < x)).Nonempty := ⟨ℓ1, mem_filter.2 ⟨Lv.max'_mem hLne, hlt⟩⟩
      set θ' := (Lv.filter (fun x => θ < x)).min' hAne
      have hθ'mem := mem_filter.1 ((Lv.filter (fun x => θ < x)).min'_mem hAne)
      have hθθ' : θ < θ' := hθ'mem.2
      have hnext : ∀ x ∈ Lv, x < θ' → x ≤ θ := by
        intro x hx hxθ'
        by_contra hcon; push Not at hcon
        exact absurd ((Lv.filter (fun x => θ < x)).min'_le x (mem_filter.2 ⟨hx, hcon⟩)) (not_le.2 hxθ')
      have hcard' : (Lv.filter (fun x => θ' < x)).card ≤ n := by
        have hss : Lv.filter (fun x => θ' < x) ⊂ Lv.filter (fun x => θ < x) := by
          refine ⟨fun x hx => mem_filter.2 ⟨(mem_filter.1 hx).1, hθθ'.trans (mem_filter.1 hx).2⟩,
            fun hsub => ?_⟩
          have := (mem_filter.1 (hsub (mem_filter.2 ⟨hθ'mem.1, hθθ'⟩))).2
          exact lt_irrefl _ this
        have := card_lt_card hss; omega
      have hih := ih θ' hθ'mem.1 (hθs'.trans hθθ'.le) hcard'
      have hng : ¬ good θ' := by
        intro hg
        have : θ' ≤ θs := G.le_max' θ' (mem_filter.2 ⟨hθ'mem.1, hg⟩)
        linarith
      have hgap := gap_step hlam hlam0 hC hCb hc hc' hid' (θ := θ') (s := ℓ1 - θ') (ν := θ)
        (hLv0 _ hθ'mem.1) (by linarith [Lv.le_max' _ hθ'mem.1])
        (fun e he _ => by linarith [Lv.le_max' _ (hSmem e he)])
        (fun f hf _ => by linarith [Lv.le_max' _ (hS'mem f hf)])
        (fun e he h => hnext _ (hSmem e he) h) (fun f hf h => hnext _ (hS'mem f hf) h) hng
      have hs2 : 2 ≤ ℓ1 - θ' + 2 := by linarith [Lv.le_max' _ hθ'mem.1]
      have hCL : 0 ≤ C * L := by positivity
      calc ℓ1 - θ + 2 = (ℓ1 - θ' + 2) + (θ' - θ) := by ring
        _ ≤ R * (ℓ1 - θ' + 2) := by simp only [R]; nlinarith
        _ ≤ R * (2 * R ^ n) := mul_le_mul_of_nonneg_left hih (by linarith)
        _ = 2 * R ^ (n + 1) := by ring
  have hspan := chain Lv.card θs hθs le_rfl (card_filter_le _ _)
  -- λ ≤ span
  have hlamspan : lam ≤ ℓ1 - θs := by
    set St := S.filter (fun e : ℕ => θs ≤ (e : ℝ) + lam)
    set St' := S'.filter (fun f : ℕ => θs ≤ (f : ℝ))
    have hg : (T : ℤ) * (∑ e ∈ St, c e * 3 ^ e) = ∑ f ∈ St', c' f * 3 ^ f :=
      sub_eq_zero.1 hθsg
    have hStne : St.Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, sum_empty, mul_zero] at hg
      have hSt'e : St' = ∅ := by
        by_contra h'
        exact sum_ne_zero_of_nonempty (fun e he => hc' e (mem_filter.1 he).1)
          (nonempty_iff_ne_empty.2 h') hg.symm
      rcases mem_union.1 hθs with h | h
      · obtain ⟨e, he, hee⟩ := mem_image.1 h
        have : e ∈ St := mem_filter.2 ⟨he, hee.ge⟩
        rw [hne] at this; simp at this
      · obtain ⟨f, hf, hff⟩ := mem_image.1 h
        have : f ∈ St' := mem_filter.2 ⟨hf, hff.ge⟩
        rw [hSt'e] at this; simp at this
    obtain ⟨e, he, f, hf, hfe⟩ := exists_le_of_split h3T (fun e he => hc e (mem_filter.1 he).1)
      hStne hg
    have h1 := Lv.le_max' _ (hSmem e (mem_filter.1 he).1)
    have h2 := (mem_filter.1 hf).2
    have h3' : (f : ℝ) ≤ e := by exact_mod_cast hfe
    linarith
  -- the endgame
  have hx : κ * δ ≤ 2 * (3 + C + C * Real.log ((1 + κ) * δ + 2)) ^ Lv.card := by
    have : (1 + κ) * (δ : ℝ) + 2 = δ + lam + 2 := by simp only [lam]; ring
    rw [this]
    have : 3 + C + C * Real.log (δ + lam + 2) = R := by simp only [R, L]; ring
    rw [this]
    have : κ * δ = lam := by simp only [lam]; ring
    linarith
  have hfin := hend Lv.card δ (Nat.cast_nonneg _) hx
  refine hfin.trans (Real.exp_le_exp.2 ?_)
  have : ((Lv.card : ℝ) + 1) ^ 2 ≤ 4 * ((K : ℝ) + 1) ^ 2 := by
    have : (Lv.card : ℝ) ≤ 2 * K := by exact_mod_cast hLvcard
    nlinarith [(Nat.cast_nonneg (Lv.card) : (0:ℝ) ≤ _)]
  nlinarith

end NormalNumbers.SparseIdentity
