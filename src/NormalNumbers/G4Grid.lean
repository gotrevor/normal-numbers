/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FreqSep

/-!
# G4 disjunctivity, §4A: the separated grid and the surviving shifts

Draft §2 (`docs/prime-lambert-disjunctivity-draft.md`), brief §4A.

Atoms are `α : Fin K → Fin (s+1)`.  With an integer base `B`, put

* `u α = ∑ᵢ αᵢ B^{i+1}`, `v α = ∑ᵢ (i+1) αᵢ B^{i+1}` (draft (2.2), indices shifted by one so that
  `i : Fin K` is the draft's coordinate `i+1`);
* `proj j α = j·u α − v α = ∑ᵢ (j − (i+1)) αᵢ B^{i+1}`.

Two facts carry the whole grid:

* **Fiber cancellation** (`proj_update_eq`, `sum_kronPow_diffZ_mul_eq_zero`): for `j = i₀ + 1 ≤ K`
  the projection ignores coordinate `i₀`, so any function of it is annihilated by every row of
  `A = D_s^{⊗K}` — the first `K` arithmetic layers cancel exactly.
* **Injectivity** (`proj_injective`): for `K < j` the projection is injective once `s·j < B`,
  by uniqueness of balanced base-`B` digits (`balanced_digits_eq_zero`).  Only `|digit| < B` is
  needed, not the draft's `2sJ+1`.

Then, with `Q` divisible by every integer up to `max(J+1, U, V)` and `D₀ ≥ V`,

* `d α = 1 + Q (D₀ + u α)`, `t α = Q v α`, `ρ α j = j d α − t α` (draft (2.3));
* `d` is pairwise coprime (`coprime_mult`), `t α ≤ j d α` for `j ≥ 1` (`offset_le_mul_mult`), and the
  surviving shifts `ρ α j`, `K < j ≤ J`, are globally distinct (`shiftG_injective`): `ρ ≡ j (mod Q)`
  separates layers and `proj_injective` separates atoms within a layer.
* On the progression `n = t α + d α · k`, `n + ρ α j = d α (k + j)` (`add_shiftG_eq`), the
  arithmetic input of the transport identity (draft (4.1)).
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### Balanced digits -/

/-- Uniqueness of base-`B` representations with digits of absolute value below `B`: if
`∑_{i<n} e_i B^i = 0` then every digit vanishes.  Peel the bottom digit by divisibility. -/
theorem balanced_digits_eq_zero {B : ℕ} : ∀ (n : ℕ) (e : ℕ → ℤ), (∀ i < n, |e i| < B) →
    ∑ i ∈ range n, e i * (B : ℤ) ^ i = 0 → ∀ i < n, e i = 0 := by
  intro n
  induction n with
  | zero => intro e _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro e he hsum i hi
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_zero, mul_one] at hsum
    have hdvd : (B : ℤ) ∣ e 0 := by
      have : e 0 = -(∑ i ∈ range n, e (i + 1) * (B : ℤ) ^ (i + 1)) := by linarith
      rw [this]
      refine dvd_neg.2 (Finset.dvd_sum fun i _ => ?_)
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.succ_ne_zero i)) _
    have h0 : e 0 = 0 := by
      have hlt := he 0 (Nat.succ_pos n)
      rcases hdvd with ⟨c, hc⟩
      rcases eq_or_ne c 0 with h | h
      · rw [hc, h, mul_zero]
      · exfalso
        have : (B : ℤ) * 1 ≤ |(B : ℤ) * c| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ B)]
          exact mul_le_mul_of_nonneg_left (Int.one_le_abs h) (by positivity)
        rw [← hc, mul_one] at this
        exact absurd (this.trans_lt hlt) (lt_irrefl _)
    rw [h0, add_zero] at hsum
    have hsum' : ∑ i ∈ range n, e (i + 1) * (B : ℤ) ^ i = 0 := by
      have hB : (B : ℤ) ≠ 0 := by
        have := he 0 (Nat.succ_pos n)
        have : (0 : ℤ) < B := (abs_nonneg _).trans_lt this
        exact this.ne'
      have : (B : ℤ) * ∑ i ∈ range n, e (i + 1) * (B : ℤ) ^ i = 0 := by
        rw [Finset.mul_sum, ← hsum]
        exact Finset.sum_congr rfl fun i _ => by ring
      exact (mul_eq_zero.1 this).resolve_left hB
    rcases i with _ | i
    · exact h0
    · exact ih (fun i => e (i + 1)) (fun i hi => he (i + 1) (by omega)) hsum' i (by omega)

/-! ### The grid encoding -/

variable {K s : ℕ}

/-- `u α = ∑ᵢ αᵢ B^{i+1}` (draft (2.2)). -/
def gridU (B : ℕ) (α : Fin K → Fin (s + 1)) : ℕ := ∑ i : Fin K, (α i : ℕ) * B ^ ((i : ℕ) + 1)

/-- `v α = ∑ᵢ (i+1) αᵢ B^{i+1}` (draft (2.2)). -/
def gridV (B : ℕ) (α : Fin K → Fin (s + 1)) : ℕ :=
  ∑ i : Fin K, ((i : ℕ) + 1) * (α i : ℕ) * B ^ ((i : ℕ) + 1)

/-- The layer-`j` projection `j·u α − v α = ∑ᵢ (j − (i+1)) αᵢ B^{i+1}`, over `ℤ`. -/
def proj (B : ℕ) (j : ℕ) (α : Fin K → Fin (s + 1)) : ℤ :=
  ∑ i : Fin K, ((j : ℤ) - ((i : ℕ) + 1)) * (α i : ℤ) * (B : ℤ) ^ ((i : ℕ) + 1)

lemma proj_eq (B j : ℕ) (α : Fin K → Fin (s + 1)) :
    proj B j α = (j : ℤ) * gridU B α - gridV B α := by
  unfold proj gridU gridV
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma gridU_le (B : ℕ) (α : Fin K → Fin (s + 1)) : gridU B α ≤ s * ∑ i : Fin K, B ^ ((i : ℕ) + 1) := by
  unfold gridU
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 (α i).isLt)

lemma gridV_le (B : ℕ) (α : Fin K → Fin (s + 1)) :
    gridV B α ≤ K * s * ∑ i : Fin K, B ^ ((i : ℕ) + 1) := by
  unfold gridV
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul i.isLt (Nat.lt_succ_iff.1 (α i).isLt))

/-- **Fiber cancellation**: the layer `j = i₀ + 1` projection ignores coordinate `i₀`. -/
lemma proj_update_eq (B : ℕ) (i₀ : Fin K) (α : Fin K → Fin (s + 1)) (c : Fin (s + 1)) :
    proj B ((i₀ : ℕ) + 1) (Function.update α i₀ c) = proj B ((i₀ : ℕ) + 1) α := by
  unfold proj
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h; simp
  · rw [Function.update_of_ne h]

/-- A function of the atoms that ignores coordinate `i₀` is annihilated by every row of a
Kronecker power of a matrix with vanishing row sums. -/
theorem sum_kronPow_mul_eq_zero {R : Type*} [CommRing R] {m : Type*} [Fintype m]
    (M : Matrix m (Fin (s + 1)) R) (hM : ∀ a, ∑ c, M a c = 0) (i₀ : Fin K)
    (g : (Fin K → Fin (s + 1)) → R) (hg : ∀ α c, g (Function.update α i₀ c) = g α)
    (a : Fin K → m) :
    ∑ α, kronPow K M a α * g α = 0 := by
  cases K with
  | zero => exact i₀.elim0
  | succ K =>
    rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ => Fin (s + 1)) i₀), Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun α' _ => ?_
    have key : ∀ c : Fin (s + 1),
        kronPow (K + 1) M a ((Fin.insertNthEquiv (fun _ => Fin (s + 1)) i₀) (c, α')) *
            g ((Fin.insertNthEquiv (fun _ => Fin (s + 1)) i₀) (c, α'))
          = M (a i₀) c * ((∏ i : Fin K, M (a (i₀.succAbove i)) (α' i)) *
              g (Fin.insertNth i₀ (0 : Fin (s + 1)) α')) := by
      intro c
      change kronPow (K + 1) M a (Fin.insertNth i₀ c α') * g (Fin.insertNth i₀ c α') = _
      have hg' : g (Fin.insertNth i₀ c α') = g (Fin.insertNth i₀ (0 : Fin (s + 1)) α') := by
        have := hg (Fin.insertNth i₀ (0 : Fin (s + 1)) α') c
        rw [← this]
        congr 1
        ext i
        by_cases h : i = i₀
        · subst h; simp
        · rw [Function.update_of_ne h]
          obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
          simp
      simp only [kronPow]
      rw [Fin.prod_univ_succAbove _ i₀, hg']
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      ring
    simp_rw [key]
    rw [← Finset.sum_mul, hM, zero_mul]

/-- The integer difference matrix has vanishing row sums. -/
lemma sum_diffZ_row (s : ℕ) (a : Fin s) : ∑ c, diffZ s a c = 0 := by
  simp [diffZ, Pi.single_apply, Finset.sum_sub_distrib]

/-- **The first `K` layers cancel**: for `j = i₀ + 1 ≤ K`, every row of `A = D_s^{⊗K}` kills any
function of `proj B j`. -/
theorem sum_kronPow_diffZ_mul_eq_zero {R : Type*} [CommRing R] (B : ℕ) (i₀ : Fin K)
    (f : ℤ → R) (a : Fin K → Fin s) :
    ∑ α, ((kronPow K (diffZ s) a α : ℤ) : R) * f (proj B ((i₀ : ℕ) + 1) α) = 0 := by
  have := sum_kronPow_mul_eq_zero (R := R) (fun a c => ((diffZ s a c : ℤ) : R))
    (fun a => by rw [← Int.cast_sum, sum_diffZ_row, Int.cast_zero]) i₀
    (fun α => f (proj B ((i₀ : ℕ) + 1) α))
    (fun α c => by rw [proj_update_eq]) a
  simpa [kronPow, Int.cast_prod] using this

/-- **Injectivity of the surviving projections**: for `K < j` and `s * j < B`, `proj B j` is
injective. -/
theorem proj_injective (B j : ℕ) (hj : K < j) (hB : s * j < B) :
    Function.Injective (proj B j : (Fin K → Fin (s + 1)) → ℤ) := by
  intro α β hαβ
  -- the digit difference
  set e : ℕ → ℤ := fun i => if h : i < K then
    ((j : ℤ) - (i + 1)) * ((α ⟨i, h⟩ : ℤ) - (β ⟨i, h⟩ : ℤ)) else 0 with he
  have hsum : ∑ i ∈ range K, e i * (B : ℤ) ^ i = 0 := by
    have h1 : proj B j α - proj B j β = (B : ℤ) * ∑ i ∈ range K, e i * (B : ℤ) ^ i := by
      unfold proj
      rw [← Finset.sum_sub_distrib, ← Fin.sum_univ_eq_sum_range
        (fun i => e i * (B : ℤ) ^ i) K, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [he, i.isLt, dite_true, Fin.eta]
      ring
    rw [hαβ, sub_self] at h1
    have hB0 : (B : ℤ) ≠ 0 := by
      have : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
      exact_mod_cast this.ne'
    exact (mul_eq_zero.1 h1.symm).resolve_left hB0
  have hdig : ∀ i < K, |e i| < B := by
    intro i hi
    simp only [he, hi, dite_true]
    rw [abs_mul]
    have h1 : |(j : ℤ) - (i + 1)| ≤ j := by
      rw [abs_le]; constructor <;> push_cast <;> linarith [(Nat.cast_nonneg i : (0 : ℤ) ≤ i)]
    have h2 : |(α ⟨i, hi⟩ : ℤ) - (β ⟨i, hi⟩ : ℤ)| ≤ s := by
      have ha := (α ⟨i, hi⟩).isLt
      have hb := (β ⟨i, hi⟩).isLt
      rw [abs_le]; constructor <;> push_cast <;> omega
    calc |(j : ℤ) - (i + 1)| * |(α ⟨i, hi⟩ : ℤ) - (β ⟨i, hi⟩ : ℤ)| ≤ (j : ℤ) * s :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ < B := by rw [mul_comm]; exact_mod_cast hB
  have hz := balanced_digits_eq_zero K e hdig hsum
  ext i
  have := hz i i.isLt
  simp only [he, i.isLt, dite_true, Fin.eta, mul_eq_zero] at this
  rcases this with h | h
  · exfalso
    have : ((i : ℕ) : ℤ) + 1 ≤ K := by exact_mod_cast i.isLt
    have : (K : ℤ) < j := by exact_mod_cast hj
    linarith
  · exact_mod_cast (sub_eq_zero.1 h)

/-- `u` itself is injective once `s < B` (the `j = 0` case of the digit argument, with
coefficient `−(i+1)` replaced by `1`). -/
theorem gridU_injective (B : ℕ) (hB : s < B) :
    Function.Injective (gridU B : (Fin K → Fin (s + 1)) → ℕ) := by
  intro α β hαβ
  set e : ℕ → ℤ := fun i => if h : i < K then ((α ⟨i, h⟩ : ℤ) - (β ⟨i, h⟩ : ℤ)) else 0 with he
  have hsum : ∑ i ∈ range K, e i * (B : ℤ) ^ i = 0 := by
    have h1 : ((gridU B α : ℕ) : ℤ) - (gridU B β : ℕ) = (B : ℤ) * ∑ i ∈ range K, e i * (B : ℤ) ^ i := by
      unfold gridU
      push_cast
      rw [← Finset.sum_sub_distrib, ← Fin.sum_univ_eq_sum_range
        (fun i => e i * (B : ℤ) ^ i) K, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [he, i.isLt, dite_true, Fin.eta]
      ring
    rw [hαβ, sub_self] at h1
    have hB0 : (B : ℤ) ≠ 0 := by
      have : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
      exact_mod_cast this.ne'
    exact (mul_eq_zero.1 h1.symm).resolve_left hB0
  have hdig : ∀ i < K, |e i| < B := by
    intro i hi
    simp only [he, hi, dite_true]
    have ha := (α ⟨i, hi⟩).isLt
    have hb := (β ⟨i, hi⟩).isLt
    have : |(α ⟨i, hi⟩ : ℤ) - (β ⟨i, hi⟩ : ℤ)| ≤ s := by
      rw [abs_le]; constructor <;> push_cast <;> omega
    exact this.trans_lt (by exact_mod_cast hB)
  have hz := balanced_digits_eq_zero K e hdig hsum
  ext i
  have := hz i i.isLt
  simp only [he, i.isLt, dite_true, Fin.eta] at this
  exact_mod_cast (sub_eq_zero.1 this)

/-! ### Multipliers, offsets, shifts -/

/-- `d α = 1 + Q (D₀ + u α)` (draft (2.3)). -/
def mult (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) : ℕ := 1 + Q * (D₀ + gridU B α)

/-- `t α = Q v α` (draft (2.3)). -/
def offset (B Q : ℕ) (α : Fin K → Fin (s + 1)) : ℕ := Q * gridV B α

/-- The shift `ρ_{α,j} = j d α − t α` (draft (2.3)). -/
def shiftG (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) (j : ℕ) : ℕ := j * mult B Q D₀ α - offset B Q α

lemma mult_pos (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) : 0 < mult B Q D₀ α := by
  unfold mult; positivity

lemma mult_mod_Q (B Q D₀ : ℕ) (hQ : 1 < Q) (α : Fin K → Fin (s + 1)) : mult B Q D₀ α % Q = 1 := by
  unfold mult
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hQ

/-- `t α ≤ j d α` for `j ≥ 1`, given `D₀ ≥ v α`. -/
lemma offset_le_mul_mult (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) (hD : gridV B α ≤ D₀) {j : ℕ}
    (hj : 1 ≤ j) : offset B Q α ≤ j * mult B Q D₀ α := by
  unfold offset mult
  calc Q * gridV B α ≤ Q * (D₀ + gridU B α) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 1 * (1 + Q * (D₀ + gridU B α)) := by omega
    _ ≤ j * (1 + Q * (D₀ + gridU B α)) := Nat.mul_le_mul_right _ hj

/-- The shift as an integer identity: `ρ α j = j d α − t α` with no truncation. -/
lemma shiftG_cast (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) (hD : gridV B α ≤ D₀) {j : ℕ}
    (hj : 1 ≤ j) :
    ((shiftG B Q D₀ α j : ℕ) : ℤ) = j * mult B Q D₀ α - offset B Q α := by
  unfold shiftG
  rw [Nat.cast_sub (offset_le_mul_mult B Q D₀ α hD hj)]
  push_cast; ring

/-- The shift in terms of the projection: `ρ α j = j + Q (j D₀ + proj B j α)`. -/
lemma shiftG_eq (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) (hD : gridV B α ≤ D₀) {j : ℕ}
    (hj : 1 ≤ j) :
    ((shiftG B Q D₀ α j : ℕ) : ℤ) = j + Q * (j * D₀ + proj B j α) := by
  rw [shiftG_cast B Q D₀ α hD hj, proj_eq]
  unfold mult offset
  push_cast; ring

/-- `ρ α j ≡ j (mod Q)`. -/
lemma shiftG_mod_Q (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) (hD : gridV B α ≤ D₀) {j : ℕ}
    (hj : 1 ≤ j) : ((shiftG B Q D₀ α j : ℕ) : ℤ) % Q = (j : ℤ) % Q := by
  rw [shiftG_eq B Q D₀ α hD hj, Int.add_mul_emod_self_left]

/-- **Global distinctness of the surviving shifts** (draft §2): for `K < j, j' ≤ J < Q` and
`s * J < B`, `ρ α j = ρ β j'` forces `j = j'` and `α = β`. -/
theorem shiftG_injective (B Q D₀ J : ℕ) (hB : s * J < B) (hJQ : J < Q)
    (hD : ∀ α : Fin K → Fin (s + 1), gridV B α ≤ D₀)
    {α β : Fin K → Fin (s + 1)} {j j' : ℕ} (hj : K < j) (hjJ : j ≤ J) (hj' : K < j') (hj'J : j' ≤ J)
    (h : shiftG B Q D₀ α j = shiftG B Q D₀ β j') : j = j' ∧ α = β := by
  have hj1 : 1 ≤ j := by omega
  have hj'1 : 1 ≤ j' := by omega
  have hZ : ((shiftG B Q D₀ α j : ℕ) : ℤ) = shiftG B Q D₀ β j' := by rw [h]
  have hmod : ((shiftG B Q D₀ α j : ℕ) : ℤ) % Q = ((shiftG B Q D₀ β j' : ℕ) : ℤ) % Q := by
    rw [hZ]
  rw [shiftG_mod_Q B Q D₀ α (hD α) hj1, shiftG_mod_Q B Q D₀ β (hD β) hj'1,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hjJ.trans_lt hJQ),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj'J.trans_lt hJQ)] at hmod
  have hjj : j = j' := by exact_mod_cast hmod
  subst hjj
  refine ⟨rfl, ?_⟩
  rw [shiftG_eq B Q D₀ α (hD α) hj1, shiftG_eq B Q D₀ β (hD β) hj1] at hZ
  have hQ0 : (Q : ℤ) ≠ 0 := by
    have : 0 < Q := by omega
    exact_mod_cast this.ne'
  have hp : proj B j α = proj B j β := by
    have := mul_left_cancel₀ hQ0 (add_left_cancel hZ)
    linarith
  exact proj_injective B j hj (lt_of_le_of_lt (Nat.mul_le_mul_left _ hjJ) hB) hp

/-- **Pairwise coprimality of the multipliers** (draft §2): with `Q` divisible by every positive
integer up to `U ≥ max u`, and `s < B`, distinct atoms have coprime `d`. -/
theorem coprime_mult (B Q D₀ U : ℕ) (hB : s < B) (hQ : 1 < Q)
    (hU : ∀ α : Fin K → Fin (s + 1), gridU B α ≤ U) (hQdvd : ∀ m, 0 < m → m ≤ U → m ∣ Q)
    {α β : Fin K → Fin (s + 1)} (hαβ : α ≠ β) :
    Nat.Coprime (mult B Q D₀ α) (mult B Q D₀ β) := by
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.Coprime]
  refine Nat.coprime_of_dvd fun p hp hpa hpb => ?_
  -- `p ∤ Q` since `d ≡ 1 (mod Q)`
  have hpQ : ¬ p ∣ Q := by
    intro hpQ
    have : p ∣ 1 := by
      have h1 : p ∣ Q * (D₀ + gridU B α) := Dvd.dvd.mul_right hpQ _
      exact (Nat.dvd_add_right h1).1 (by simpa [mult, add_comm] using hpa)
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  -- `p ∣ Q (u α − u β)` over `ℤ`
  have hdiff : (p : ℤ) ∣ (Q : ℤ) * ((gridU B α : ℤ) - gridU B β) := by
    have ha : (p : ℤ) ∣ (mult B Q D₀ α : ℤ) := by exact_mod_cast hpa
    have hb : (p : ℤ) ∣ (mult B Q D₀ β : ℤ) := by exact_mod_cast hpb
    have heq : (Q : ℤ) * ((gridU B α : ℤ) - gridU B β)
        = (mult B Q D₀ α : ℤ) - mult B Q D₀ β := by
      unfold mult; push_cast; ring
    rw [heq]
    exact dvd_sub ha hb
  have hpQ' : ¬ (p : ℤ) ∣ Q := by exact_mod_cast hpQ
  have hdu : (p : ℤ) ∣ (gridU B α : ℤ) - gridU B β :=
    (Int.Prime.dvd_mul' hp hdiff).resolve_left hpQ'
  have hne : (gridU B α : ℤ) - gridU B β ≠ 0 := by
    intro h0
    exact hαβ (gridU_injective B hB (by exact_mod_cast sub_eq_zero.1 h0))
  -- `p ≤ |u α − u β| ≤ U`, so `p ∣ Q`
  have hle : (p : ℤ) ≤ |(gridU B α : ℤ) - gridU B β| := Int.le_of_dvd (abs_pos.2 hne) (by
    rwa [dvd_abs])
  have hU' : |(gridU B α : ℤ) - gridU B β| ≤ U := by
    have := hU α; have := hU β
    rw [abs_le]; constructor <;> push_cast <;> omega
  exact hpQ (hQdvd p hp.pos (by exact_mod_cast hle.trans hU'))

/-- On the progression `n = t α + d α · k`, the shifted argument factors:
`n + ρ α j = d α (k + j)` (draft (4.1)). -/
lemma add_shiftG_eq (B Q D₀ : ℕ) (α : Fin K → Fin (s + 1)) (hD : gridV B α ≤ D₀) {j : ℕ}
    (hj : 1 ≤ j) (k : ℕ) :
    offset B Q α + mult B Q D₀ α * k + shiftG B Q D₀ α j = mult B Q D₀ α * (k + j) := by
  have h := offset_le_mul_mult B Q D₀ α hD hj
  unfold shiftG
  zify [h]
  ring

end NormalNumbers.G4
