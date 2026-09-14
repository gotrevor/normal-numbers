import NormalNumbers.PrimeLambertTail

/-!
# Large primes: the exact pointwise bound (draft §5.5, eq. (19))

Every prime part is bounded by `‖c‖₁ · 2^{−K}` with no hypothesis at all: on each atom at
most the geometric tail `∑_{K<j≤J} 2^{−j} < 2^{−K}` survives (`abs_primePart_le`), and a prime
dividing none of the arguments contributes nothing (`primePart_eq_zero`).  Hence the large
class is bounded by the number of large primes that divide some argument
(`abs_classSum_le_card`), and `LargePrimeNegligible` reduces to the count Prop
`LargePrimeCountSmall`: `#{p large : p ∣ some n + j d_a − s_a} · ‖c‖₁ 2^{−K} ≤ ε_N → 0`
(`largePrimeNegligible_of_count`).  The draft bounds that count by
`H (J−K) log(3N)/log R` since each argument is `≤ 3N` and has at most `log(3N)/log R` prime
factors above `R`; that arithmetic is the remaining open input.
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- `ℓ¹`-mass of a configuration. -/
noncomputable def l1 (c : TConfig) : ℝ := ∑ a ∈ c.support, |(c a : ℝ)|

lemma l1_nonneg (c : TConfig) : 0 ≤ l1 c := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- `∑_{K ≤ i < J} 2^{−(i+1)} ≤ 2^{−K}`. -/
lemma sum_Ico_geom_le (K J : ℕ) : ∑ i ∈ Ico K J, (1 : ℝ) / 2 ^ (i + 1) ≤ 1 / 2 ^ K := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∀ i ∈ range (J - K), (1 : ℝ) / 2 ^ (K + i + 1) = 1 / 2 ^ (i + K + 1) := by
    intro i _; rw [show K + i + 1 = i + K + 1 by ring]
  rw [Finset.sum_congr rfl h, ← tsum_shift_geom K]
  exact Summable.sum_le_tsum _ (fun i _ => by positivity)
    ((summable_nat_add_iff K).mpr summable_geom_shift |>.congr (fun i => by simp only))

/-- **Pointwise bound**: `|X_p(n)| ≤ ‖c‖₁ 2^{−K}`, unconditionally. -/
theorem abs_primePart_le (c : TConfig) (K J p : ℕ) (n : ℤ) :
    |primePart c K J p n| ≤ l1 c / 2 ^ K := by
  unfold primePart Finsupp.sum l1
  rw [Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  rw [abs_mul, div_eq_mul_one_div]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => ?_)).trans
    (sum_Ico_geom_le K J))
  split_ifs <;> simp

/-- A prime dividing no argument contributes nothing. -/
theorem primePart_eq_zero (c : TConfig) (K J p : ℕ) (n : ℤ)
    (h : ¬ ∃ a ∈ c.support, ∃ i ∈ Ico K J, (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2) :
    primePart c K J p n = 0 := by
  unfold primePart Finsupp.sum
  refine Finset.sum_eq_zero (fun a ha => ?_)
  simp only
  rw [Finset.sum_eq_zero (fun i hi => ?_), mul_zero]
  rw [if_neg (fun hd => h ⟨a, ha, i, hi, hd⟩)]

/-- The primes of a class that actually divide some argument of the finite tail at `n`. -/
def activePrimes (c : TConfig) (K J : ℕ) (S : Finset ℕ) (n : ℤ) : Finset ℕ :=
  S.filter (fun p => ∃ a ∈ c.support, ∃ i ∈ Ico K J, (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2)

/-- **Class bound**: `|∑_{p ∈ S} X_p(n)| ≤ #(active primes) · ‖c‖₁ 2^{−K}`. -/
theorem abs_classSum_le_card (c : TConfig) (K J : ℕ) (S : Finset ℕ) (n : ℤ) :
    |classSum c K J S n| ≤ (activePrimes c K J S n).card * (l1 c / 2 ^ K) := by
  unfold classSum
  rw [← Finset.sum_filter_add_sum_filter_not S
    (fun p => ∃ a ∈ c.support, ∃ i ∈ Ico K J, (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2)]
  rw [Finset.sum_eq_zero (fun p hp => primePart_eq_zero c K J p n (Finset.mem_filter.mp hp).2),
    add_zero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p _ => abs_primePart_le c K J p n)).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

/-- Draft (19) as a count: the number of large primes dividing some argument, times
`‖c‖₁ 2^{−K}`, is uniformly `o(1)` on the sample. -/
def LargePrimeCountSmall {q : ℤ} (C : Chain q) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ N, ∀ n ∈ (C.D N).P,
      (activePrimes (C.c N) (C.K N) (C.S N).J (C.S N).large n).card
        * (l1 (C.c N) / 2 ^ C.K N) ≤ ε N

/-- `LargePrimeCountSmall → LargePrimeNegligible`. -/
theorem largePrimeNegligible_of_count {q : ℤ} (C : Chain q) (h : LargePrimeCountSmall C) :
    LargePrimeNegligible C := by
  obtain ⟨ε, hε, hb⟩ := h
  exact ⟨ε, hε, fun N n hn => (abs_classSum_le_card _ _ _ _ n).trans (hb N n hn)⟩

end NormalNumbers.PrimeLambert
