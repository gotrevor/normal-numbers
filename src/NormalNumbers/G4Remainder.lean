/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Frame

/-!
# G4 disjunctivity, §4D: the exact remainder decomposition

Draft §7, brief §4D.  `PropD` asks that the small-prime vector `S n` and the exact transported
vector `Ffull n` be close *on average over the sample*, in the average coordinate metric.  This
module does the exact algebra that turns that into three arithmetic estimates; no analytic
bound is claimed here.

* **`sum_kronPow_mul_shiftG_eq_zero`** — for `j = i₀ + 1 ≤ K`, `n + ρ_{α,j}` depends on the atom
  only through `proj B j α` (`shiftG_eq`: `ρ_{α,j} = j + Q(jD₀ + proj B j α)`), which ignores
  coordinate `i₀`; so every row of `A = D_s^{⊗K}` annihilates *any* function of it.  **The first
  `K` arithmetic layers cancel exactly**, for any `n` and any weight.
* **`Frame.Ffull_eq_retained`** — consequently, on a frame built from a `GridParams`,
  `Ffull n = (∑_α A_{να} ∑_{j > K} 4^{−j} ω(n + ρ_{α,j})) − γ`: only the retained layers survive.

The remaining difference `S n − Ffull n` then splits, prime by prime, into
* the **frozen** primes `p ∣ P₀`, whose contribution is constant on the progression (if `p ∣ P₀`
  then `p ∣ n + ρ ↔ p ∣ b₀ + ρ`) — this is exactly what the translate `γ` absorbs;
* the primes `p ∤ P₀`, `p ≤ R` — these are `sm`, already in `S`;
* the primes `p ∤ P₀`, `p > R` — the medium/large ranges of §4D; and
* the layers `j > J`, the infinite far tail.
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-! ### Summability of the dilated tail -/

lemma summable_dilatedTailB {b : ℕ} (hb : 2 ≤ b) (d k : ℕ) (hd : d ≠ 0) :
    Summable (fun i : ℕ => omegaR (d * (k + i + 1)) / (b : ℝ) ^ (i + 1)) := by
  refine Summable.congr ?_ (fun i => (dilatedTailB_term (b := b) d k hd i).symm)
  exact ((summable_tailB hb k).add ((summable_inv_pow_succ hb).mul_left _)).sub
    (summable_corrB hb d k)

/-! ### The first `K` layers cancel, for any weight -/

/-- **Exact cancellation of layer `j = i₀ + 1 ≤ K`.**  `n + ρ_{α,j}` is a function of
`proj B j α` alone, and that projection ignores coordinate `i₀`; so every row of `D_s^{⊗K}`
annihilates any function of `n + ρ_{α,j}`. -/
theorem sum_kronPow_mul_shiftG_eq_zero {R : Type*} [CommRing R] {K s : ℕ} (B Q D₀ : ℕ)
    (hD : ∀ α : Fin K → Fin (s + 1), gridV B α ≤ D₀) (i₀ : Fin K)
    (g : ℤ → R) (a : Fin K → Fin s) (n : ℤ) :
    ∑ α, ((kronPow K (diffZ s) a α : ℤ) : R) *
        g (n + (shiftG B Q D₀ α ((i₀ : ℕ) + 1) : ℕ)) = 0 := by
  have key : ∀ α : Fin K → Fin (s + 1),
      (n + (shiftG B Q D₀ α ((i₀ : ℕ) + 1) : ℕ) : ℤ)
        = n + ((((i₀ : ℕ) : ℤ) + 1) + Q * (((((i₀ : ℕ) : ℤ) + 1)) * D₀
            + proj B ((i₀ : ℕ) + 1) α)) := by
    intro α
    rw [shiftG_eq B Q D₀ α (hD α) (by omega)]
    push_cast
    ring
  simp_rw [key]
  exact sum_kronPow_diffZ_mul_eq_zero B i₀
    (fun x => g (n + ((((i₀ : ℕ) : ℤ) + 1) + Q * (((((i₀ : ℕ) : ℤ) + 1)) * D₀ + x)))) a

/-! ### Only the retained layers survive -/

namespace Frame

variable (fr : Frame)

/-- The retained part of the transported vector: the layers `j > K`, before reduction mod one
and before subtracting `γ`. -/
noncomputable def tailFrom (n : ℕ) (ν : Fin fr.r) : ℝ :=
  ∑ α, (fr.A ν α : ℝ) *
    ∑' i : ℕ, omegaR (n + fr.shift α (fr.K + i + 1)) / (4 : ℝ) ^ (fr.K + i + 1)

/-- Summability of one atom's full layer series, on a progression point. -/
lemma summable_layer {n : ℕ} {α : Fin fr.H} {k : ℕ} (hd : fr.d α ≠ 0)
    (hnk : n = fr.t α + fr.d α * k) :
    Summable (fun j : ℕ => omegaR (n + fr.shift α (j + 1)) / (4 : ℝ) ^ (j + 1)) := by
  refine (summable_dilatedTailB (b := 4) (by norm_num) (fr.d α) k hd).congr (fun j => ?_)
  rw [hnk, fr.add_shift_eq α k j]
  norm_num

end Frame

/-- **Only the retained layers survive.**  On the concrete frame, the layers `j ≤ K` of the exact
transported vector are annihilated by every row of `A = D_s^{⊗K}`, so `Ffull` is the retained
tail translated by `γ`. -/
theorem gridFrame_Ffull_eq (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrame G X hne sm γ hη hε D).Ffull n ν
      = ((((gridFrame G X hne sm γ hη hε D).tailFrom n ν : ℝ)) : UnitAddCircle) - γ ν := by
  classical
  set fr := gridFrame G X hne sm γ hη hε D with hfr
  choose k hk1 hk2 using fun α : Fin fr.H => G.exists_mult_mul hn (G.atomEquiv.symm α)
  have hd : ∀ α : Fin fr.H, fr.d α ≠ 0 := fun α => (G.d_pos _).ne'
  have hsum : ∀ α : Fin fr.H,
      Summable (fun j : ℕ => omegaR (n + fr.shift α (j + 1)) / (4 : ℝ) ^ (j + 1)) :=
    fun α => fr.summable_layer (hd α) (hk1 α)
  -- split each atom's series at layer `K`
  have hsplit : ∀ α : Fin fr.H,
      (∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (4 : ℝ) ^ (j + 1))
        = (∑ j ∈ Finset.range fr.K, omegaR (n + fr.shift α (j + 1)) / (4 : ℝ) ^ (j + 1))
          + ∑' i : ℕ, omegaR (n + fr.shift α (fr.K + i + 1)) / (4 : ℝ) ^ (fr.K + i + 1) := by
    intro α
    rw [← (hsum α).sum_add_tsum_nat_add fr.K]
    congr 1
    exact tsum_congr fun i => by rw [show i + fr.K = fr.K + i from Nat.add_comm _ _]
  have hzero : (∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑ j ∈ Finset.range fr.K, omegaR (n + fr.shift α (j + 1)) / (4 : ℝ) ^ (j + 1)) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjK : j < G.K := Finset.mem_range.1 hj
    have := sum_kronPow_mul_shiftG_eq_zero (R := ℝ) G.B G.Q G.D₀ G.hD ⟨j, hjK⟩
      (fun x => omegaR x.toNat / (4 : ℝ) ^ (j + 1)) (G.rowEquiv.symm ν) (n : ℤ)
    rw [← Equiv.sum_comp G.atomEquiv.symm
      (fun α' : G.Atom => ((kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) α' : ℤ) : ℝ) *
        (omegaR (((n : ℤ) + (shiftG G.B G.Q G.D₀ α' (j + 1) : ℕ)).toNat) / (4 : ℝ) ^ (j + 1)))]
      at this
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 2
  have hreal : (∑ α : Fin fr.H, (fr.A ν α : ℝ) *
        ∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (4 : ℝ) ^ (j + 1))
      = fr.tailFrom n ν := by
    unfold Frame.tailFrom
    simp_rw [hsplit, mul_add]
    rw [Finset.sum_add_distrib, hzero, zero_add]
  show (((∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (4 : ℝ) ^ (j + 1)) : ℝ) : UnitAddCircle)
      - fr.γ ν = ((fr.tailFrom n ν : ℝ) : UnitAddCircle) - γ ν
  rw [hreal]
  rfl

/-! ### The frozen / small / large split of `ω` -/

/-- The primes kept in the small-prime vector `S`: prime, at most `R`, and prime to the
progression modulus `P₀`.  Primes dividing `P₀` are *frozen* — on the progression their
contribution is a constant, absorbed by the translate `γ` — and primes above `R` are the
remainder of §4D. -/
def smallPrimes (R P₀ : ℕ) : Finset ℕ := (R + 1).primesBelow.filter (fun p => ¬ p ∣ P₀)

lemma mem_smallPrimes {R P₀ p : ℕ} : p ∈ smallPrimes R P₀ ↔ p.Prime ∧ p ≤ R ∧ ¬ p ∣ P₀ := by
  unfold smallPrimes
  rw [Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h1⟩, h3⟩

lemma smallPrimes_prime {R P₀ p : ℕ} (hp : p ∈ smallPrimes R P₀) : p.Prime :=
  (mem_smallPrimes.1 hp).1

lemma smallPrimes_le {R P₀ p : ℕ} (hp : p ∈ smallPrimes R P₀) : p ≤ R :=
  (mem_smallPrimes.1 hp).2.1

lemma smallPrimes_not_dvd {R P₀ p : ℕ} (hp : p ∈ smallPrimes R P₀) : ¬ p ∣ P₀ :=
  (mem_smallPrimes.1 hp).2.2

/-- The number of prime factors of `m` above `R` that do not divide `P₀`: the §4D remainder
count (its medium and very-large ranges together). -/
def omegaBig (R P₀ m : ℕ) : ℕ := (m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ R < p)).card

lemma omegaOn_primeFactors_eq {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaOn P₀.primeFactors m = (m.primeFactors.filter (fun p => p ∣ P₀)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨⟨h1, h3, hm⟩, h2⟩
  · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨⟨h1, h3, hP₀⟩, h2⟩

lemma omegaOn_smallPrimes_eq {R P₀ m : ℕ} (hm : m ≠ 0) :
    omegaOn (smallPrimes R P₀) m
      = (m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ p ≤ R)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_smallPrimes]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h4, hm⟩, h3, h2⟩
  · rintro ⟨⟨h1, h2, -⟩, h3, h4⟩; exact ⟨⟨h1, h4, h3⟩, h2⟩

/-- **The frozen / small / large partition of `ω`.**  Every prime factor of `m` either divides
`P₀` (frozen), or is prime to `P₀` and at most `R` (counted by `S`), or is prime to `P₀` and
above `R` (the §4D remainder). -/
theorem omega_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    ArithmeticFunction.cardDistinctFactors m
      = omegaOn P₀.primeFactors m + omegaOn (smallPrimes R P₀) m + omegaBig R P₀ m := by
  classical
  rw [cardDistinctFactors_eq_card_primeFactors, omegaOn_primeFactors_eq hP₀ hm,
    omegaOn_smallPrimes_eq hm]
  unfold omegaBig
  rw [← Finset.card_filter_add_card_filter_not (s := m.primeFactors) (p := fun p => p ∣ P₀),
    add_assoc]
  congr 1
  rw [← Finset.card_filter_add_card_filter_not
    (s := m.primeFactors.filter (fun p => ¬ p ∣ P₀)) (p := fun p => p ≤ R)]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter]
    tauto
  · congr 1
    ext p
    simp only [Finset.mem_filter, not_le]
    tauto

/-- In real form, on a nonzero argument. -/
lemma omegaR_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaR m = (omegaOn P₀.primeFactors m : ℝ) + (omegaOn (smallPrimes R P₀) m : ℝ)
      + (omegaBig R P₀ m : ℝ) := by
  unfold omegaR
  rw [omega_split R hP₀ hm]
  push_cast
  ring

end NormalNumbers.G4
