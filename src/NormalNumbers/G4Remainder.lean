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
    ∑' i : ℕ, omegaR (n + fr.shift α (fr.K + i + 1)) / (fr.bse : ℝ) ^ (fr.K + i + 1)

/-- Summability of one atom's full layer series, on a progression point. -/
lemma summable_layer {n : ℕ} {α : Fin fr.H} {k : ℕ} (hd : fr.d α ≠ 0)
    (hnk : n = fr.t α + fr.d α * k) :
    Summable (fun j : ℕ => omegaR (n + fr.shift α (j + 1)) / (fr.bse : ℝ) ^ (j + 1)) := by
  refine (summable_dilatedTailB (b := fr.bse) fr.hbse (fr.d α) k hd).congr (fun j => ?_)
  rw [hnk, fr.add_shift_eq α k j]

end Frame

/-- **Only the retained layers survive.**  On the concrete frame, the layers `j ≤ K` of the exact
transported vector are annihilated by every row of `A = D_s^{⊗K}`, so `Ffull` is the retained
tail translated by `γ`. -/
theorem gridFrame_Ffull_eq (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrame bb hbb G X hne sm γ hη hε D).Ffull n ν
      = ((((gridFrame bb hbb G X hne sm γ hη hε D).tailFrom n ν : ℝ)) : UnitAddCircle) - γ ν := by
  classical
  set fr := gridFrame bb hbb G X hne sm γ hη hε D with hfr
  choose k hk1 hk2 using fun α : Fin fr.H => G.exists_mult_mul hn (G.atomEquiv.symm α)
  have hd : ∀ α : Fin fr.H, fr.d α ≠ 0 := fun α => (G.d_pos _).ne'
  have hsum : ∀ α : Fin fr.H,
      Summable (fun j : ℕ => omegaR (n + fr.shift α (j + 1)) / (bb : ℝ) ^ (j + 1)) :=
    fun α => fr.summable_layer (hd α) (hk1 α)
  -- split each atom's series at layer `K`
  have hsplit : ∀ α : Fin fr.H,
      (∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (bb : ℝ) ^ (j + 1))
        = (∑ j ∈ Finset.range fr.K, omegaR (n + fr.shift α (j + 1)) / (bb : ℝ) ^ (j + 1))
          + ∑' i : ℕ, omegaR (n + fr.shift α (fr.K + i + 1)) / (bb : ℝ) ^ (fr.K + i + 1) := by
    intro α
    rw [← (hsum α).sum_add_tsum_nat_add fr.K]
    congr 1
    exact tsum_congr fun i => by rw [show i + fr.K = fr.K + i from Nat.add_comm _ _]
  have hzero : (∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑ j ∈ Finset.range fr.K, omegaR (n + fr.shift α (j + 1)) / (bb : ℝ) ^ (j + 1)) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjK : j < G.K := Finset.mem_range.1 hj
    have := sum_kronPow_mul_shiftG_eq_zero (R := ℝ) G.B G.Q G.D₀ G.hD ⟨j, hjK⟩
      (fun x => omegaR x.toNat / (bb : ℝ) ^ (j + 1)) (G.rowEquiv.symm ν) (n : ℤ)
    rw [← Equiv.sum_comp G.atomEquiv.symm
      (fun α' : G.Atom => ((kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) α' : ℤ) : ℝ) *
        (omegaR (((n : ℤ) + (shiftG G.B G.Q G.D₀ α' (j + 1) : ℕ)).toNat) / (bb : ℝ) ^ (j + 1)))]
      at this
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 2
  have hreal : (∑ α : Fin fr.H, (fr.A ν α : ℝ) *
        ∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (bb : ℝ) ^ (j + 1))
      = fr.tailFrom n ν := by
    show _ = ∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑' i : ℕ, omegaR (n + fr.shift α (fr.K + i + 1)) / (bb : ℝ) ^ (fr.K + i + 1)
    simp_rw [hsplit, mul_add]
    rw [Finset.sum_add_distrib, hzero, zero_add]
  show (((∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (bb : ℝ) ^ (j + 1)) : ℝ) : UnitAddCircle)
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

/-! ### Layer blocks, and the three-way split of the retained tail -/

/-- One retained layer-block of the grid, with an arbitrary arithmetic weight `w`:
`∑_α A_{aα} ∑_{K < j ≤ J} w(n + ρ_{α,j}) bb^{−j}`.  `Sval` is the case `w = ω_{sm}`. -/
noncomputable def blockSum (bb : ℕ) (G : GridParams) (w : ℕ → ℝ) (n : ℕ) (a : Fin G.K → Fin G.s) : ℝ :=
  ∑ α : G.Atom, ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) *
    ∑ jj : Fin G.N, w (n + shiftAL G.B G.Q G.D₀ (α, jj)) / (bb : ℝ) ^ layer G.K jj

lemma Sval_eq_blockSum (bb : ℕ) (G : GridParams) (sm : Finset ℕ) (n : ℕ) (a : Fin G.K → Fin G.s) :
    Sval bb sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n a
      = blockSum bb G (fun m => (omegaOn sm m : ℝ)) n a := rfl

lemma blockSum_add (bb : ℕ) (G : GridParams) (w₁ w₂ : ℕ → ℝ) (n : ℕ) (a : Fin G.K → Fin G.s) :
    blockSum bb G (fun m => w₁ m + w₂ m) n a = blockSum bb G w₁ n a + blockSum bb G w₂ n a := by
  unfold blockSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun jj _ => ?_)
  ring

lemma blockSum_congr (bb : ℕ) (G : GridParams) {w₁ w₂ : ℕ → ℝ} {n m : ℕ} (a : Fin G.K → Fin G.s)
    (h : ∀ α : G.Atom, ∀ jj : Fin G.N,
      w₁ (n + shiftAL G.B G.Q G.D₀ (α, jj)) = w₂ (m + shiftAL G.B G.Q G.D₀ (α, jj))) :
    blockSum bb G w₁ n a = blockSum bb G w₂ m a := by
  unfold blockSum
  exact Finset.sum_congr rfl fun α _ =>
    congrArg _ (Finset.sum_congr rfl fun jj _ => by rw [h α jj])

/-- The infinite far tail: the layers `j > J = K + N`. -/
noncomputable def farPart (bb : ℕ) (G : GridParams) (n : ℕ) (a : Fin G.K → Fin G.s) : ℝ :=
  ∑ α : G.Atom, ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) *
    ∑' i : ℕ, omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + G.N + i + 1))
      / (bb : ℝ) ^ (G.K + G.N + i + 1)

/-- **Retained layers = the `J`-truncation plus the far tail.** -/
theorem tailFrom_split (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrame bb hbb G X hne sm γ hη hε D).tailFrom n ν
      = blockSum bb G omegaR n (G.rowEquiv.symm ν) + farPart bb G n (G.rowEquiv.symm ν) := by
  classical
  have hd : ∀ α : G.Atom, G.d α ≠ 0 := fun α => (G.d_pos α).ne'
  have hsum : ∀ α : G.Atom, Summable
      (fun j : ℕ => omegaR (n + shiftG G.B G.Q G.D₀ α (j + 1)) / (bb : ℝ) ^ (j + 1)) := by
    intro α
    obtain ⟨k, hk1, -⟩ := G.exists_mult_mul hn α
    refine (summable_dilatedTailB (b := bb) hbb (G.d α) k (hd α)).congr (fun j => ?_)
    rw [hk1]
    show omegaR (G.d α * (k + j + 1)) / (bb : ℝ) ^ (j + 1)
      = omegaR (offset G.B G.Q α + mult G.B G.Q G.D₀ α * k
          + shiftG G.B G.Q G.D₀ α (j + 1)) / (bb : ℝ) ^ (j + 1)
    rw [add_shiftG_eq G.B G.Q G.D₀ α (G.hD α) (by omega)]
    show omegaR (G.d α * (k + j + 1)) / (bb : ℝ) ^ (j + 1)
      = omegaR (G.d α * (k + (j + 1))) / (bb : ℝ) ^ (j + 1)
    rw [show k + j + 1 = k + (j + 1) by omega]
  have hsplit : ∀ α : G.Atom,
      (∑' i : ℕ, omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + i + 1)) / (bb : ℝ) ^ (G.K + i + 1))
        = (∑ jj : Fin G.N, omegaR (n + shiftAL G.B G.Q G.D₀ (α, jj)) / (bb : ℝ) ^ layer G.K jj)
          + ∑' i : ℕ, omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + G.N + i + 1))
              / (bb : ℝ) ^ (G.K + G.N + i + 1) := by
    intro α
    have hs' : Summable (fun i : ℕ =>
        omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + i + 1)) / (bb : ℝ) ^ (G.K + i + 1)) := by
      refine ((summable_nat_add_iff G.K).2 (hsum α)).congr (fun i => ?_)
      rw [show i + G.K = G.K + i from Nat.add_comm _ _]
    rw [← hs'.sum_add_tsum_nat_add G.N]
    congr 1
    · rw [show (∑ jj : Fin G.N, omegaR (n + shiftAL G.B G.Q G.D₀ (α, jj)) / (bb : ℝ) ^ layer G.K jj)
          = ∑ jj : Fin G.N, omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + 1 + (jj : ℕ)))
              / (bb : ℝ) ^ (G.K + 1 + (jj : ℕ)) from rfl,
        Fin.sum_univ_eq_sum_range (fun i => omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + 1 + i))
          / (bb : ℝ) ^ (G.K + 1 + i)) G.N]
      exact Finset.sum_congr rfl fun i _ => by rw [show G.K + i + 1 = G.K + 1 + i by omega]
    · exact tsum_congr fun i => by rw [show G.K + (i + G.N) + 1 = G.K + G.N + i + 1 by omega]
  show (∑ α : Fin G.hDim,
      ((kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) (G.atomEquiv.symm α) : ℤ) : ℝ) *
      ∑' i : ℕ, omegaR (n + shiftG G.B G.Q G.D₀ (G.atomEquiv.symm α) (G.K + i + 1))
        / (bb : ℝ) ^ (G.K + i + 1)) = _
  rw [Equiv.sum_comp G.atomEquiv.symm (fun α : G.Atom =>
    ((kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) α : ℤ) : ℝ) *
      ∑' i : ℕ, omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + i + 1)) / (bb : ℝ) ^ (G.K + i + 1))]
  unfold blockSum farPart
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [hsplit α, mul_add]

/-! ### The frozen primes are constant on the progression -/

lemma shiftG_pos (G : GridParams) (α : G.Atom) {j : ℕ} (hj : 1 ≤ j) :
    0 < shiftG G.B G.Q G.D₀ α j := by
  unfold shiftG
  refine Nat.sub_pos_of_lt (lt_of_lt_of_le (G.t_lt_d α) ?_)
  exact Nat.le_mul_of_pos_left _ (by omega)

lemma shiftAL_pos (G : GridParams) (i : G.Idx) : 0 < shiftAL G.B G.Q G.D₀ i :=
  shiftG_pos G i.1 (by unfold layer; omega)

/-- For a prime dividing `P₀`, divisibility of `n + ρ` depends only on `n mod P₀`; so the
frozen-prime count is constant on the progression. -/
lemma omegaOn_primeFactors_congr {P₀ n m ρ : ℕ} (h : n % P₀ = m % P₀) :
    omegaOn P₀.primeFactors (n + ρ) = omegaOn P₀.primeFactors (m + ρ) := by
  classical
  unfold omegaOn
  congr 1
  refine Finset.filter_congr fun p hp => ?_
  have hpP : p ∣ P₀ := (Nat.mem_primeFactors.1 hp).2.1
  have hnm : n ≡ m [MOD p] := Nat.ModEq.of_dvd hpP h
  constructor
  · intro hd
    exact (Nat.modEq_zero_iff_dvd).1 (((hnm.add_right ρ).symm).trans
      ((Nat.modEq_zero_iff_dvd).2 hd))
  · intro hd
    exact (Nat.modEq_zero_iff_dvd).1 ((hnm.add_right ρ).trans ((Nat.modEq_zero_iff_dvd).2 hd))

/-- The frozen translate `γ`: the contribution of the primes dividing `P₀`, evaluated at the
progression's residue `b₀`.  On the sample it is exactly the frozen part of `Ffull`. -/
noncomputable def frozenTranslate (bb : ℕ) (G : GridParams) (ν : Fin G.rDim) : ℝ :=
  blockSum bb G (fun m => (omegaOn G.P₀.primeFactors m : ℝ)) G.b₀ (G.rowEquiv.symm ν)

/-- The frozen translate as a point of the torus. -/
noncomputable def frozenGamma (bb : ℕ) (G : GridParams) : Torus G.rDim :=
  fun ν => ((frozenTranslate bb G ν : ℝ) : UnitAddCircle)

lemma blockSum_frozen_eq (bb : ℕ) (G : GridParams) {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G (fun m => (omegaOn G.P₀.primeFactors m : ℝ)) n a
      = blockSum bb G (fun m => (omegaOn G.P₀.primeFactors m : ℝ)) G.b₀ a := by
  refine blockSum_congr bb G a fun α jj => ?_
  have h1 : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have h2 : G.b₀ % G.P₀ = G.b₀ := Nat.mod_eq_of_lt G.b₀_lt_P₀
  have h3 : omegaOn G.P₀.primeFactors (n + shiftAL G.B G.Q G.D₀ (α, jj))
      = omegaOn G.P₀.primeFactors (G.b₀ + shiftAL G.B G.Q G.D₀ (α, jj)) :=
    omegaOn_primeFactors_congr (h1.trans h2.symm)
  rw [h3]

/-! ### The three-range decomposition of the transported vector -/

/-- **The exact remainder decomposition.**  On the sample, the transported vector is the
small-prime vector plus the large-prime block plus the far tail, translated by the frozen
constant — every term named and exact. -/
theorem blockSum_omegaR_split (bb : ℕ) (G : GridParams) (R : ℕ) (n : ℕ) (a : Fin G.K → Fin G.s) :
    blockSum bb G omegaR n a
      = blockSum bb G (fun m => (omegaOn G.P₀.primeFactors m : ℝ)) n a
        + Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n a
        + blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n a := by
  rw [Sval_eq_blockSum, ← blockSum_add, ← blockSum_add]
  refine blockSum_congr bb G a fun α jj => ?_
  exact omegaR_split R G.P₀_pos.ne' (by have := shiftAL_pos G (α, jj); omega)

/-- Distance on the unit circle is at most the real distance. -/
lemma dist_coe_le' (x y : ℝ) :
    dist ((x : ℝ) : UnitAddCircle) ((y : ℝ) : UnitAddCircle) ≤ |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq]
  simpa using round_le (x - y) 0

/-- **`Ffull` on the sample, fully decomposed.**  With `sm` the small primes below `R` prime to
`P₀` and `γ` the frozen translate, the exact transported vector is the small-prime vector plus
exactly two named remainders: the large-prime block (`p > R`, `p ∤ P₀`, layers `K < j ≤ J`) and
the infinite far tail (layers `j > J`). -/
theorem gridFrame_Ffull_decomp (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrame bb hbb G X hne (smallPrimes R G.P₀) (frozenGamma bb G) hη hε D).Ffull n ν
      = (((Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
          + blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
          + farPart bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle) := by
  rw [gridFrame_Ffull_eq bb hbb G X hne _ _ hη hε D hn ν,
    tailFrom_split bb hbb G X hne _ _ hη hε D hn ν,
    blockSum_omegaR_split bb G R n (G.rowEquiv.symm ν),
    blockSum_frozen_eq bb G hn (G.rowEquiv.symm ν)]
  show (((frozenTranslate bb G ν
      + Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
      + blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
      + farPart bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle)
      - ((frozenTranslate bb G ν : ℝ) : UnitAddCircle) = _
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  ring

/-! ### `PropD` from the two named remainder averages -/

/-- The sample average of the average coordinate size of the **large-prime block**: primes
`p > R` with `p ∤ P₀`, in the retained layers `K < j ≤ J`.  §4D's medium (`R < p ≤ Y`, signed
two-congruence counting) and very-large (`p > Y`, pointwise) ranges together. -/
noncomputable def bigAvg (bb : ℕ) (G : GridParams) (X R : ℕ) : ℝ :=
  ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
    (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
      |blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|

/-- The sample average of the average coordinate size of the **infinite far tail**: layers
`j > J`. -/
noncomputable def farAvg (bb : ℕ) (G : GridParams) (X : ℕ) : ℝ :=
  ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
    (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, |farPart bb G n (G.rowEquiv.symm ν)|

/-- **`PropD` reduces to exactly two arithmetic estimates.**  With `γ` the frozen translate, the
only gap between the small-prime vector and the exact transported vector is the large-prime
block plus the far tail; if each has small sample average in the *average* coordinate metric
(the normalisation that avoids multiplying the error by `r`), `PropD` holds.

This is the whole content of brief §4D as a Lean statement: the frozen primes are gone (into
`γ`), the small primes are gone (into `S`), and what remains is `bigAvg` and `farAvg`. -/
theorem gridFrame_propD (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δfar : ℝ}
    (hbig : bigAvg bb G X R ≤ δbig * (ε * η)) (hfar : farAvg bb G X ≤ δfar * (ε * η)) :
    (gridFrame bb hbb G X hne (smallPrimes R G.P₀) (frozenGamma bb G) hη hε D).PropD (δbig + δfar) := by
  classical
  set fr := gridFrame bb hbb G X hne (smallPrimes R G.P₀) (frozenGamma bb G) hη hε D with hfr
  have hcard : (0 : ℝ) ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ := by positivity
  have hstep : ∀ n ∈ apSample X G.P₀ G.b₀, dAv (fr.S n) (fr.Ffull n)
      ≤ (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
        + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, |farPart bb G n (G.rowEquiv.symm ν)| := by
    intro n hn
    have hpt : ∀ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)
        ≤ |blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
          + |farPart bb G n (G.rowEquiv.symm ν)| := by
      intro ν
      rw [gridFrame_Ffull_decomp bb hbb G X hne R hη hε D hn ν]
      refine (dist_coe_le' _ _).trans ?_
      have : Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
          - (Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
            + blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
            + farPart bb G n (G.rowEquiv.symm ν))
          = -(blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
              + farPart bb G n (G.rowEquiv.symm ν)) := by ring
      rw [this, abs_neg]
      exact abs_add_le _ _
    calc dAv (fr.S n) (fr.Ffull n)
        = (∑ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)) / (G.rDim : ℝ) := rfl
      _ ≤ (∑ ν : Fin G.rDim,
            (|blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
              + |farPart bb G n (G.rowEquiv.symm ν)|)) / (G.rDim : ℝ) := by
            gcongr with ν
            exact hpt ν
      _ = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
          + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, |farPart bb G n (G.rowEquiv.symm ν)| := by
            rw [Finset.sum_add_distrib]
            ring
  show ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
      dAv (fr.S n) (fr.Ffull n) ≤ (δbig + δfar) * fr.res
  have hres : fr.res = ε * η := rfl
  rw [hres]
  calc ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        dAv (fr.S n) (fr.Ffull n)
      ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
          ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
              |blockSum bb G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
            + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, |farPart bb G n (G.rowEquiv.symm ν)|) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hcard
    _ = bigAvg bb G X R + farAvg bb G X := by
        unfold bigAvg farAvg
        rw [Finset.sum_add_distrib]
        ring
    _ ≤ δbig * (ε * η) + δfar * (ε * η) := add_le_add hbig hfar
    _ = (δbig + δfar) * (ε * η) := by ring

end NormalNumbers.G4
