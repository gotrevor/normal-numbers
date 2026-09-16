/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Remainder
import NormalNumbers.G4FrameW

/-!
# §4D for the prime-subset weight: the three-range split of `ω_S`

`G4Remainder` splits `ω(m)` into the frozen primes (`p ∣ P₀`), the small primes
(`p ≤ R`, `p ∤ P₀`, counted by the vector `S`) and the large primes (`omegaBig`).  For campaign A
the same split is needed for `ω_S`, and the point of this module is that it costs **no new
machinery**: the local layer of `ω_S` is `omegaOn` of the *filtered* finset of small primes, so
the small-prime vector `Sval bb ((smallPrimes R P₀).filter S)` is the `S`-restricted vector, and
every §4C/§4D estimate that is stated for an arbitrary finset of primes applies verbatim.

* `omegaSN_split` — `ω_S(m) = omegaOn (P₀.primeFactors.filter S) m
  + omegaOn ((smallPrimes R P₀).filter S) m + omegaBigS R P₀ S m`;
* `omegaBigS_le_omegaBig` — the `S`-junk is dominated by the `ω`-junk, so every remainder bound
  of `G4Remainder` transfers by monotonicity;
* `blockSum_omegaS_split` — the exact decomposition of the retained block.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

variable (S : ℕ → Prop) [DecidablePred S]

/-- The `S`-restricted large-prime count. -/
def omegaBigS (R P₀ : ℕ) (m : ℕ) : ℕ :=
  (m.primeFactors.filter (fun p => S p ∧ ¬ p ∣ P₀ ∧ R < p)).card

lemma omegaBigS_le_omegaBig (R P₀ m : ℕ) : omegaBigS S R P₀ m ≤ omegaBig R P₀ m := by
  classical
  refine Finset.card_le_card (fun p hp => ?_)
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.2.1, hp.2.2.2⟩

lemma omegaOn_filter_primeFactors_eq {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaOn (P₀.primeFactors.filter S) m
      = ((m.primeFactors.filter S).filter (fun p => p ∣ P₀)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨⟨h1, h2, -⟩, hS⟩, h3⟩; exact ⟨⟨⟨h1, h3, hm⟩, hS⟩, h2⟩
  · rintro ⟨⟨⟨h1, h2, -⟩, hS⟩, h3⟩; exact ⟨⟨⟨h1, h3, hP₀⟩, hS⟩, h2⟩

lemma omegaOn_filter_smallPrimes_eq {R P₀ m : ℕ} (hm : m ≠ 0) :
    omegaOn ((smallPrimes R P₀).filter S) m
      = ((m.primeFactors.filter S).filter (fun p => ¬ p ∣ P₀ ∧ p ≤ R)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_smallPrimes]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3⟩, hS⟩, h4⟩; exact ⟨⟨⟨h1, h4, hm⟩, hS⟩, h3, h2⟩
  · rintro ⟨⟨⟨h1, h2, -⟩, hS⟩, h3, h4⟩; exact ⟨⟨⟨h1, h4, h3⟩, hS⟩, h2⟩

/-- **The frozen / small / large partition of `ω_S`.** -/
theorem omegaSN_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaSN S m = omegaOn (P₀.primeFactors.filter S) m
      + omegaOn ((smallPrimes R P₀).filter S) m + omegaBigS S R P₀ m := by
  classical
  rw [omegaOn_filter_primeFactors_eq S hP₀ hm, omegaOn_filter_smallPrimes_eq S hm]
  unfold omegaSN omegaBigS
  rw [← Finset.card_filter_add_card_filter_not (s := m.primeFactors.filter S)
      (p := fun p => p ∣ P₀), add_assoc]
  congr 1
  rw [← Finset.card_filter_add_card_filter_not
    (s := (m.primeFactors.filter S).filter (fun p => ¬ p ∣ P₀)) (p := fun p => p ≤ R)]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter]
    tauto
  · congr 1
    ext p
    simp only [Finset.mem_filter, not_le]
    tauto

/-- The real form of the split, on a nonzero argument. -/
lemma omegaS_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaS S m = (omegaOn (P₀.primeFactors.filter S) m : ℝ)
      + (omegaOn ((smallPrimes R P₀).filter S) m : ℝ) + (omegaBigS S R P₀ m : ℝ) := by
  unfold omegaS
  rw [omegaSN_split S R hP₀ hm]
  push_cast
  ring

/-- **The exact remainder decomposition for `ω_S`.**  The `S`-local layer is the ordinary
small-prime vector of the *filtered* finset `(smallPrimes R P₀).filter S`. -/
theorem blockSum_omegaS_split (bb : ℕ) (G : GridParams) (R : ℕ) (n : ℕ)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G (omegaS S) n a
      = blockSum bb G (fun m => (omegaOn (G.P₀.primeFactors.filter S) m : ℝ)) n a
        + Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n a
        + blockSum bb G (fun m => (omegaBigS S R G.P₀ m : ℝ)) n a := by
  rw [Sval_eq_blockSum, ← blockSum_add, ← blockSum_add]
  refine blockSum_congr bb G a fun α jj => ?_
  exact omegaS_split S R G.P₀_pos.ne' (by have := shiftAL_pos G (α, jj); omega)

/-! ### The retained tail and the far tail, for a general weight -/

namespace TWeight

lemma summable_dilatedTailB (W : TWeight) {b : ℕ} (hb : 2 ≤ b) (d k : ℕ) (hd : d ≠ 0) :
    Summable (fun i : ℕ => (W.wN (d * (k + i + 1)) : ℝ) / (b : ℝ) ^ (i + 1)) := by
  refine Summable.congr ?_ (fun i => (W.dilatedTailB_term (b := b) d k hd i).symm)
  exact ((W.summable_tailB hb k).add ((summable_inv_pow_succ hb).mul_left _)).sub
    (W.summable_corrB hb d k)

end TWeight

namespace Frame

variable (fr : Frame) (W : TWeight)

/-- The retained part of the transported vector for a general weight. -/
noncomputable def tailFromW (n : ℕ) (ν : Fin fr.r) : ℝ :=
  ∑ α, (fr.A ν α : ℝ) *
    ∑' i : ℕ, (W.wN (n + fr.shift α (fr.K + i + 1)) : ℝ) / (fr.bse : ℝ) ^ (fr.K + i + 1)

lemma summable_layerW {n : ℕ} {α : Fin fr.H} {k : ℕ} (hd : fr.d α ≠ 0)
    (hnk : n = fr.t α + fr.d α * k) :
    Summable (fun j : ℕ => (W.wN (n + fr.shift α (j + 1)) : ℝ) / (fr.bse : ℝ) ^ (j + 1)) := by
  refine (W.summable_dilatedTailB (b := fr.bse) fr.hbse (fr.d α) k hd).congr (fun j => ?_)
  rw [hnk, fr.add_shift_eq α k j]

end Frame

/-- **Only the retained layers survive**, for a general weight. -/
theorem gridFrameW_Ffull_eq (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).Ffull n ν
      = ((((gridFrameW W bb hbb G X hne sm γ hη hε D).tailFromW W n ν : ℝ)) : UnitAddCircle)
        - γ ν := by
  classical
  set fr := gridFrameW W bb hbb G X hne sm γ hη hε D with hfr
  choose k hk1 hk2 using fun α : Fin fr.H => G.exists_mult_mul hn (G.atomEquiv.symm α)
  have hd : ∀ α : Fin fr.H, fr.d α ≠ 0 := fun α => (G.d_pos _).ne'
  have hsum : ∀ α : Fin fr.H,
      Summable (fun j : ℕ => (W.wN (n + fr.shift α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)) :=
    fun α => fr.summable_layerW W (hd α) (hk1 α)
  have hsplit : ∀ α : Fin fr.H,
      (∑' j : ℕ, (W.wN (n + fr.shift α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1))
        = (∑ j ∈ Finset.range fr.K, (W.wN (n + fr.shift α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1))
          + ∑' i : ℕ, (W.wN (n + fr.shift α (fr.K + i + 1)) : ℝ) / (bb : ℝ) ^ (fr.K + i + 1) := by
    intro α
    rw [← (hsum α).sum_add_tsum_nat_add fr.K]
    congr 1
    exact tsum_congr fun i => by rw [show i + fr.K = fr.K + i from Nat.add_comm _ _]
  have hzero : (∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑ j ∈ Finset.range fr.K, (W.wN (n + fr.shift α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjK : j < G.K := Finset.mem_range.1 hj
    have := sum_kronPow_mul_shiftG_eq_zero (R := ℝ) G.B G.Q G.D₀ G.hD ⟨j, hjK⟩
      (fun x => (W.wN x.toNat : ℝ) / (bb : ℝ) ^ (j + 1)) (G.rowEquiv.symm ν) (n : ℤ)
    rw [← Equiv.sum_comp G.atomEquiv.symm
      (fun α' : G.Atom => ((kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) α' : ℤ) : ℝ) *
        ((W.wN (((n : ℤ) + (shiftG G.B G.Q G.D₀ α' (j + 1) : ℕ)).toNat) : ℝ)
          / (bb : ℝ) ^ (j + 1)))] at this
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 2
  have hreal : (∑ α : Fin fr.H, (fr.A ν α : ℝ) *
        ∑' j : ℕ, (W.wN (n + fr.shift α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1))
      = fr.tailFromW W n ν := by
    show _ = ∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑' i : ℕ, (W.wN (n + fr.shift α (fr.K + i + 1)) : ℝ) / (bb : ℝ) ^ (fr.K + i + 1)
    simp_rw [hsplit, mul_add]
    rw [Finset.sum_add_distrib, hzero, zero_add]
  show (((∑ α : Fin fr.H, (fr.A ν α : ℝ) *
      ∑' j : ℕ, (W.wN (n + fr.shift α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)) : ℝ) : UnitAddCircle)
      - fr.γ ν = ((fr.tailFromW W n ν : ℝ) : UnitAddCircle) - γ ν
  rw [hreal]
  rfl

/-- The infinite far tail for a general weight: the layers `j > J = K + N`. -/
noncomputable def farPartW (W : TWeight) (bb : ℕ) (G : GridParams) (n : ℕ)
    (a : Fin G.K → Fin G.s) : ℝ :=
  ∑ α : G.Atom, ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) *
    ∑' i : ℕ, (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + G.N + i + 1)) : ℝ)
      / (bb : ℝ) ^ (G.K + G.N + i + 1)

/-- **Retained layers = the `J`-truncation plus the far tail**, for a general weight. -/
theorem tailFrom_splitW (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).tailFromW W n ν
      = blockSum bb G (fun m => (W.wN m : ℝ)) n (G.rowEquiv.symm ν)
        + farPartW W bb G n (G.rowEquiv.symm ν) := by
  classical
  have hd : ∀ α : G.Atom, G.d α ≠ 0 := fun α => (G.d_pos α).ne'
  have hsum : ∀ α : G.Atom, Summable
      (fun j : ℕ => (W.wN (n + shiftG G.B G.Q G.D₀ α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)) := by
    intro α
    obtain ⟨k, hk1, -⟩ := G.exists_mult_mul hn α
    refine (W.summable_dilatedTailB (b := bb) hbb (G.d α) k (hd α)).congr (fun j => ?_)
    rw [hk1]
    show (W.wN (G.d α * (k + j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)
      = (W.wN (offset G.B G.Q α + mult G.B G.Q G.D₀ α * k
          + shiftG G.B G.Q G.D₀ α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)
    rw [add_shiftG_eq G.B G.Q G.D₀ α (G.hD α) (by omega)]
    show (W.wN (G.d α * (k + j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)
      = (W.wN (G.d α * (k + (j + 1))) : ℝ) / (bb : ℝ) ^ (j + 1)
    rw [show k + j + 1 = k + (j + 1) by omega]
  have hsplit : ∀ α : G.Atom,
      (∑' i : ℕ, (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + i + 1)) : ℝ) / (bb : ℝ) ^ (G.K + i + 1))
        = (∑ jj : Fin G.N, (W.wN (n + shiftAL G.B G.Q G.D₀ (α, jj)) : ℝ)
              / (bb : ℝ) ^ layer G.K jj)
          + ∑' i : ℕ, (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + G.N + i + 1)) : ℝ)
              / (bb : ℝ) ^ (G.K + G.N + i + 1) := by
    intro α
    have hs' : Summable (fun i : ℕ =>
        (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + i + 1)) : ℝ) / (bb : ℝ) ^ (G.K + i + 1)) := by
      refine ((summable_nat_add_iff G.K).2 (hsum α)).congr (fun i => ?_)
      rw [show i + G.K = G.K + i from Nat.add_comm _ _]
    rw [← hs'.sum_add_tsum_nat_add G.N]
    congr 1
    · rw [show (∑ jj : Fin G.N, (W.wN (n + shiftAL G.B G.Q G.D₀ (α, jj)) : ℝ)
            / (bb : ℝ) ^ layer G.K jj)
          = ∑ jj : Fin G.N, (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + 1 + (jj : ℕ))) : ℝ)
              / (bb : ℝ) ^ (G.K + 1 + (jj : ℕ)) from rfl,
        Fin.sum_univ_eq_sum_range (fun i =>
          (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + 1 + i)) : ℝ) / (bb : ℝ) ^ (G.K + 1 + i)) G.N]
      exact Finset.sum_congr rfl fun i _ => by rw [show G.K + i + 1 = G.K + 1 + i by omega]
    · exact tsum_congr fun i => by rw [show G.K + (i + G.N) + 1 = G.K + G.N + i + 1 by omega]
  show (∑ α : Fin G.hDim,
      ((kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) (G.atomEquiv.symm α) : ℤ) : ℝ) *
      ∑' i : ℕ, (W.wN (n + shiftG G.B G.Q G.D₀ (G.atomEquiv.symm α) (G.K + i + 1)) : ℝ)
        / (bb : ℝ) ^ (G.K + i + 1)) = _
  rw [Equiv.sum_comp G.atomEquiv.symm (fun α : G.Atom =>
    ((kronPow G.K (diffZ G.s) (G.rowEquiv.symm ν) α : ℤ) : ℝ) *
      ∑' i : ℕ, (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + i + 1)) : ℝ)
        / (bb : ℝ) ^ (G.K + i + 1))]
  unfold blockSum farPartW
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [hsplit α, mul_add]

/-! ### The full decomposition for the prime-subset weight -/

/-- The frozen part of `ω_S` is constant on the progression. -/
lemma omegaOn_filter_primeFactors_congr {P₀ n m ρ : ℕ} (h : n % P₀ = m % P₀) :
    omegaOn (P₀.primeFactors.filter S) (n + ρ) = omegaOn (P₀.primeFactors.filter S) (m + ρ) := by
  classical
  unfold omegaOn
  congr 1
  refine Finset.filter_congr fun p hp => ?_
  have hpP : p ∣ P₀ := (Nat.mem_primeFactors.1 (Finset.mem_filter.1 hp).1).2.1
  have hnm : n ≡ m [MOD p] := Nat.ModEq.of_dvd hpP h
  constructor
  · intro hd
    exact (Nat.modEq_zero_iff_dvd).1 (((hnm.add_right ρ).symm).trans
      ((Nat.modEq_zero_iff_dvd).2 hd))
  · intro hd
    exact (Nat.modEq_zero_iff_dvd).1 ((hnm.add_right ρ).trans ((Nat.modEq_zero_iff_dvd).2 hd))

/-- The `S`-frozen translate. -/
noncomputable def frozenTranslateS (bb : ℕ) (G : GridParams) (ν : Fin G.rDim) : ℝ :=
  blockSum bb G (fun m => (omegaOn (G.P₀.primeFactors.filter S) m : ℝ)) G.b₀ (G.rowEquiv.symm ν)

/-- The `S`-frozen translate as a point of the torus. -/
noncomputable def frozenGammaS (bb : ℕ) (G : GridParams) : Torus G.rDim :=
  fun ν => ((frozenTranslateS S bb G ν : ℝ) : UnitAddCircle)

lemma blockSum_frozenS_eq (bb : ℕ) (G : GridParams) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (a : Fin G.K → Fin G.s) :
    blockSum bb G (fun m => (omegaOn (G.P₀.primeFactors.filter S) m : ℝ)) n a
      = blockSum bb G (fun m => (omegaOn (G.P₀.primeFactors.filter S) m : ℝ)) G.b₀ a := by
  refine blockSum_congr bb G a fun α jj => ?_
  have h1 : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have h2 : G.b₀ % G.P₀ = G.b₀ := Nat.mod_eq_of_lt G.b₀_lt_P₀
  rw [omegaOn_filter_primeFactors_congr S (h1.trans h2.symm)]

/-- **`Ffull` for the prime-subset weight, fully decomposed.**  Exactly the shape of
`gridFrame_Ffull_decomp`, with the small-prime vector taken on the filtered finset
`(smallPrimes R P₀).filter S` and the junk `omegaBigS ≤ omegaBig`. -/
theorem gridFrameW_subset_Ffull_decomp (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrameW (TWeight.subset S) bb hbb G X hne ((smallPrimes R G.P₀).filter S)
        (frozenGammaS S bb G) hη hε D).Ffull n ν
      = (((Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
            (G.rowEquiv.symm ν)
          + blockSum bb G (fun m => (omegaBigS S R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
          + farPartW (TWeight.subset S) bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle) := by
  have hw : (fun m => ((TWeight.subset S).wN m : ℝ)) = omegaS S := by
    funext m; rw [TWeight.subset_wN]
  rw [gridFrameW_Ffull_eq (TWeight.subset S) bb hbb G X hne _ _ hη hε D hn ν,
    tailFrom_splitW (TWeight.subset S) bb hbb G X hne _ _ hη hε D hn ν, hw,
    blockSum_omegaS_split S bb G R n (G.rowEquiv.symm ν),
    blockSum_frozenS_eq S bb G hn (G.rowEquiv.symm ν)]
  show (((frozenTranslateS S bb G ν
      + Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
          (G.rowEquiv.symm ν)
      + blockSum bb G (fun m => (omegaBigS S R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
      + farPartW (TWeight.subset S) bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle)
      - ((frozenTranslateS S bb G ν : ℝ) : UnitAddCircle) = _
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  ring

end NormalNumbers.G4
