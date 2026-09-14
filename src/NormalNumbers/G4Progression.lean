/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SmallPrimeVector
import NormalNumbers.G4Transport
import Mathlib.Data.Nat.ChineseRemainder

/-!
# G4 disjunctivity, §3: one compatible progression

Draft §3.  A `GridParams` bundles the grid data `K, s, B, Q, D₀, N` (with `J = K + N`) and the
five arithmetic side conditions used by `G4Grid`.  From it we build

* `Mprod = ∏_α d_α²` and the CRT residue `b₀ < Mprod` with `b₀ ≡ t_α (mod d_α²)` for every atom
  (`Nat.chineseRemainderOfFinset`; the `d_α²` are pairwise coprime by `coprime_mult`);
* `freezeQ = (∏_{p ≤ 2T} p) · ∏_{i≠i'} |ρ_i − ρ_{i'}|`, the primes to freeze;
* `P₀ = Mprod · freezeQ`, the progression modulus, with residue `b₀`.

Then on the sample `apSample X P₀ b₀ = {n < X : n ≡ b₀ (P₀)}`:

* **`exists_mult_mul`** — every `n` is `t_α + d_α k` with `d_α ∣ k` (so `k ≡ 0` modulo every
  prime of `d_α`): the input of `Frame.propA_of_progression` with `c = 0`;
* **`two_mul_card_le_of_not_dvd`** and **`goodPrime_of_not_dvd_P₀`** — a prime not dividing
  `P₀` exceeds `2T` and is good for the shifts: the inputs of
  `norm_sampleAvg_torusChar_Sval_le` for `sm = {p ≤ R prime : p ∤ P₀}`.

Size bounds on `P₀` (draft (3.2)) belong to the §5 schedule module.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- The grid parameters and the side conditions of `G4Grid`. -/
structure GridParams where
  K : ℕ
  s : ℕ
  B : ℕ
  Q : ℕ
  D₀ : ℕ
  /-- number of retained layers, `J = K + N` -/
  N : ℕ
  /-- an upper bound for every `u α` -/
  U : ℕ
  hB : s * (K + N) < B
  hsB : s < B
  hJQ : K + N < Q
  hQ : 1 < Q
  hD : ∀ α : Fin K → Fin (s + 1), gridV B α ≤ D₀
  hU : ∀ α : Fin K → Fin (s + 1), gridU B α ≤ U
  hQdvd : ∀ m, 0 < m → m ≤ U → m ∣ Q

namespace GridParams

variable (G : GridParams)

/-- The atoms. -/
abbrev Atom := Fin G.K → Fin (G.s + 1)

/-- The atom/layer index set of the grid. -/
abbrev Idx := AtomLayer G.K G.s G.N

/-- `d_α`. -/
def d (α : G.Atom) : ℕ := mult G.B G.Q G.D₀ α

/-- `t_α`. -/
def t (α : G.Atom) : ℕ := offset G.B G.Q α

/-- The shifts on the index set. -/
def ρ (i : G.Idx) : ℕ := shiftAL G.B G.Q G.D₀ i

lemma d_pos (α : G.Atom) : 0 < G.d α := mult_pos _ _ _ _

lemma t_lt_d (α : G.Atom) : G.t α < G.d α := by
  have := offset_le_mul_mult G.B G.Q G.D₀ α (G.hD α) (le_refl 1)
  unfold t d
  rw [one_mul] at this
  -- `t ≤ d` and `d ≡ 1 (mod Q)` while `t ≡ 0 (mod Q)`, `Q > 1`
  rcases this.lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 := mult_mod_Q G.B G.Q G.D₀ G.hQ α
    rw [← h] at h1
    unfold offset at h1
    rw [Nat.mul_mod_right] at h1
    omega

lemma coprime_d {α β : G.Atom} (h : α ≠ β) : Nat.Coprime (G.d α) (G.d β) :=
  coprime_mult G.B G.Q G.D₀ G.U G.hsB G.hQ G.hU G.hQdvd h

lemma ρ_injective : Function.Injective G.ρ :=
  shiftAL_injective G.B G.Q G.D₀ (G.K + G.N) G.hB G.hJQ G.hD le_rfl

/-! ### The CRT residue modulo `∏ d_α²` -/

/-- `∏_α d_α²`. -/
def Mprod : ℕ := ∏ α : G.Atom, G.d α ^ 2

lemma Mprod_pos : 0 < G.Mprod :=
  Finset.prod_pos fun α _ => pow_pos (G.d_pos α) 2

lemma sq_d_dvd_Mprod (α : G.Atom) : G.d α ^ 2 ∣ G.Mprod :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ α)

/-- The CRT residue: `b₀ ≡ t_α (mod d_α²)` for every atom. -/
noncomputable def b₀ : ℕ :=
  Nat.chineseRemainderOfFinset G.t (fun α => G.d α ^ 2) Finset.univ
    (fun α _ => pow_ne_zero 2 (G.d_pos α).ne')
    (fun α _ β _ h => (G.coprime_d h).pow 2 2)

lemma b₀_modEq (α : G.Atom) : G.b₀ ≡ G.t α [MOD G.d α ^ 2] :=
  (Nat.chineseRemainderOfFinset G.t (fun α => G.d α ^ 2) Finset.univ
    (fun α _ => pow_ne_zero 2 (G.d_pos α).ne')
    (fun α _ β _ h => (G.coprime_d h).pow 2 2)).2 α (Finset.mem_univ α)

lemma b₀_lt_Mprod : G.b₀ < G.Mprod :=
  Nat.chineseRemainderOfFinset_lt_prod G.t (fun α => G.d α ^ 2)
    (fun α _ => pow_ne_zero 2 (G.d_pos α).ne')
    (fun α _ β _ h => (G.coprime_d h).pow 2 2)

/-! ### The frozen primes -/

/-- `∏_{p ≤ 2T} p · ∏_{i ≠ i'} |ρ_i − ρ_{i'}|`, `T = |Idx|`. -/
def freezeQ : ℕ :=
  (∏ p ∈ (2 * Fintype.card G.Idx + 1).primesBelow, p) *
    ∏ i : G.Idx, ∏ i' : G.Idx, (if i = i' then 1 else Nat.dist (G.ρ i) (G.ρ i'))

lemma freezeQ_pos : 0 < G.freezeQ := by
  unfold freezeQ
  refine Nat.mul_pos (Finset.prod_pos fun p hp => (Nat.mem_primesBelow.1 hp).2.pos) ?_
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun i' _ => ?_
  split_ifs with h
  · exact Nat.one_pos
  · exact Nat.dist_pos_of_ne (fun h' => h (G.ρ_injective h'))

lemma prime_dvd_freezeQ_of_le {p : ℕ} (hp : p.Prime) (h : p ≤ 2 * Fintype.card G.Idx) :
    p ∣ G.freezeQ := by
  unfold freezeQ
  refine Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ ?_) _
  exact Nat.mem_primesBelow.2 ⟨by omega, hp⟩

lemma dist_dvd_freezeQ {i i' : G.Idx} (h : i ≠ i') : Nat.dist (G.ρ i) (G.ρ i') ∣ G.freezeQ := by
  unfold freezeQ
  refine Dvd.dvd.mul_left ?_ _
  have h1 : (∏ i' : G.Idx, (if i = i' then 1 else Nat.dist (G.ρ i) (G.ρ i'))) ∣
      ∏ i : G.Idx, ∏ i' : G.Idx, (if i = i' then 1 else Nat.dist (G.ρ i) (G.ρ i')) :=
    Finset.dvd_prod_of_mem (fun i => ∏ i' : G.Idx, (if i = i' then 1 else Nat.dist (G.ρ i) (G.ρ i')))
      (Finset.mem_univ i)
  refine dvd_trans ?_ h1
  have := Finset.dvd_prod_of_mem (fun i' => if i = i' then 1 else Nat.dist (G.ρ i) (G.ρ i'))
    (Finset.mem_univ i')
  simpa [if_neg h] using this

/-! ### The progression modulus -/

/-- `P₀ = Mprod · freezeQ`. -/
def P₀ : ℕ := G.Mprod * G.freezeQ

lemma P₀_pos : 0 < G.P₀ := Nat.mul_pos G.Mprod_pos G.freezeQ_pos

lemma b₀_lt_P₀ : G.b₀ < G.P₀ :=
  G.b₀_lt_Mprod.trans_le (Nat.le_mul_of_pos_right _ G.freezeQ_pos)

lemma Mprod_dvd_P₀ : G.Mprod ∣ G.P₀ := Dvd.intro _ rfl

lemma freezeQ_dvd_P₀ : G.freezeQ ∣ G.P₀ := Dvd.intro_left _ rfl

/-- **Every sample point freezes the multiplier residues**: `n = t_α + d_α k` with `d_α ∣ k`. -/
theorem exists_mult_mul {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    ∃ k, n = G.t α + G.d α * k ∧ G.d α ∣ k := by
  have hmod : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have hd2 : G.d α ^ 2 ∣ G.P₀ := (G.sq_d_dvd_Mprod α).trans G.Mprod_dvd_P₀
  have h1 : n ≡ G.b₀ [MOD G.d α ^ 2] :=
    (Nat.ModEq.of_dvd hd2 ((Nat.mod_modEq n G.P₀).symm.trans (by rw [hmod])))
  have h2 : n ≡ G.t α [MOD G.d α ^ 2] := h1.trans (G.b₀_modEq α)
  have ht : G.t α < G.d α ^ 2 := by
    have := G.t_lt_d α
    have := G.d_pos α
    nlinarith
  have hnm : n % G.d α ^ 2 = G.t α := by
    unfold Nat.ModEq at h2
    rw [h2, Nat.mod_eq_of_lt ht]
  refine ⟨G.d α * (n / G.d α ^ 2), ?_, Dvd.intro _ rfl⟩
  have := Nat.div_add_mod n (G.d α ^ 2)
  rw [hnm] at this
  rw [← mul_assoc, ← pow_two]
  omega

/-- A prime not dividing `P₀` exceeds `2T`. -/
theorem two_mul_card_le_of_not_dvd {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ G.P₀) :
    2 * Fintype.card G.Idx ≤ p := by
  by_contra hlt
  push Not at hlt
  exact h ((G.prime_dvd_freezeQ_of_le hp hlt.le).trans G.freezeQ_dvd_P₀)

/-- A prime not dividing `P₀` is good for the shifts. -/
theorem goodPrime_of_not_dvd_P₀ {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ G.P₀) : GoodPrime G.ρ p := by
  refine goodPrime_of_not_dvd G.ρ G.ρ_injective hp.pos fun i i' hii' hdvd => ?_
  refine h (((Int.natCast_dvd_natCast).1 ?_).trans (G.dist_dvd_freezeQ hii' |>.trans
    G.freezeQ_dvd_P₀))
  rw [Nat.dist]
  push_cast
  rcases le_total (G.ρ i) (G.ρ i') with hle | hle
  · rw [Nat.sub_eq_zero_of_le hle, Nat.cast_sub hle]
    push_cast
    have : ((G.ρ i' : ℤ) - G.ρ i) = -((G.ρ i : ℤ) - G.ρ i') := by ring
    rw [this, zero_add, dvd_neg]
    exact hdvd
  · rw [Nat.sub_eq_zero_of_le hle, Nat.cast_sub hle]
    push_cast
    rw [add_zero]
    exact hdvd

end GridParams

end NormalNumbers.G4
