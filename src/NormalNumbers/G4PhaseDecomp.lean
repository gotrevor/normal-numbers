/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FourierControl

/-!
# G4 §4C: the phase decomposition of `q·S(n)` into local phases

With `w = Aᵀq`, `q·S(n) = ∑_{(α,j)} w_α 4^{−j} ω_s(n + ρ_{α,j})` where `ω_s(m) = #{p ∈ s : p ∣ m}`.
Abstractly: a finite family of roots `i : ι` with shifts `ρ_i` and coefficients `x_i`, and the
total phase `Φ(n) = ∑_i x_i ω_s(n+ρ_i)`.  This file proves

* `phase_eq_sum_local` — `Φ(n) = ∑_{p∈s} θ_p(n)`, `θ_p(n) = ∑_i x_i 1[p ∣ n+ρ_i]`;
  `ee_phase_eq_prod` — hence `ee(Φ n) = ∏_{p∈s} ee(θ_p n)`.
* `LocalPhase.ofShifts` — `θ_p` IS the `θ` of a `LocalPhase` (roots `= {b < p : ∃ i, p ∣ b+ρ_i}`,
  phase at `b` the sum of the `x_i` whose root is `b`), for `2·|ι| ≤ p`.
* `sum_sq_ofShifts_eq` — for a **good prime** (the roots `−ρ_i mod p` distinct), the summed
  squared distances of the local phases equal `∑_i dist(x_i,ℤ)²` — the quantity
  `G4FreqSep.sum_sq_distZ_freqDepth_ge` bounds below.
* **`norm_sampleAvg_ee_phase_le`** — `norm_sampleAvg_prod_ee_le` instantiated: the contraction
  runs over the good primes, every prime in `s` contributes to the error budget.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

@[simp] lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  simp only [ee]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma ee_sum {ι : Type*} (T : Finset ι) (x : ι → ℝ) : ee (∑ i ∈ T, x i) = ∏ i ∈ T, ee (x i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih => rw [Finset.sum_insert haT, Finset.prod_insert haT, ee_add, ih]

/-- `ω_s(m) = #{p ∈ s : p ∣ m}`. -/
def omegaOn (s : Finset ℕ) (m : ℕ) : ℕ := (s.filter (fun p => p ∣ m)).card

section Phase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total phase `Φ(n) = ∑_i x_i ω_s(n + ρ_i)`. -/
noncomputable def totalPhase (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, x i * omegaOn s (n + ρ i)

/-- The local phase at `p`: `θ_p(n) = ∑_i x_i 1[p ∣ n + ρ_i]`. -/
noncomputable def localPhase (p : ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, x i * (if p ∣ n + ρ i then 1 else 0)

lemma phase_eq_sum_local (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) :
    totalPhase s ρ x n = ∑ p ∈ s, localPhase p ρ x n := by
  unfold totalPhase localPhase omegaOn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole]

lemma ee_phase_eq_prod (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) :
    ee (totalPhase s ρ x n) = ∏ p ∈ s, ee (localPhase p ρ x n) := by
  rw [phase_eq_sum_local, ee_sum]

/-- The root of `i` modulo `p`: the residue `b` with `p ∣ b + ρ_i`. -/
def root (p : ℕ) (ρ : ι → ℕ) (i : ι) : ℕ := (p - ρ i % p) % p

lemma dvd_add_iff_mod_eq_root {p : ℕ} (hp : 0 < p) (ρ : ι → ℕ) (i : ι) (n : ℕ) :
    p ∣ n + ρ i ↔ n % p = root p ρ i := by
  unfold root
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  generalize ha : n % p = a
  generalize hb : ρ i % p = b
  have ha' : a < p := ha ▸ Nat.mod_lt _ hp
  have hb' : b < p := hb ▸ Nat.mod_lt _ hp
  rcases Nat.eq_zero_or_pos b with h0 | h0
  · subst h0; simp [Nat.mod_eq_of_lt ha']
  · rw [Nat.mod_eq_of_lt (by omega : p - b < p)]
    constructor
    · intro h
      rcases Nat.lt_or_ge (a + b) p with hl | hg
      · rw [Nat.mod_eq_of_lt hl] at h; omega
      · rw [Nat.mod_eq_sub_mod hg, Nat.mod_eq_of_lt (by omega)] at h; omega
    · intro h; subst h; rw [Nat.sub_add_cancel hb'.le, Nat.mod_self]

/-! ### The induced local data -/

/-- The trivial local data (no active roots). -/
def LocalPhase.trivial (p : ℕ) : LocalPhase p :=
  ⟨∅, by simp, fun _ => 0, by simp⟩

/-- The local data at `p` induced by shifts `ρ` and coefficients `x`: the roots are the residues
`−ρ_i mod p`, and the phase at a root is the sum of the coefficients landing there. -/
noncomputable def LocalPhase.ofShifts (p : ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (hp : 0 < p)
    (hk : 2 * Fintype.card ι ≤ p) : LocalPhase p where
  roots := Finset.univ.image (root p ρ)
  hroots := by
    intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hb
    exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  x := fun b => ∑ i ∈ Finset.univ.filter (fun i => root p ρ i = b), x i
  hk := by
    calc 2 * (Finset.univ.image (root p ρ)).card ≤ 2 * Fintype.card ι := by
          have := Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := root p ρ)
          rw [Finset.card_univ] at this
          omega
      _ ≤ p := hk

/-- The local data at every `p`, trivial where the good-prime condition fails. -/
noncomputable def shiftPhase (ρ : ι → ℕ) (x : ι → ℝ) (p : ℕ) : LocalPhase p :=
  if h : 0 < p ∧ 2 * Fintype.card ι ≤ p then LocalPhase.ofShifts p ρ x h.1 h.2
  else LocalPhase.trivial p

lemma shiftPhase_eq {ρ : ι → ℕ} {x : ι → ℝ} {p : ℕ} (hp : 0 < p) (hk : 2 * Fintype.card ι ≤ p) :
    shiftPhase ρ x p = LocalPhase.ofShifts p ρ x hp hk := by
  unfold shiftPhase; rw [dif_pos ⟨hp, hk⟩]

/-- `θ` of the induced data is the local phase. -/
lemma theta_ofShifts {p : ℕ} (ρ : ι → ℕ) (x : ι → ℝ) (hp : 0 < p) (hk : 2 * Fintype.card ι ≤ p)
    (n : ℕ) : (LocalPhase.ofShifts p ρ x hp hk).θ n = localPhase p ρ x n := by
  unfold LocalPhase.θ localPhase LocalPhase.ofShifts
  simp only
  by_cases h : n % p ∈ Finset.univ.image (root p ρ)
  · rw [if_pos h, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hd : (p ∣ n + ρ i) ↔ (root p ρ i = n % p) := by
      rw [dvd_add_iff_mod_eq_root hp]; exact eq_comm
    simp only [hd]
    split_ifs <;> simp
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ p ∣ n + ρ i := fun hd =>
      h (Finset.mem_image.2 ⟨i, Finset.mem_univ _, ((dvd_add_iff_mod_eq_root hp ρ i n).1 hd).symm⟩)
    rw [if_neg this, mul_zero]

/-- **Good primes see every coefficient separately.**  When the roots are distinct mod `p`, the
summed squared distances of the local phases equal `∑_i dist(x_i, ℤ)²`. -/
lemma sum_sq_ofShifts_eq {p : ℕ} (ρ : ι → ℕ) (x : ι → ℝ) (hp : 0 < p)
    (hk : 2 * Fintype.card ι ≤ p) (hinj : Function.Injective (root p ρ)) :
    ∑ b ∈ (LocalPhase.ofShifts p ρ x hp hk).roots,
        distZ ((LocalPhase.ofShifts p ρ x hp hk).x b) ^ 2
      = ∑ i, distZ (x i) ^ 2 := by
  unfold LocalPhase.ofShifts
  simp only
  rw [Finset.sum_image (fun i _ j _ h => hinj h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Finset.univ.filter (fun j => root p ρ j = root p ρ i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hinj.eq_iff
  rw [this, Finset.sum_singleton]

/-- The good-prime predicate: the roots `−ρ_i mod p` are pairwise distinct. -/
def GoodPrime (ρ : ι → ℕ) (p : ℕ) : Prop := Function.Injective (root p ρ)

open Classical in
/-- **§4C for phase sums of shifted `ω`.**  The contraction runs over the good primes of `s`
(with the uniform lower bound `θ₀ ≤ ∑_i dist(x_i,ℤ)²`); every prime of `s` enters the four
error terms. -/
theorem norm_sampleAvg_ee_phase_le (X P₀ a : ℕ) (hP₀ : 0 < P₀)
    (ha : a < P₀) (hne : (apSample X P₀ a).Nonempty)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hsP : ∀ p ∈ s, p.Coprime P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ s, p ≤ R)
    (ρ : ι → ℕ) (x : ι → ℝ) (hk : ∀ p ∈ s, 2 * Fintype.card ι ≤ p)
    {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀) (hθ : θ₀ ≤ ∑ i, distZ (x i) ^ 2)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    ‖sampleAvg (apSample X P₀ a) id (fun n => ee (totalPhase s ρ x n))‖
      ≤ Real.exp (-∑ p ∈ s, 4 * (if GoodPrime ρ p then θ₀ else 0) / p)
        + ((s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card
            * (2 ^ M * (2 * (R : ℝ) ^ M / (apSample X P₀ a).card))
          + (∏ p ∈ s, (1 + lam' * (2 * (shiftPhase ρ x p).roots.card / p))) / lam' ^ M
          + 2 * (2 * Real.exp 1 / lam) ^ M
              * ∏ p ∈ s, (1 + Real.exp lam * ((shiftPhase ρ x p).roots.card / p))
          + 2 * (2 * Real.exp 1 / M) ^ M * (s.card : ℝ) ^ M
              * (2 * (R : ℝ) ^ M / (apSample X P₀ a).card)) := by
  have hpos : ∀ p ∈ s, 0 < p := fun p hp => (hs p hp).pos
  have hfun : (fun n => ee (totalPhase s ρ x n))
      = fun n => ∏ p ∈ s, ee ((shiftPhase ρ x p).θ n) := by
    funext n
    rw [ee_phase_eq_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [shiftPhase_eq (hpos p hp) (hk p hp), theta_ofShifts]
  rw [hfun]
  refine norm_sampleAvg_prod_ee_le X P₀ a hP₀ ha hne s hs hsP hR1 hR (shiftPhase ρ x)
    (fun p => if GoodPrime ρ p then θ₀ else 0) (fun p _ => by split_ifs <;> simp [hθ0])
    (fun p hp => ?_) hM hlam' hlam
  rw [shiftPhase_eq (hpos p hp) (hk p hp)]
  split_ifs with hg
  · rw [sum_sq_ofShifts_eq ρ x (hpos p hp) (hk p hp) hg]; exact hθ
  · exact Finset.sum_nonneg fun b _ => by positivity

end Phase

end NormalNumbers.G4
