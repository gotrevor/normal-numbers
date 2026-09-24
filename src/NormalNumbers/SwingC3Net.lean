/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Lambert

/-!
# Nets on the circle: a perturbed grid meets every long enough arc

Leaf A of `SwingC3Rotation.lean` (`exists_rotationCover`) needs exactly this geometric fact.
The CRT steering of `SwingC3Split.exists_crt_pattern` produces rotation constants of the shape

`θ_k = C + k·b^{−ℓ'} + ρ_k`,  `0 ≤ ρ_k ≤ ε`,

— an exact grid of spacing `b^{−ℓ'}`, perturbed by the *uncontrolled* contribution of the window
slots beyond `ℓ'`.  `exists_perturbed_grid_mem_Ico` says such a family still meets every arc of
length `> b^{−ℓ'} + ε`, so it is a net, and that is all the covering argument needs.  This is
precisely why the route asks for a **net** and not for the exact grid that `LargeTailLaw`
demanded: the perturbation `ρ` is what killed the exact-grid version.
-/

open Finset

namespace NormalNumbers

/-- **An exact grid meets every arc longer than its spacing.**  The `m` points
`fract (c + k/m)`, `k < m`, form a coset of the `1/m`-grid on the circle, so any arc
`[α, α+len) ⊆ [0,1)` with `len > 1/m` contains one of them. -/
theorem exists_grid_mem_Ico {m : ℕ} (hm : 0 < m) (c α len : ℝ) (hα : 0 ≤ α)
    (hlen : 1 / (m : ℝ) < len) (hαlen : α + len ≤ 1) :
    ∃ k, k < m ∧ Int.fract (c + (k : ℝ) / m) ∈ Set.Ico α (α + len) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set s : ℝ := Int.fract (α - c) with hsdef
  have hs0 : 0 ≤ s := Int.fract_nonneg _
  have hs1 : s < 1 := Int.fract_lt_one _
  set k0 : ℤ := ⌈s * (m : ℝ)⌉ with hk0def
  have hlo : s * (m : ℝ) ≤ (k0 : ℝ) := Int.le_ceil _
  have hhi : (k0 : ℝ) < s * (m : ℝ) + 1 := Int.ceil_lt_add_one _
  have hk0nn : (0 : ℤ) ≤ k0 := Int.ceil_nonneg (by positivity)
  have hk0le : k0 ≤ (m : ℤ) := by
    rw [hk0def, Int.ceil_le]
    push_cast
    nlinarith
  set j : ℕ := k0.toNat with hjdef
  have hjcast : ((j : ℤ) : ℝ) = (k0 : ℝ) := by
    rw [hjdef, Int.toNat_of_nonneg hk0nn]
  have hjR : (j : ℝ) = (k0 : ℝ) := by exact_mod_cast hjcast
  have hjle : j ≤ m := by
    have : (k0 : ℤ) ≤ (m : ℤ) := hk0le
    omega
  set δ : ℝ := (j : ℝ) / m - s with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef, sub_nonneg, le_div_iff₀ hmR, hjR]
    linarith
  have hδhi : δ < 1 / (m : ℝ) := by
    rw [hδdef, sub_lt_iff_lt_add, div_lt_iff₀ hmR, hjR]
    have : (1 : ℝ) / (m : ℝ) * (m : ℝ) = 1 := by field_simp
    nlinarith
  -- the grid point at index `j` lands at `α + δ`
  have hfr : Int.fract (c + (j : ℝ) / m) = α + δ := by
    have hrw : c + (j : ℝ) / m = (α + δ) - ((⌊α - c⌋ : ℤ) : ℝ) := by
      rw [hδdef, hsdef, Int.fract]
      ring
    rw [hrw, Int.fract_sub_intCast, Int.fract_eq_self]
    constructor
    · linarith
    · linarith
  have hmem : (α + δ) ∈ Set.Ico α (α + len) := ⟨by linarith, by linarith⟩
  rcases lt_or_eq_of_le hjle with hjlt | hjeq
  · exact ⟨j, hjlt, by rw [hfr]; exact hmem⟩
  · refine ⟨0, hm, ?_⟩
    have hone : (j : ℝ) / m = 1 := by rw [hjeq]; field_simp
    have : c + ((0 : ℕ) : ℝ) / m = (c + (j : ℝ) / m) - ((1 : ℤ) : ℝ) := by
      rw [hone]; push_cast; ring
    rw [this, Int.fract_sub_intCast, hfr]
    exact hmem

/-- **A perturbed grid is still a net.**  Shifting each grid point forward by at most `ε`
costs exactly `ε` of arc length. -/
theorem exists_perturbed_grid_mem_Ico {m : ℕ} (hm : 0 < m) (c α len ε : ℝ) (ρ : ℕ → ℝ)
    (hρ0 : ∀ k, 0 ≤ ρ k) (hρ : ∀ k, ρ k ≤ ε) (hα : 0 ≤ α)
    (hlen : 1 / (m : ℝ) + ε < len) (hαlen : α + len ≤ 1) :
    ∃ k, k < m ∧ Int.fract (c + (k : ℝ) / m + ρ k) ∈ Set.Ico α (α + len) := by
  have hε : 0 ≤ ε := le_trans (hρ0 0) (hρ 0)
  obtain ⟨k, hk, hmem⟩ :=
    exists_grid_mem_Ico hm c α (len - ε) hα (by linarith) (by linarith)
  refine ⟨k, hk, ?_⟩
  obtain ⟨h1, h2⟩ := hmem
  have hsplit : c + (k : ℝ) / m + ρ k
      = (Int.fract (c + (k : ℝ) / m) + ρ k) + ((⌊c + (k : ℝ) / m⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; ring
  rw [hsplit, Int.fract_add_intCast, Int.fract_eq_self.2]
  · exact ⟨by linarith [hρ0 k], by linarith [hρ k]⟩
  · exact ⟨by linarith [hρ0 k], by linarith [hρ k]⟩

/-! ### The head/remainder split of `tailSmall`

The CRT steering controls `ω_{≤P}(a+j)` only for `j ≤ L`.  The rest of the window contributes
the perturbation `ρ` of `exists_perturbed_grid_mem_Ico`, and it is bounded by
`π(P)·b^{−L}/(b−1)` because `ω_{≤P} ≤ π(P)` pointwise. -/

/-- `π(P)`, the number of primes `≤ P`. -/
def piCount (P : ℕ) : ℕ := ((range (P + 1)).filter Nat.Prime).card

lemma omegaSmall_le_piCount (P m : ℕ) : omegaSmall P m ≤ piCount P := by
  classical
  unfold omegaSmall piCount
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_range] at hp ⊢
  exact ⟨by omega, hp.1.1⟩

/-- **The window head plus a small remainder.**  `tailSmall P b n` is its first `L` terms plus a
remainder in `[0, π(P)·b^{−L}/(b−1)]`. -/
theorem tailSmall_head_rem {b : ℕ} (hb : 2 ≤ b) (P n L : ℕ) :
    ∃ r : ℝ, tailSmall P b n
        = (∑ i ∈ range L, (omegaSmall P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) + r
      ∧ 0 ≤ r ∧ r ≤ (piCount P : ℝ) / ((b : ℝ) ^ L * ((b : ℝ) - 1)) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  set f : ℕ → ℝ := fun i => (omegaSmall P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) with hf
  have hsum : Summable f := summable_tailOf hb (omegaSmall_le_omegaR P) n
  have hsplit := hsum.sum_add_tsum_nat_add L
  refine ⟨∑' i : ℕ, f (i + L), ?_, ?_, ?_⟩
  · rw [tailSmall]
    exact hsplit.symm
  · exact tsum_nonneg fun i => by rw [hf]; positivity
  · -- majorise by the geometric series with constant `π(P)`
    set K : ℝ := (piCount P : ℝ) with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hmaj : Summable (fun i : ℕ => K / (b : ℝ) ^ (i + L + 1)) := by
      have : Summable (fun i : ℕ => K * ((1 / (b : ℝ)) ^ i * (1 / (b : ℝ)) ^ (L + 1))) :=
        ((summable_geometric_of_lt_one (by positivity)
          (by rw [div_lt_one hb0]; linarith)).mul_right _).mul_left K
      refine this.congr fun i => ?_
      rw [div_pow, div_pow, one_pow, one_pow]
      rw [show i + L + 1 = i + (L + 1) by ring, pow_add]
      field_simp
      ring
    have hle : ∑' i : ℕ, f (i + L) ≤ ∑' i : ℕ, K / (b : ℝ) ^ (i + L + 1) := by
      refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff L).2 hsum) hmaj
      simp only [hf]
      have h1 : (omegaSmall P (n + (i + L) + 1) : ℝ) ≤ K := by
        rw [hK]; exact_mod_cast omegaSmall_le_piCount P _
      have h2 : (0 : ℝ) < (b : ℝ) ^ (i + L + 1) := by positivity
      gcongr
    refine hle.trans (le_of_eq ?_)
    have hgeo : ∑' i : ℕ, ((1 : ℝ) / (b : ℝ)) ^ i = (b : ℝ) / ((b : ℝ) - 1) := by
      rw [tsum_geometric_of_lt_one (by positivity) (by rw [div_lt_one hb0]; linarith)]
      field_simp
    have hrw : ∀ i : ℕ, K / (b : ℝ) ^ (i + L + 1)
        = (K / (b : ℝ) ^ (L + 1)) * ((1 : ℝ) / (b : ℝ)) ^ i := by
      intro i
      rw [div_pow, one_pow, show i + L + 1 = i + (L + 1) by ring, pow_add]
      field_simp
    rw [tsum_congr hrw, tsum_mul_left, hgeo]
    field_simp
    ring

end NormalNumbers
