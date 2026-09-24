import NormalNumbers.DelangeSlotPrincipal

/-!
# Rung 2, layer 4: the master dichotomy

Both halves of rung 2 are now proved:

* `Sgsum_tendsto_zero_of_psi_littleO` (+ `psiChar_littleO`, `psiAP_tendsto`) handles any
  `κ` whose sum over a period vanishes;
* `sigmaMeang_chiZero_tendsto_zero` handles the principal character.

This file merges them into **one** statement, `charSum_tendsto_zero`, covering every completely
multiplicative periodic `κ` supported on the units.  The dichotomy is elementary orthogonality:
if `κ b ≠ 1` for some unit `b`, then multiplying the period sum by `κ b` permutes the summands,
so the period sum is `0`; otherwise `κ` *is* `chiZero M` on the nose.

This is what makes the additive twist reachable without ever constructing the `m = s·t`
(`Q`-primary × `Q`-coprime) factorisation: every function that arises when the additive
character is unfolded — a Dirichlet character times principal characters mod various primes —
is again a completely multiplicative periodic function supported on units, i.e. an instance of
`charSum_tendsto_zero`.
-/

open Finset ArithmeticFunction Filter Topology

namespace NormalNumbers.DelangeSlot

/-- A completely multiplicative `M`-periodic function supported on the units mod `M`,
of modulus one there: exactly a Dirichlet character mod `M` viewed on `ℕ`. -/
structure IsCharLike (M : ℕ) (κ : ℕ → ℂ) : Prop where
  pos : 0 < M
  mul : ∀ a b : ℕ, κ (a * b) = κ a * κ b
  per : ∀ a b : ℕ, a % M = b % M → κ a = κ b
  zero : ∀ n : ℕ, ¬ Nat.Coprime n M → κ n = 0
  unit : ∀ n : ℕ, Nat.Coprime n M → ‖κ n‖ = 1

lemma IsCharLike.norm_le {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ) (n : ℕ) : ‖κ n‖ ≤ 1 := by
  by_cases hc : Nat.Coprime n M
  · exact le_of_eq (h.unit n hc)
  · simp [h.zero n hc]

/-- **Orthogonality.**  If `κ` is not identically `1` on the units, its sum over a period
vanishes. -/
theorem IsCharLike.sum_eq_zero {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ)
    {b : ℕ} (hb : Nat.Coprime b M) (hb1 : κ b ≠ 1) :
    ∑ a ∈ range M, κ a = 0 := by
  classical
  have hM : NeZero M := ⟨h.pos.ne'⟩
  have hbu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  obtain ⟨u, hu⟩ := hbu
  set key : ℕ → ℕ := fun a => (b * a) % M with hkey
  set inv : ℕ → ℕ := fun a => (((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (a : ZMod M)).val with hinv
  have hcast : ∀ a : ℕ, ((key a : ℕ) : ZMod M) = (b : ZMod M) * (a : ZMod M) := by
    intro a; simp [hkey, ZMod.natCast_mod]
  have hcastinv : ∀ a : ℕ, ((inv a : ℕ) : ZMod M)
      = ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (a : ZMod M) := by
    intro a; simp [hinv, ZMod.natCast_val, ZMod.cast_id]
  have hkey_mem : ∀ a ∈ range M, key a ∈ range M := fun a _ ↦
    mem_range.2 (Nat.mod_lt _ h.pos)
  have hinv_mem : ∀ a ∈ range M, inv a ∈ range M := fun a _ ↦
    mem_range.2 (ZMod.val_lt _)
  have hleft : ∀ a ∈ range M, inv (key a) = a := by
    intro a ha
    have ha' : a < M := mem_range.1 ha
    have : ((inv (key a) : ℕ) : ZMod M) = (a : ZMod M) := by
      rw [hcastinv, hcast, ← hu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
    have h2 := congrArg ZMod.val this
    rwa [ZMod.val_natCast_of_lt (mem_range.1 (hinv_mem _ (hkey_mem a ha))),
      ZMod.val_natCast_of_lt ha'] at h2
  have hright : ∀ a ∈ range M, key (inv a) = a := by
    intro a ha
    have ha' : a < M := mem_range.1 ha
    have : ((key (inv a) : ℕ) : ZMod M) = (a : ZMod M) := by
      rw [hcast, hcastinv, ← hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    have h2 := congrArg ZMod.val this
    rwa [ZMod.val_natCast_of_lt (mem_range.1 (hkey_mem _ (hinv_mem a ha))),
      ZMod.val_natCast_of_lt ha'] at h2
  have hswap : ∑ a ∈ range M, κ a = ∑ a ∈ range M, κ (key a) :=
    (Finset.sum_nbij' key inv hkey_mem hinv_mem hleft hright (fun _ _ ↦ rfl)).symm
  have hmulsum : ∑ a ∈ range M, κ (key a) = κ b * ∑ a ∈ range M, κ a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← h.mul]
    exact h.per (key a) (b * a) (by simp [hkey, Nat.mod_mod])
  have hS : ∑ a ∈ range M, κ a = κ b * ∑ a ∈ range M, κ a := hswap.trans hmulsum
  have hfac : (1 - κ b) * ∑ a ∈ range M, κ a = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.1 hfac with h' | h'
  · exact absurd (sub_eq_zero.1 h').symm hb1
  · exact h'

/-- **The master statement.**  For any character-like `κ` and any unimodular `z ≠ 1`, the mean
of `κ · z^{ω_{>P}}` tends to `0`. -/
theorem charSum_tendsto_zero {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ) :
    Tendsto (fun N : ℕ => Sgsum κ z P N / (N : ℂ)) atTop (𝓝 0) := by
  by_cases hprin : ∀ b : ℕ, Nat.Coprime b M → κ b = 1
  · -- `κ` is literally `chiZero M`
    have hκ : κ = chiZero M := by
      funext n
      by_cases hc : Nat.Coprime n M
      · rw [hprin n hc, chiZero, if_pos hc]
      · rw [h.zero n hc, chiZero, if_neg hc]
    have := sigmaMeang_chiZero_tendsto_zero hz hz1 P (Q := M) h.pos.ne'
    simpa [hκ, sigmaMeang] using this
  · push_neg at hprin
    obtain ⟨b, hb, hb1⟩ := hprin
    exact Sgsum_tendsto_zero_of_psi_littleO h.mul h.norm_le hz
      (psiChar_littleO h.pos κ h.per h.zero (h.sum_eq_zero hb hb1))

end NormalNumbers.DelangeSlot
