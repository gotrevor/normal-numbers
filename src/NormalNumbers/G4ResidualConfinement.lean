/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyResidueProbe
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# After the extraction, L1: **residual CRT confinement, correctly indexed**

`G4EntropyResidueProbe.not_dense_of_any_residue` is a valid theorem about the sampler it
defines, whose window index is the **re-centred** `kIdxOf G b n α = (n − b mod d_α²)/d_α`.
That is *not* the physical orbit index `(n − t_α)/d_α` once the multiplier residue varies: for
`0 ≤ t < d`, `0 ≤ c < d` and `n = t + d·c + d²·q` the physical index is `c + d·q` while the
re-centred one is `d·q` (`recentring`; `d = 5, t = 1, c = 2, q = 3, n = 86` gives `17` vs `15`,
`recentring_anchor`).  So that theorem is not a universal impossibility statement about every
way of varying the CRT phases.

This module proves the brief's lemma **with the physical index**, and with *no* frozen-residue
hypothesis at all: pairwise-coprime multipliers `d_α`, offsets `t_α < d_α`, `D = ∏ d_α`, and a
sample set `P` whose every point satisfies the exact identities `n ≡ t_α (mod d_α)` for every
atom.  Then

* `modEq_prod_of_forall` — CRT pins any two sample points to the same class mod `D`;
* `physIdx_of_pinned` — for `n = a + D·q`, `k_α = (a − t_α)/d_α + (D/d_α)·q`;
* `physIdx_modEq` — hence `k_α` lives in one class mod `D/d_α`;
* `card_filter_le_of_confined` — the positions `2k_α + h`, `h < m`, read below `L` number at
  most `Σ_α (L/(2(D/d_α)) + 1)·m`;
* `density_bound` — in real terms, `≤ L · m (Σ_α d_α)/(2D) + |ι|·m`, i.e. upper density
  `≤ m (Σ_α d_α)/(2D)`.

It is a fixed-grid coverage bound, not a statement about all grids or about the union across
scales.  The schedule specialization is at the end of the file (`Sched.confinement_at_scale`,
`Sched.density_coeff_le`): with `|ι| = (K²+1)^K` atoms each `≥ dmin`, the coefficient
`m (Σ_α d_α)/(2D)` is at most `m·|ι| / (2·dmin^(|ι|−1))`.  At `i = 0`: `K = 160000`,
`|ι| = (2.56·10¹⁰ + 1)^160000 > 10^1665000`, `dmin > 10^6` — the coefficient is below
`10^(−10^1665000)`; this is what "small" means here.
-/

open Finset

namespace NormalNumbers.G4Confine

/-! ### The physical index and the scalar re-centring identity -/

/-- The physical orbit index of `n` at an atom with multiplier `d` and offset `t`:
`(n − t)/d`.  On the schedule this is `kIdx`. -/
def physIdx (d t n : ℕ) : ℕ := (n - t) / d

/-- **The re-centring identity.**  For `n = t + d·c + d²·q` the physical index is `c + d·q`;
subtracting the residue `t + d·c` (as `kIdxOf` does with `b mod d²`) gives `d·q` instead. -/
theorem recentring (d t c q : ℕ) (hd : 0 < d) :
    physIdx d t (t + d * c + d ^ 2 * q) = c + d * q ∧
      (t + d * c + d ^ 2 * q - (t + d * c)) / d = d * q := by
  constructor
  · unfold physIdx
    have : t + d * c + d ^ 2 * q - t = d * (c + d * q) := by ring_nf; omega
    rw [this, Nat.mul_div_cancel_left _ hd]
  · have : t + d * c + d ^ 2 * q - (t + d * c) = d * (d * q) := by ring_nf; omega
    rw [this, Nat.mul_div_cancel_left _ hd]

/-- The brief's numbers: `d = 5, t = 1, c = 2, q = 3, n = 86` — physical `17`, re-centred `15`. -/
theorem recentring_anchor : physIdx 5 1 86 = 17 ∧ (86 - (1 + 5 * 2)) / 5 = 15 := by
  decide

/-! ### CRT pins the sample to one class mod `D` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pairwise-coprime moduli: congruence at each of them is congruence mod the product. -/
theorem modEq_prod_of_forall {d : ι → ℕ} (hcop : ∀ α β, α ≠ β → Nat.Coprime (d α) (d β))
    {n n' : ℕ} (h : ∀ α, n ≡ n' [MOD d α]) : n ≡ n' [MOD ∏ α, d α] := by
  rw [Nat.modEq_iff_dvd, Nat.cast_prod]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro α _ β _ hab
    exact Nat.isCoprime_iff_coprime.2 (hcop α β hab)
  · intro α _
    exact (Nat.modEq_iff_dvd).1 (h α)

/-- `physIdx d t n = n / d` when `n mod d = t`. -/
lemma physIdx_eq_div {d t n : ℕ} (hn : n % d = t) : physIdx d t n = n / d := by
  unfold physIdx
  rw [← hn, ← Nat.div_eq_sub_mod_div]

/-- **The pinned index.**  If `n = a + D·q` with `d ∣ D` and `t ≤ a`, then
`(n − t)/d = (a − t)/d + (D/d)·q`. -/
theorem physIdx_of_pinned {d t a D q : ℕ} (hd : 0 < d) (hdD : d ∣ D) (hta : t ≤ a) :
    physIdx d t (a + D * q) = physIdx d t a + (D / d) * q := by
  unfold physIdx
  obtain ⟨M, rfl⟩ := hdD
  rw [Nat.mul_div_cancel_left _ hd]
  have : a + d * M * q - t = (a - t) + d * (M * q) := by
    rw [mul_assoc]; omega
  rw [this, Nat.add_mul_div_left _ _ hd]

/-- **Index confinement.**  Two sample points with the same offsets at every atom have physical
indices congruent mod `D/d_α`. -/
theorem physIdx_modEq {d t : ι → ℕ} (hd : ∀ α, 0 < d α)
    (hcop : ∀ α β, α ≠ β → Nat.Coprime (d α) (d β)) {n n' : ℕ}
    (hn : ∀ α, n % d α = t α) (hn' : ∀ α, n' % d α = t α) (α : ι) :
    physIdx (d α) (t α) n ≡ physIdx (d α) (t α) n' [MOD (∏ β, d β) / d α] := by
  have hD : n ≡ n' [MOD ∏ β, d β] := by
    refine modEq_prod_of_forall hcop fun β => ?_
    show n % d β = n' % d β
    rw [hn β, hn' β]
  have hdvd : d α ∣ ∏ β, d β := Finset.dvd_prod_of_mem _ (Finset.mem_univ α)
  rw [physIdx_eq_div (hn α), physIdx_eq_div (hn' α)]
  refine Nat.ModEq.mul_left_cancel' (hd α).ne' ?_
  rw [Nat.mul_div_cancel' hdvd]
  have h1 : d α * (n / d α) + t α = n := by
    conv_rhs => rw [← Nat.div_add_mod n (d α)]
    rw [hn α]
  have h2 : d α * (n' / d α) + t α = n' := by
    conv_rhs => rw [← Nat.div_add_mod n' (d α)]
    rw [hn' α]
  refine Nat.ModEq.add_right_cancel' (t α) ?_
  rw [h1, h2]
  exact hD

/-! ### One residue class of indices reads a sparse column -/

/-- `{2(k₀ mod M + M·c) + h : c ≤ L/(2M), h < m}`: the windows at indices `≡ k₀ (mod M)`. -/
def resCol (M k₀ m L : ℕ) : Finset ℕ :=
  ((Finset.range (L / (2 * M) + 1)) ×ˢ Finset.range m).image
    (fun z => 2 * (k₀ % M + M * z.1) + z.2)

lemma card_resCol_le (M k₀ m L : ℕ) : (resCol M k₀ m L).card ≤ (L / (2 * M) + 1) * m := by
  refine le_trans Finset.card_image_le ?_
  simp [resCol, Finset.card_product]

lemma mem_resCol {M k₀ m L k h : ℕ} (hM : 0 < M) (hk : k ≡ k₀ [MOD M]) (hh : h < m)
    (hL : 2 * k + h < L) : 2 * k + h ∈ resCol M k₀ m L := by
  have hk' : k = k₀ % M + M * (k / M) := by
    have := Nat.mod_add_div k M
    rw [show k % M = k₀ % M from hk] at this
    omega
  refine Finset.mem_image.2 ⟨(k / M, h), ?_, ?_⟩
  · refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 hh⟩
    have hc : (k / M) * (2 * M) ≤ L := by
      have := Nat.mul_div_le k M
      nlinarith
    have := (Nat.le_div_iff_mul_le (show 0 < 2 * M by omega)).2 hc
    omega
  · simp only
    rw [← hk']

/-! ### The union bound -/

/-- **Residual CRT confinement (finite prefix).**  With pairwise-coprime `d_α`, a sample `P`
whose points all satisfy `n ≡ t_α (mod d_α)`, and a predicate `U` on `[0, L)` covered by the
windows `[2k_α(n), 2k_α(n) + m)`, the count of `U` below `L` is at most
`Σ_α (L/(2(D/d_α)) + 1)·m`. -/
theorem card_filter_le_of_confined {d t : ι → ℕ} (hd : ∀ α, 0 < d α)
    (hcop : ∀ α β, α ≠ β → Nat.Coprime (d α) (d β)) (P : Finset ℕ)
    (hP : ∀ n ∈ P, ∀ α, n % d α = t α) (U : ℕ → Prop) [DecidablePred U] {m L : ℕ}
    (hcov : ∀ j, j < L → U j →
      ∃ n ∈ P, ∃ α, ∃ h < m, j = 2 * physIdx (d α) (t α) n + h) :
    ((Finset.range L).filter U).card ≤ ∑ α, (L / (2 * ((∏ β, d β) / d α)) + 1) * m := by
  classical
  rcases P.eq_empty_or_nonempty with hPe | ⟨n₀, hn₀⟩
  · have : (Finset.range L).filter U = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun j hj hU => ?_
      obtain ⟨n, hn, -⟩ := hcov j (Finset.mem_range.1 hj) hU
      simp [hPe] at hn
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  set D := ∏ β, d β with hDdef
  have hDpos : 0 < D := Finset.prod_pos fun β _ => hd β
  have hMpos : ∀ α, 0 < D / d α := fun α =>
    Nat.div_pos (Nat.le_of_dvd hDpos (Finset.dvd_prod_of_mem _ (Finset.mem_univ α))) (hd α)
  have hsub : (Finset.range L).filter U ⊆
      Finset.univ.biUnion (fun α => resCol (D / d α) (physIdx (d α) (t α) n₀) m L) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨n, hn, α, h, hh, rfl⟩ := hcov j hj.1 hj.2
    refine Finset.mem_biUnion.2 ⟨α, Finset.mem_univ α, ?_⟩
    exact mem_resCol (hMpos α) (physIdx_modEq hd hcop (hP n hn) (hP n₀ hn₀) α) hh hj.1
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun α _ => card_resCol_le _ _ _ _

/-- **Residual CRT confinement (density form).**  The count below `L` is at most
`L · m (Σ_α d_α)/(2D) + |ι|·m`; dividing by `L`, the upper density of the read set is at most
`m (Σ_α d_α)/(2D)`. -/
theorem density_bound {d t : ι → ℕ} (hd : ∀ α, 0 < d α)
    (hcop : ∀ α β, α ≠ β → Nat.Coprime (d α) (d β)) (P : Finset ℕ)
    (hP : ∀ n ∈ P, ∀ α, n % d α = t α) (U : ℕ → Prop) [DecidablePred U] {m L : ℕ}
    (hcov : ∀ j, j < L → U j →
      ∃ n ∈ P, ∃ α, ∃ h < m, j = 2 * physIdx (d α) (t α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) * ((m : ℝ) * ∑ α, (d α : ℝ)) / (2 * ∏ α, (d α : ℝ)) + Fintype.card ι * m := by
  classical
  have hnat := card_filter_le_of_confined hd hcop P hP U hcov (m := m) (L := L)
  set D := ∏ β, d β with hDdef
  have hDpos : 0 < D := Finset.prod_pos fun β _ => hd β
  have hDR : (D : ℝ) = ∏ α, (d α : ℝ) := by rw [hDdef, Nat.cast_prod]
  have hDRpos : (0 : ℝ) < D := by exact_mod_cast hDpos
  -- per-atom real bound
  have hα : ∀ α, (((L / (2 * (D / d α)) + 1) * m : ℕ) : ℝ) ≤
      (L : ℝ) * (d α : ℝ) / (2 * D) * m + m := by
    intro α
    have hdvd : d α ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ α)
    have hdpos : (0 : ℝ) < d α := by exact_mod_cast hd α
    have h1 : ((L / (2 * (D / d α)) : ℕ) : ℝ) ≤ (L : ℝ) / (2 * ((D / d α : ℕ) : ℝ)) := by
      have := (Nat.cast_div_le (α := ℝ) (m := L) (n := 2 * (D / d α)))
      rwa [Nat.cast_mul, Nat.cast_ofNat] at this
    have h2 : ((D / d α : ℕ) : ℝ) = (D : ℝ) / d α := Nat.cast_div hdvd hdpos.ne'
    have h3 : (L : ℝ) / (2 * ((D : ℝ) / d α)) = (L : ℝ) * (d α : ℝ) / (2 * D) := by
      field_simp
    rw [h2, h3] at h1
    push_cast
    have := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) m)
    linarith
  have hsum : (∑ α, (((L / (2 * (D / d α)) + 1) * m : ℕ) : ℝ)) ≤
      ∑ α, ((L : ℝ) * (d α : ℝ) / (2 * D) * m + m) := Finset.sum_le_sum fun α _ => hα α
  have hcast : (((Finset.range L).filter U).card : ℝ) ≤
      ∑ α, (((L / (2 * (D / d α)) + 1) * m : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast hnat
  have hrhs : ∑ α, ((L : ℝ) * (d α : ℝ) / (2 * D) * m + m) =
      (L : ℝ) * ((m : ℝ) * ∑ α, (d α : ℝ)) / (2 * ∏ α, (d α : ℝ)) + Fintype.card ι * m := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hDR]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun α _ => by ring
  linarith

/-- The coefficient is tiny whenever every multiplier is `≥ dm`: `Σ_α d_α / D ≤ |ι| / dm^(|ι|−1)`,
because `D/d_α = ∏_{β ≠ α} d_β ≥ dm^(|ι|−1)`. -/
theorem sum_div_prod_le {d : ι → ℕ} {dm : ℕ} (hdm : 0 < dm) (hd : ∀ α, dm ≤ d α) :
    (∑ α, (d α : ℝ)) / ∏ α, (d α : ℝ) ≤ Fintype.card ι / (dm : ℝ) ^ (Fintype.card ι - 1) := by
  classical
  have hdpos : ∀ α, (0 : ℝ) < d α := fun α => by
    have := hd α; exact_mod_cast (lt_of_lt_of_le hdm this)
  have hDpos : (0 : ℝ) < ∏ α, (d α : ℝ) := Finset.prod_pos fun α _ => hdpos α
  have hdmR : (0 : ℝ) < dm := by exact_mod_cast hdm
  -- each term `d α / D = 1 / ∏_{β ≠ α} d β ≤ 1 / dm^(card − 1)`
  have hterm : ∀ α, (d α : ℝ) / ∏ β, (d β : ℝ) ≤ 1 / (dm : ℝ) ^ (Fintype.card ι - 1) := by
    intro α
    have hsplit : ∏ β, (d β : ℝ) = (d α : ℝ) * ∏ β ∈ Finset.univ.erase α, (d β : ℝ) :=
      (Finset.mul_prod_erase Finset.univ (fun β => (d β : ℝ)) (Finset.mem_univ α)).symm
    have hrest : (dm : ℝ) ^ (Fintype.card ι - 1) ≤ ∏ β ∈ Finset.univ.erase α, (d β : ℝ) := by
      have := Finset.pow_card_le_prod (Finset.univ.erase α) d dm (fun β _ => hd β)
      rw [Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ] at this
      exact_mod_cast this
    have hrestpos : (0 : ℝ) < ∏ β ∈ Finset.univ.erase α, (d β : ℝ) :=
      Finset.prod_pos fun β _ => hdpos β
    rw [hsplit, div_mul_cancel_left₀ (hdpos α).ne', inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hrest
  calc (∑ α, (d α : ℝ)) / ∏ α, (d α : ℝ) = ∑ α, (d α : ℝ) / ∏ β, (d β : ℝ) := by
        rw [Finset.sum_div]
    _ ≤ ∑ _α : ι, (1 : ℝ) / (dm : ℝ) ^ (Fintype.card ι - 1) := Finset.sum_le_sum fun α _ => hterm α
    _ = Fintype.card ι / (dm : ℝ) ^ (Fintype.card ι - 1) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]

end NormalNumbers.G4Confine

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.G4Confine Finset

/-- On the schedule's sample every point has `n mod d_α = t_α` (no frozen-residue input used:
only `d_α ∣ d_α² ∣ P₀` and `b₀ ≡ t_α (mod d_α²)`). -/
lemma mod_d_eq_t_of_mem {G : GridParams} {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (α : G.Atom) : n % G.d α = G.t α := by
  obtain ⟨k, hk, -⟩ := G.exists_mult_mul hn α
  rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (G.t_lt_d α)]

/-- `kIdx` is the physical index. -/
lemma kIdx_eq_physIdx (G : GridParams) (n : ℕ) (α : G.Atom) :
    kIdx G n α = physIdx (G.d α) (G.t α) n := rfl

/-- **The schedule specialization.**  At scale `i`, any predicate `U` covered by the positions
the sample reads has count below `L` at most `L · kk (Σ_α d_α)/(2 ∏_α d_α) + (K²+1)^K · kk`. -/
theorem confinement_at_scale (i : ℕ) (U : ℕ → Prop) [DecidablePred U] {L : ℕ}
    (hcov : ∀ j, j < L → U j → j ∈ sampledPosAt i) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) * ((kk i : ℝ) * ∑ α, ((gridAt i).d α : ℝ)) / (2 * ∏ α, ((gridAt i).d α : ℝ))
        + ((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i := by
  classical
  have h := density_bound (ι := (gridAt i).Atom) (d := (gridAt i).d) (t := (gridAt i).t)
    (gridAt i).d_pos (fun α β hab => (gridAt i).coprime_d hab)
    (apSample (X (KK i)) (gridAt i).P₀ (gridAt i).b₀)
    (fun n hn α => mod_d_eq_t_of_mem hn α) U (m := kk i) (L := L) (by
      intro j hj hU
      obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (gridAt i)).1 (hcov j hj hU)
      exact ⟨n, hn, α, h, hh, rfl⟩)
  rwa [card_Atom_gridAt] at h

/-- **The numbers.**  The density coefficient at scale `i` is at most
`kk · (K²+1)^K / (2 · dmin^((K²+1)^K − 1))`. -/
theorem density_coeff_le (i : ℕ) :
    (kk i : ℝ) * (∑ α, ((gridAt i).d α : ℝ)) / (2 * ∏ α, ((gridAt i).d α : ℝ)) ≤
      (kk i : ℝ) * ((KK i ^ 2 + 1) ^ KK i : ℕ) / (2 * (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i - 1)) := by
  classical
  have h := sum_div_prod_le (ι := (gridAt i).Atom) (d := (gridAt i).d) (dmin_pos i) (dmin_le_d i)
  rw [card_Atom_gridAt] at h
  have hDpos : (0 : ℝ) < ∏ α, ((gridAt i).d α : ℝ) :=
    Finset.prod_pos fun α _ => by exact_mod_cast (gridAt i).d_pos α
  have hk : (0 : ℝ) ≤ kk i := Nat.cast_nonneg _
  have hpow : (0 : ℝ) < (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i - 1) := by
    have : (0 : ℝ) < dmin i := by exact_mod_cast dmin_pos i
    positivity
  calc (kk i : ℝ) * (∑ α, ((gridAt i).d α : ℝ)) / (2 * ∏ α, ((gridAt i).d α : ℝ))
      = ((kk i : ℝ) / 2) * ((∑ α, ((gridAt i).d α : ℝ)) / ∏ α, ((gridAt i).d α : ℝ)) := by
        ring
    _ ≤ ((kk i : ℝ) / 2) * (((KK i ^ 2 + 1) ^ KK i : ℕ) /
          (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i - 1)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (kk i : ℝ) * ((KK i ^ 2 + 1) ^ KK i : ℕ) /
          (2 * (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i - 1)) := by ring

end NormalNumbers.G4.Sched
