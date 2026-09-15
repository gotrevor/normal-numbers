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
  sorry

/-- The brief's numbers: `d = 5, t = 1, c = 2, q = 3, n = 86` — physical `17`, re-centred `15`. -/
theorem recentring_anchor : physIdx 5 1 86 = 17 ∧ (86 - (1 + 5 * 2)) / 5 = 15 := by
  decide

/-! ### CRT pins the sample to one class mod `D` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pairwise-coprime moduli: congruence at each of them is congruence mod the product. -/
theorem modEq_prod_of_forall {d : ι → ℕ} (hcop : ∀ α β, α ≠ β → Nat.Coprime (d α) (d β))
    {n n' : ℕ} (h : ∀ α, n ≡ n' [MOD d α]) : n ≡ n' [MOD ∏ α, d α] := by
  sorry

/-- `physIdx d t n = n / d` when `n mod d = t`. -/
lemma physIdx_eq_div {d t n : ℕ} (hn : n % d = t) : physIdx d t n = n / d := by
  sorry

/-- **The pinned index.**  If `n = a + D·q` with `d ∣ D` and `t ≤ a`, then
`(n − t)/d = (a − t)/d + (D/d)·q`. -/
theorem physIdx_of_pinned {d t a D q : ℕ} (hd : 0 < d) (hdD : d ∣ D) (hta : t ≤ a) :
    physIdx d t (a + D * q) = physIdx d t a + (D / d) * q := by
  sorry

/-- **Index confinement.**  Two sample points with the same offsets at every atom have physical
indices congruent mod `D/d_α`. -/
theorem physIdx_modEq {d t : ι → ℕ} (hd : ∀ α, 0 < d α)
    (hcop : ∀ α β, α ≠ β → Nat.Coprime (d α) (d β)) {n n' : ℕ}
    (hn : ∀ α, n % d α = t α) (hn' : ∀ α, n' % d α = t α) (α : ι) :
    physIdx (d α) (t α) n ≡ physIdx (d α) (t α) n' [MOD (∏ β, d β) / d α] := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The coefficient is tiny whenever every multiplier is `≥ dm`: `Σ_α d_α / D ≤ |ι| / dm^(|ι|−1)`,
because `D/d_α = ∏_{β ≠ α} d_β ≥ dm^(|ι|−1)`. -/
theorem sum_div_prod_le {d : ι → ℕ} {dm : ℕ} (hdm : 0 < dm) (hd : ∀ α, dm ≤ d α) :
    (∑ α, (d α : ℝ)) / ∏ α, (d α : ℝ) ≤ Fintype.card ι / (dm : ℝ) ^ (Fintype.card ι - 1) := by
  sorry

end NormalNumbers.G4Confine

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.G4Confine Finset

/-- On the schedule's sample every point has `n mod d_α = t_α` (no frozen-residue input used:
only `d_α ∣ d_α² ∣ P₀` and `b₀ ≡ t_α (mod d_α²)`). -/
lemma mod_d_eq_t_of_mem {G : GridParams} {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (α : G.Atom) : n % G.d α = G.t α := by
  sorry

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
  sorry

/-- **The numbers.**  The density coefficient at scale `i` is at most
`kk · (K²+1)^K / (2 · dmin^((K²+1)^K − 1))`. -/
theorem density_coeff_le (i : ℕ) :
    (kk i : ℝ) * (∑ α, ((gridAt i).d α : ℝ)) / (2 * ∏ α, ((gridAt i).d α : ℝ)) ≤
      (kk i : ℝ) * ((KK i ^ 2 + 1) ^ KK i : ℕ) / (2 * (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i - 1)) := by
  sorry

end NormalNumbers.G4.Sched
