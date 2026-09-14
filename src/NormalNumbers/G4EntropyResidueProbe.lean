/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyFamily

/-!
# Entropy expedition, objective B: **the residue probe**

The arithmetic sample `apSample X G.P₀ G.b₀` fixes **one** class mod `P₀`.  Objective B asks
whether the union over *all* classes — every `b` with its own frozen multiplier residues
`c_α = b mod d_α²` — reads a set of digit positions of density one, which is what
`G4EntropyBarrier`/`qForces_normal_iff_density_one` would need to force normality of `G₄`
itself.

`G4EntropyFamily.not_dense_of_scale` already closes the *grid* direction: no family of
admissible `GridParams` at a fixed scale reads half of any prefix.  But every grid there samples
its **own** `b₀`, so it does not cover B's question, which moves the class while keeping the
grid.  This module closes that remaining direction.

The point is that the confinement is a property of the **multipliers**, not of the class:

* `dvd_kIdxOf` — for *every* `b` and every `n ≡ b (mod P₀)`, the class-relative window index
  `kIdxOf G b n α = (n − b mod d_α²)/d_α` is divisible by `d_α`.  The proof is the same two
  lines as `GridParams.exists_mult_mul`, with `b mod d_α²` in place of `t_α`: `d_α² ∣ P₀`, so
  `n mod d_α² = b mod d_α²` whatever `b` is.  Nothing about `b₀`'s CRT construction is used.
* `card_filter_le_of_classes` — hence the union over an arbitrary finset `B` of classes reads
  at most `|D|·(L/(2 dm) + 1)·m` positions below `L`, with no `|B|` in it.
* `not_dense_of_any_residue` — at the implemented schedule that is below `L/2`.

**Verdict B: NO** — not because some estimate in the E0 cone fails off `b₀` (the audit in the
handoff finds them all class-uniform), but because the *payoff* is unavailable: the union over
every residue class still misses more than half of every prefix, so it can never read density
one.  The surviving arithmetic gap is named there: it is not an estimate, it is `d_α ∣ kIdx`.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4

/-! ### The class-relative window index -/

/-- The window index of the class-`b` sample at atom `α`: `(n − b mod d_α²)/d_α`.  At `b = b₀`
this is `kIdx` (`GridParams.b₀_modEq` makes `b₀ mod d_α² = t_α`). -/
noncomputable def kIdxOf (G : GridParams) (b n : ℕ) (α : G.Atom) : ℕ :=
  (n - b % G.d α ^ 2) / G.d α

/-- **The multiplier residue is frozen in every class.**  For any `b` and any `n` in the class
of `b` mod `P₀`, `n = (b mod d_α²) + d_α²·q` and `kIdxOf G b n α = d_α·q`. -/
theorem exists_kIdxOf_eq (G : GridParams) {b X n : ℕ} (hn : n ∈ apSample X G.P₀ b)
    (α : G.Atom) : ∃ q, kIdxOf G b n α = G.d α * q := by
  have hmod : n % G.P₀ = b := (Finset.mem_filter.1 hn).2
  have hd2 : G.d α ^ 2 ∣ G.P₀ := (G.sq_d_dvd_Mprod α).trans G.Mprod_dvd_P₀
  have hbn : b % G.d α ^ 2 = n % G.d α ^ 2 := by
    rw [← hmod, Nat.mod_mod_of_dvd n hd2]
  refine ⟨n / G.d α ^ 2, ?_⟩
  have hd : 0 < G.d α := G.d_pos α
  have hsub : n - b % G.d α ^ 2 = G.d α ^ 2 * (n / G.d α ^ 2) := by
    rw [hbn]
    have := Nat.div_add_mod n (G.d α ^ 2)
    omega
  rw [kIdxOf, hsub, pow_two, mul_assoc, Nat.mul_div_cancel_left _ hd]

/-- The digit positions the class-`b` sample reads: `2·kIdxOf + h`, `h < m`. -/
noncomputable def sampledPosOf (G : GridParams) (b X m : ℕ) : Finset ℕ := by
  classical
  exact ((apSample X G.P₀ b) ×ˢ (Finset.univ : Finset G.Atom) ×ˢ Finset.range m).image
    (fun z => 2 * kIdxOf G b z.1 z.2.1 + z.2.2)

lemma mem_sampledPosOf {G : GridParams} {b X m j : ℕ} :
    j ∈ sampledPosOf G b X m ↔
      ∃ n ∈ apSample X G.P₀ b, ∃ α : G.Atom, ∃ h < m, j = 2 * kIdxOf G b n α + h := by
  classical
  unfold sampledPosOf
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, Finset.mem_range,
    true_and, Prod.exists]
  constructor
  · rintro ⟨n, α, h, ⟨hn, hh⟩, rfl⟩; exact ⟨n, hn, α, h, hh, rfl⟩
  · rintro ⟨n, hn, α, h, hh, rfl⟩; exact ⟨n, α, h, ⟨hn, hh⟩, rfl⟩

/-! ### The period column, with the `c = 0` cell included -/

/-- `{2(d·c) + h : c ≤ L/(2d), h < m}`.  Unlike `periodCol` this keeps `c = 0`, which the
class-relative index needs (`n < d_α²` is possible for any class). -/
noncomputable def periodCol₀ (d m L : ℕ) : Finset ℕ :=
  ((Finset.range (L / (2 * d) + 1)) ×ˢ Finset.range m).image (fun z => 2 * (d * z.1) + z.2)

lemma card_periodCol₀_le (d m L : ℕ) : (periodCol₀ d m L).card ≤ (L / (2 * d) + 1) * m := by
  refine le_trans Finset.card_image_le ?_
  simp [periodCol₀, Finset.card_product]

lemma mem_periodCol₀ {d m L c h : ℕ} (hd : 0 < d) (hh : h < m) (hL : 2 * (d * c) + h < L) :
    2 * (d * c) + h ∈ periodCol₀ d m L := by
  refine Finset.mem_image.2 ⟨(c, h), ?_, rfl⟩
  refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 hh⟩
  have hc : c * (2 * d) ≤ L := by nlinarith
  have := (Nat.le_div_iff_mul_le (show 0 < 2 * d by omega)).2 hc
  omega

/-! ### The union over classes is still sparse -/

variable {ι : Type*} [DecidableEq ι]

/-- **The class bound.**  Whatever the set `B` of residue classes, if the grid's multipliers lie
in a finite set `D` bounded below by `dm`, the positions the classes read below `L` number at
most `|D|·(L/(2 dm) + 1)·m` — a quantity with no `|B|` in it. -/
theorem card_filter_le_of_classes (G : GridParams) (D : Finset ℕ) (B : Finset ℕ)
    (U : ℕ → Prop) [DecidablePred U] {X m L dm : ℕ} (hdm : 0 < dm)
    (hD : ∀ α : G.Atom, G.d α ∈ D) (hdmD : ∀ d ∈ D, dm ≤ d)
    (hcov : ∀ j, j < L → U j → ∃ b ∈ B, j ∈ sampledPosOf G b X m) :
    ((Finset.range L).filter U).card ≤ D.card * ((L / (2 * dm) + 1) * m) := by
  classical
  have hsub : (Finset.range L).filter U ⊆ D.biUnion (fun d => periodCol₀ d m L) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨b, _, hjb⟩ := hcov j hj.1 hj.2
    obtain ⟨n, hn, α, h, hh, rfl⟩ := mem_sampledPosOf.1 hjb
    obtain ⟨q, hq⟩ := exists_kIdxOf_eq G hn α
    refine Finset.mem_biUnion.2 ⟨G.d α, hD α, ?_⟩
    rw [hq] at hj ⊢
    exact mem_periodCol₀ (G.d_pos α) hh hj.1
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  calc ∑ d ∈ D, (periodCol₀ d m L).card ≤ ∑ d ∈ D, (L / (2 * dm) + 1) * m := by
        refine Finset.sum_le_sum fun d hd => ?_
        refine le_trans (card_periodCol₀_le d m L) ?_
        have : L / (2 * d) ≤ L / (2 * dm) :=
          Nat.div_le_div_left (Nat.mul_le_mul_left 2 (hdmD d hd)) (by omega)
        exact Nat.mul_le_mul_right _ (by omega)
    _ = D.card * ((L / (2 * dm) + 1) * m) := by rw [Finset.sum_const, smul_eq_mul]

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy Finset

/-- **B's verdict, as a theorem: moving the residue class cannot help.**

At scale `i`, for *any* set `B` of residue classes mod `P₀` — every class, if you like, each
with its own frozen multiplier residues — the digit positions the classes read below `L` are
less than half of `[0, L)`, for every prefix length `L ≥ 2·dmin i`.

So the union over classes does **not** read density one, and the hypothesis objective B hoped to
place on it cannot force normality of `G₄`.  The obstruction is not an estimate in the E0 cone:
it is the structural identity `d_α ∣ kIdxOf G b n α`, which `exists_kIdxOf_eq` shows holds in
every class, exactly as `kIdx_spec` shows it in `b₀`'s. -/
theorem not_dense_of_any_residue (i : ℕ) (B : Finset ℕ) (U : ℕ → Prop) [DecidablePred U]
    {L : ℕ} (hL : 2 * dmin i ≤ L)
    (hcov : ∀ j, j < L → U j →
      ∃ b ∈ B, j ∈ sampledPosOf (gridAt i) b (X (KK i)) (kk i)) :
    ¬ (L ≤ 2 * ((Finset.range L).filter U).card) := by
  intro hdense
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set m := kk i with hm
  set q := L / (2 * dmin i) with hq
  have hq1 : 1 ≤ q := by
    rw [hq]
    exact (Nat.one_le_div_iff (by have := dmin_pos i; omega)).2 hL
  have hbase := card_filter_le_of_classes (gridAt i) (multipliers i) B U (dmin_pos i)
    (fun α => Finset.mem_image.2 ⟨α, Finset.mem_univ α, rfl⟩)
    (fun d hd => dmin_le_of_mem_multipliers hd) hcov
  rw [← hq] at hbase
  have hcard : ((Finset.range L).filter U).card ≤ H * ((q + 1) * m) :=
    le_trans hbase (Nat.mul_le_mul_right _ (card_multipliers_le i))
  have hq2 : q + 1 ≤ 2 * q := by omega
  set A : ℕ := 2 * (H * m) * q with hA
  have hcard2 : ((Finset.range L).filter U).card ≤ A := by
    rw [hA]
    refine le_trans hcard ?_
    calc H * ((q + 1) * m) ≤ H * ((2 * q) * m) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq2)
      _ = 2 * (H * m) * q := by ring
  -- `key_size`: `8·(H·m) ≤ 2^(i+3)·(H·m) ≤ 2·dmin`
  have hkey : 8 * (H * m) ≤ 2 * dmin i := by
    refine le_trans ?_ (key_size i)
    exact Nat.mul_le_mul_right _ (by
      have : (2 : ℕ) ^ 3 ≤ 2 ^ (i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this)
  have hqL : 2 * dmin i * q ≤ L := Nat.mul_div_le L (2 * dmin i)
  have h8 : 8 * A ≤ 2 * L := by
    rw [hA]
    calc 8 * (2 * (H * m) * q) = 2 * ((8 * (H * m)) * q) := by ring
      _ ≤ 2 * ((2 * dmin i) * q) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hkey)
      _ ≤ 2 * L := Nat.mul_le_mul_left _ hqL
  have hdm := dmin_pos i
  omega

end NormalNumbers.G4.Sched
