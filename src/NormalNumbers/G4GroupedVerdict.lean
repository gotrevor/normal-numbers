/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4RowVariance

/-!
# Objective R, the last escape: **giving up the single-`n` joint sample, at the schedule**

`DESIGN-2026-09-15-deformation.md` §0 lists three deformations the `T(K′)` verdict does not
test.  Two are closed: a non-coordinatewise ("row-balanced") cancellation
(`Sched.balanced_union_le`) and a different tensor matrix (`RowVariance.union_le_of_determining`).
The third — *let the atoms read from several sample points instead of one* — was reduced to a
size condition by `RowVariance.grouped_coeff_le` / `grouped_union_le'`, but that condition was
never checked **at the implemented schedule**.  This module checks it, and the answer corrects
the design's prose estimate.

The design (`G4BalancedRigidity`, `Grouped` docstring) read the criterion off
`grouped_union_card_le` as `w ≳ 2 log H / log dmin` — "a vanishing fraction of `H`", so
"the single-`n` sample is *not* essential".  That reading drops the family factor `|𝓕|`, which
at the schedule is `(2 dmax+1)^{2E}` with `E = K(K²+1)^{K−1}`, i.e. **already `dmin^{4E}`**.
Putting it back:

* `grouped_size_cond` — at the schedule the exact size condition of `grouped_coeff_le` holds as
  soon as the smallest group has `w ≥ 8E + 5` atoms, because
  `(2 dmax+1)^{2E} · m · H² · dmax ≤ dmin^{4E+3}` and `w − w/2 ≥ 4E + 3`;
* `grouped_balanced_union_le` — then a family of **grouped** samplers with two row-balanced
  layers reads, below `L`, at most `L / dmin^{w/2} + G · (2 dmax+1)^{2E} · H · m` positions:
  upper density `≤ dmin^{−w/2} ≤ dmin^{−(4E+2)}`;
* `grouped_block_count_le` — groups are disjoint, so `G · w ≤ H`; with `w ≥ 8E + 5` this is
  **`8 K G ≤ K² + 1`**, i.e. at most `(K²+1)/(8K) ≈ K/8` blocks.

So the joint sample *may* be broken up, but into at most about `K/8` blocks (`20000` at
`i = 0`), not into `H/w` blocks with `w` logarithmic.  The confinement rate survives: the
density stays below `dmin^{−(4E+2)}` and `4E + 2 > 10^{1660000}` at `i = 0`.

**Honest residue.**  Below `w = 8E + 5` the *counting* bound is vacuous — not the arithmetic.
Nothing here exhibits a sampler that escapes; what expires is the union bound, at exactly the
point where a block carries fewer atoms than the determining set `skel` needs
(`|skel| ≤ E`, and the threshold is `8E`).  Nothing in this module is a claim about the
normality of `G₄`.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Confine NormalNumbers.G4.RowBalance
open NormalNumbers.G4.RowVariance

/-- **The grouped size condition, at the schedule.**  `grouped_coeff_le`'s hypothesis
`|𝓕| m H² dmax ≤ 2 dmin^{w−w/2}` holds for the full row-balanced family as soon as the smallest
group carries `8E + 5` atoms. -/
theorem grouped_size_cond (i : ℕ) {w : ℕ}
    (hw : 8 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 5 ≤ w) :
    (2 * dmax i + 1) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
        * kk i * ((KK i ^ 2 + 1) ^ KK i) ^ 2 * dmax i
      ≤ 2 * dmin i ^ (w - w / 2) := by
  set E := KK i * (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set D := dmin i with hD
  set Dm := dmax i with hDm
  have h9 : 9 ≤ D := nine_le_dmin i
  have hDm2 : Dm ≤ 2 * D := dmax_le i
  have hkk1 : 1 ≤ kk i := by unfold kk; omega
  have hkey : 8 * (H * kk i) ≤ 2 * D := by
    have := key_size i
    have h8 : (8 : ℕ) ≤ 2 ^ (i + 3) := by
      have : (2 : ℕ) ^ 3 ≤ 2 ^ (i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    calc 8 * (H * kk i) ≤ 2 ^ (i + 3) * (H * kk i) := Nat.mul_le_mul_right _ h8
      _ ≤ 2 * D := this
  -- `H ≤ D`, from `8 H m ≤ 2 D` and `m ≥ 1`
  have hHD : H ≤ D := by nlinarith
  -- `2 Dm + 1 ≤ D²`
  have ha : 2 * Dm + 1 ≤ D ^ 2 := by nlinarith
  -- `m H Dm ≤ D²`
  have hb : kk i * H * Dm ≤ D ^ 2 := by nlinarith
  -- the family factor
  have hF : (2 * Dm + 1) ^ (2 * E) ≤ D ^ (4 * E) := by
    calc (2 * Dm + 1) ^ (2 * E) ≤ (D ^ 2) ^ (2 * E) := Nat.pow_le_pow_left ha _
      _ = D ^ (4 * E) := by rw [← pow_mul]; congr 1; ring
  -- the remaining factor
  have hrest : kk i * H ^ 2 * Dm ≤ D ^ 3 := by
    calc kk i * H ^ 2 * Dm = (kk i * H * Dm) * H := by ring
      _ ≤ D ^ 2 * D := Nat.mul_le_mul hb hHD
      _ = D ^ 3 := by ring
  have hprod : (2 * Dm + 1) ^ (2 * E) * kk i * H ^ 2 * Dm ≤ D ^ (4 * E + 3) := by
    calc (2 * Dm + 1) ^ (2 * E) * kk i * H ^ 2 * Dm
        = (2 * Dm + 1) ^ (2 * E) * (kk i * H ^ 2 * Dm) := by ring
      _ ≤ D ^ (4 * E) * D ^ 3 := Nat.mul_le_mul hF hrest
      _ = D ^ (4 * E + 3) := by rw [← pow_add]
  have hexp : 4 * E + 3 ≤ w - w / 2 := by omega
  have hmono : D ^ (4 * E + 3) ≤ D ^ (w - w / 2) := Nat.pow_le_pow_right (by omega) hexp
  omega

/-- **Blocks are big.**  The groups are disjoint and cover the atoms, so `G · w ≤ H`. -/
theorem grouped_block_size (i : ℕ) {G w : ℕ} (grp : (gridAt i).Atom → Fin G)
    (hwg : ∀ g : Fin G, w ≤ Fintype.card {α : (gridAt i).Atom // grp α = g}) :
    G * w ≤ (KK i ^ 2 + 1) ^ KK i := by
  classical
  have hcard : (Finset.univ : Finset ((gridAt i).Atom)).card
      = ∑ g : Fin G, (Finset.univ.filter (fun α => grp α = g)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (grp x))
  have hsub : ∀ g : Fin G,
      Fintype.card {α : (gridAt i).Atom // grp α = g}
        = (Finset.univ.filter (fun α => grp α = g)).card := by
    intro g; simp [Fintype.card_subtype]
  have hge : ∑ _g : Fin G, w ≤ ∑ g : Fin G, (Finset.univ.filter (fun α => grp α = g)).card :=
    Finset.sum_le_sum fun g _ => by rw [← hsub g]; exact hwg g
  have hGw : G * w = ∑ _g : Fin G, w := by
    simp [Finset.sum_const, Finset.card_univ]
  rw [hGw]
  calc ∑ _g : Fin G, w ≤ ∑ g : Fin G, (Finset.univ.filter (fun α => grp α = g)).card := hge
    _ = (Finset.univ : Finset ((gridAt i).Atom)).card := hcard.symm
    _ = (KK i ^ 2 + 1) ^ KK i := by rw [Finset.card_univ, card_Atom_gridAt]

/-- **At most `(K²+1)/(8K) ≈ K/8` blocks.**  A grouping whose smallest block meets the size
condition `w ≥ 8E + 5` has `8 K G ≤ K² + 1`. -/
theorem grouped_block_count_le (i : ℕ) {G w : ℕ} (grp : (gridAt i).Atom → Fin G)
    (hwg : ∀ g : Fin G, w ≤ Fintype.card {α : (gridAt i).Atom // grp α = g})
    (hw : 8 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 5 ≤ w) :
    8 * KK i * G ≤ KK i ^ 2 + 1 := by
  have hK := KK_ge i
  set E1 := (KK i ^ 2 + 1) ^ (KK i - 1) with hE1
  have hE1pos : 0 < E1 := Nat.one_le_pow _ _ (by positivity)
  have hH : (KK i ^ 2 + 1) ^ KK i = (KK i ^ 2 + 1) * E1 := by
    rw [hE1, ← pow_succ']; congr 1; omega
  have hGw := grouped_block_size i grp hwg
  rw [hH] at hGw
  -- `G * (8 * K * E1) ≤ G * w ≤ (K²+1) * E1`
  have hwE : 8 * (KK i * E1) ≤ w := by omega
  have hstep : G * (8 * (KK i * E1)) ≤ (KK i ^ 2 + 1) * E1 :=
    le_trans (Nat.mul_le_mul_left G hwE) hGw
  have hstep' : (8 * KK i * G) * E1 ≤ (KK i ^ 2 + 1) * E1 := by
    calc (8 * KK i * G) * E1 = G * (8 * (KK i * E1)) := by ring
      _ ≤ (KK i ^ 2 + 1) * E1 := hstep
  exact Nat.le_of_mul_le_mul_right hstep' hE1pos

/-- **The grouped verdict at the schedule.**  A family of samplers of the tensor shape whose
atoms are partitioned into `G` blocks, each block sharing one sample point, each member having
two distinct row-balanced layers, and each block carrying at least `w ≥ 8E + 5` atoms, reads
below `L` at most `L / dmin^{w/2} + G · (2 dmax+1)^{2E} · H · m` positions — upper density
`≤ dmin^{−w/2}`, the same shape as the single-`n` verdict `balanced_union_le`. -/
theorem grouped_balanced_union_le (i : ℕ) {G : ℕ} (grp : (gridAt i).Atom → Fin G)
    {κ : Type*} [DecidableEq κ] (𝓕 : Finset κ)
    (d t : κ → (gridAt i).Atom → ℕ) (P : κ → Fin G → Finset ℕ) {w L : ℕ}
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (hbal : ∀ ν ∈ 𝓕, ∃ j j' : ℕ, j ≠ j' ∧
      RowBalance.Balanced (RowBalance.layer j (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ))) ∧
      RowBalance.Balanced (RowBalance.layer j' (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ))))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin i ≤ d ν α ∧ d ν α ≤ dmax i)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax i)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ g, ∀ n ∈ P ν g, ∀ α, grp α = g → n % d ν α = t ν α)
    (hwg : ∀ g : Fin G, w ≤ Fintype.card {α : (gridAt i).Atom // grp α = g})
    (hGH : G ≤ (KK i ^ 2 + 1) ^ KK i)
    (hw : 8 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 5 ≤ w)
    (U : ℕ → Prop) [DecidablePred U]
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ g, ∃ n ∈ P ν g, ∃ α, grp α = g ∧ ∃ h < kk i,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin i : ℝ) ^ (w / 2)
        + (G : ℝ) * (((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
            * (((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i)) := by
  classical
  set E := KK i * (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  -- the family count, exactly as in `balanced_union_le`
  have hcardF : 𝓕.card ≤ (2 * dmax i + 1) ^ (2 * E) := by
    set 𝓕' := 𝓕.image (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) with h𝓕'
    have hc : 𝓕.card = 𝓕'.card := (Finset.card_image_of_injOn hinj).symm
    rw [hc]
    have h1 := card_mdf_pairs_le (K := KK i) (s := KK i ^ 2) (M := dmax i) 𝓕'
      (by
        intro p hp
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨j, j', hne, hj, hj'⟩ := hbal ν hν
        exact mdf_d_t_of_two_balanced_layers hne hj hj')
      (by
        intro p hp α
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        constructor
        · show |((d ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast (hd ν hν α).2
        · show |((t ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast ht ν hν α)
    refine le_trans h1 (Nat.pow_le_pow_right (by omega) ?_)
    have := card_skel_le (KK i) (KK i ^ 2)
    omega
  -- the size condition
  have hbig : 𝓕.card * kk i * Fintype.card ((gridAt i).Atom) ^ 2 * dmax i
      ≤ 2 * dmin i ^ (w - w / 2) := by
    rw [card_Atom_gridAt]
    refine le_trans ?_ (grouped_size_cond i hw)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ hcardF))
  have hGH' : G ≤ Fintype.card ((gridAt i).Atom) := by rw [card_Atom_gridAt]; exact hGH
  have hbase := grouped_union_le' (ι := (gridAt i).Atom) grp 𝓕 d t P
    (dmin := dmin i) (dmax := dmax i) (m := kk i) (L := L) (w := w)
    (dmin_pos i) hwg hGH' hbig (fun ν hν α => hd ν hν α) hcop hP U hcov
  rw [card_Atom_gridAt, ← hH] at hbase
  refine le_trans hbase (add_le_add le_rfl ?_)
  have hF' : (𝓕.card : ℝ) ≤ ((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * E) := by exact_mod_cast hcardF
  have hG0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg _
  have hHm : (0 : ℝ) ≤ ((H : ℕ) : ℝ) * kk i := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hF' hHm) hG0

end NormalNumbers.G4.Sched

/-! ### The seam: the capture budget *supplies* the two cancelled layers

`RowVariance.two_layers_of_dyadic` **proves** `2 ≤ K′` from the sampler's released-row second
moment; `RowVariance.cancelled_union_le` and `grouped_balanced_union_le` **assume** it.  Until
now nothing joined them, so the verdict read as an implication with an unmet hypothesis.

`Capture.InsideCapture K K′` packages the analytic side of one sampler — the dyadic rough-prime
data, the released weights, the bounded shift gaps, the three scale conditions and the capture
inequality — as a single `Prop` in `K` and `K′`.  Then `budget_confines` and
`grouped_budget_confines` are the verdict with `2 ≤ K′` **derived**: a family of samplers at the
schedule, each inside the capture budget and each cancelling its first `K′` layers, reads upper
density `≤ dmin^{−H/2}` (joint sample) resp. `≤ dmin^{−w/2}` (blocks of size `w ≥ 8E + 5`). -/

namespace NormalNumbers.G4.Capture

open NormalNumbers.G4.RowVariance

/-- **The two-layer conclusion in Mertens form.**  `two_layers_of_dyadic` needs its rough primes
to lie in `[T, 2T]` with `|S| ≥ 1920·2^K·k` — a *count* of primes in a dyadic interval, which
mathlib does not supply (only `Nat.bertrand`, one prime).  The `|S|`-free Mertens bound
`roughRowVarianceLower_mertens` has no upper bound on `p`, and `scales_satisfiable` proves its
hypotheses meetable for every `K`, `k`, `Q`.  This is `Budget.budget_forces_two_layers` fed by
it; the strict positivity of the constant comes for free, since `ε ≥ 3/(T−1) > 0`. -/
theorem two_layers_of_mertens {K L T Q c0 N k : ℕ} (hT : 4 ≤ T) (hQ : 0 < Q) (hQT : Q < T)
    (hN : 0 < N) (hK : 8 ≤ K) (hL : 0 < L)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (hge : ∀ p ∈ S, T ≤ p)
    (ρ : ℕ → Fin (2 ^ K) × Fin L → ℤ) (w : ℕ → Fin (2 ^ K) × Fin L → ℝ)
    (hw : ∀ K'' i, |w K'' i| = (1 / 4 : ℝ) ^ (K'' + 1 + (i.2 : ℕ)))
    (hΔ : ∀ (K'' : ℕ) (i j), i ≠ j →
      ρ K'' i - ρ K'' j ≠ 0 ∧ (ρ K'' i - ρ K'' j).natAbs < T ^ (k + 1))
    {V : ℝ} (hV : V ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2))
    (hsmall : (4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N)
        * (5 * (2 : ℝ) ^ K / 3)
      ≤ (V - 3 * (S.card : ℝ) ^ 2 / N) / 2)
    {K' : ℕ}
    (hcap : avg ((Finset.range N).image (fun x => c0 + Q * x))
        (fun n => (∑ i, w K' i * fluct S (ρ K' i) n) ^ 2)
      ≤ (((V - 3 * (S.card : ℝ) ^ 2 / N) / 2) * (1 - (1 / 16 : ℝ) ^ L))
          * ((1 : ℝ) / 2) ^ (K / 2)) :
    2 ≤ K' := by
  have hT1 : (0 : ℝ) < (T : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  have h1 : (0 : ℝ) ≤ 4 * (k : ℝ) / T := by positivity
  have h2 : (0 : ℝ) < 3 / ((T : ℝ) - 1) := div_pos (by norm_num) hT1
  have h3 : (0 : ℝ) ≤ 3 * (S.card : ℝ) ^ 2 / N := by positivity
  have hApos : (0 : ℝ) < 5 * (2 : ℝ) ^ K / 3 := by positivity
  have hεpos : (0 : ℝ) < 4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N := by
    linarith
  have hc0 : (0 : ℝ) < (V - 3 * (S.card : ℝ) ^ 2 / N) / 2 := by
    nlinarith [mul_pos hεpos hApos]
  have hL16 : (0 : ℝ) < 1 - (1 / 16 : ℝ) ^ L := by
    have : (1 / 16 : ℝ) ^ L < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  exact RowBalance.Budget.budget_forces_two_layers (mul_pos hc0 hL16) hK
    (roughRowVarianceLower_mertens hT hQ hQT hN S hprime hge ρ w hw hΔ hV hsmall) hcap

/-- **The analytic side of one sampler, packaged.**  Everything `two_layers_of_mertens` consumes
except the row size `K` and the cancelled-layer count `K′`: a rough prime set `S` above the
roughness threshold `T > Q`, released weights `w` of the standard shape `4^{−(K″+1+ℓ)}`,
released shifts `ρ` with distinct, `T^{k+1}`-bounded gaps, the variance target `V`, the
correlation-level inequality, and the capture inequality at `K′`. -/
def InsideCapture (K K' : ℕ) : Prop :=
  ∃ (L T Q c0 N k : ℕ) (S : Finset ℕ)
    (ρ : ℕ → Fin (2 ^ K) × Fin L → ℤ) (w : ℕ → Fin (2 ^ K) × Fin L → ℝ) (V : ℝ),
    4 ≤ T ∧ 0 < Q ∧ Q < T ∧ 0 < N ∧ 0 < L ∧
    (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, T ≤ p) ∧
    (∀ K'' i, |w K'' i| = (1 / 4 : ℝ) ^ (K'' + 1 + (i.2 : ℕ))) ∧
    (∀ (K'' : ℕ) (i j), i ≠ j →
      ρ K'' i - ρ K'' j ≠ 0 ∧ (ρ K'' i - ρ K'' j).natAbs < T ^ (k + 1)) ∧
    V ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2) ∧
    (4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N) * (5 * (2 : ℝ) ^ K / 3)
      ≤ (V - 3 * (S.card : ℝ) ^ 2 / N) / 2 ∧
    avg ((Finset.range N).image (fun x => c0 + Q * x))
        (fun n => (∑ i, w K' i * fluct S (ρ K' i) n) ^ 2)
      ≤ (((V - 3 * (S.card : ℝ) ^ 2 / N) / 2) * (1 - (1 / 16 : ℝ) ^ L))
          * ((1 : ℝ) / 2) ^ (K / 2)

/-- **The budget forces two cancelled layers.**  `two_layers_of_mertens`, with its analytic data
existentially quantified. -/
theorem two_le_of_insideCapture {K K' : ℕ} (hK : 8 ≤ K) (h : InsideCapture K K') : 2 ≤ K' := by
  obtain ⟨L, T, Q, c0, N, k, S, ρ, w, V, hT, hQ, hQT, hN, hL, hprime, hge, hw, hΔ, hV,
    hsmall, hcap⟩ := h
  exact two_layers_of_mertens hT hQ hQT hN hK hL S hprime hge ρ w hw hΔ hV hsmall hcap

/-! ### `InsideCapture` is not an empty hypothesis

An existential hypothesis that nothing satisfies would make `budget_confines` vacuously true.
`structural_satisfiable` rules that out for everything except the capture inequality itself:
for every row size `K`, window length `L > 0` and gap exponent `k`, all of `InsideCapture`'s
structural conjuncts are simultaneously meetable.  The trick is that the frozen modulus `Q` is
existential too, so taking `Q = 2^K · L` makes `scales_satisfiable`'s own conclusion `Q < T`
deliver the shift-gap bound for free.

What is left is exactly the sampler's own capture inequality — a genuine constraint, and a
consistent one: `RoughRowVarianceLower` forces `sm K′ ≥ c·2^K·16^{−K′}/15` while the budget caps
it at `c·2^{−K/2}`, and the two meet precisely when `4K′ ≳ 3K/2`, i.e. `K′ ≳ 3K/8` — DESIGN §3's
estimate (E), recovered as the consistency range of the packaged `Prop`. -/

/-- **Structural non-vacuity of `InsideCapture`.**  Every conjunct but the capture inequality is
satisfiable, for every `K`, `k` and every `L > 0`. -/
theorem structural_satisfiable (K k L : ℕ) (hL : 0 < L) :
    ∃ (T Q c0 N : ℕ) (S : Finset ℕ)
      (ρ : ℕ → Fin (2 ^ K) × Fin L → ℤ) (w : ℕ → Fin (2 ^ K) × Fin L → ℝ) (V : ℝ),
      4 ≤ T ∧ 0 < Q ∧ Q < T ∧ 0 < N ∧
      (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, T ≤ p) ∧
      (∀ K'' i, |w K'' i| = (1 / 4 : ℝ) ^ (K'' + 1 + (i.2 : ℕ))) ∧
      (∀ (K'' : ℕ) (i j), i ≠ j →
        ρ K'' i - ρ K'' j ≠ 0 ∧ (ρ K'' i - ρ K'' j).natAbs < T ^ (k + 1)) ∧
      V ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2) ∧
      (4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N) * (5 * (2 : ℝ) ^ K / 3)
        ≤ (V - 3 * (S.card : ℝ) ^ 2 / N) / 2 := by
  classical
  -- the frozen modulus is existential: take it to be the index count, so `Q < T` bounds the gaps
  set Q : ℕ := 2 ^ K * L with hQdef
  have hQpos : 0 < Q := by
    have h2 : 0 < 2 ^ K := by positivity
    exact Nat.mul_pos h2 hL
  obtain ⟨T, S, N, hT, hQT, hN, hprime, hge, hV, hsmall⟩ := scales_satisfiable K k Q
  refine ⟨T, Q, 0, N, S,
    fun _ i => ((finProdFinEquiv i : ℕ) : ℤ),
    fun K'' i => (1 / 4 : ℝ) ^ (K'' + 1 + (i.2 : ℕ)), 1,
    hT, hQpos, hQT, hN, hprime, hge, ?_, ?_, hV, hsmall⟩
  · intro K'' i
    exact abs_of_pos (by positivity)
  · intro K'' i j hij
    have hlt : ∀ x : Fin (2 ^ K) × Fin L, ((finProdFinEquiv x : ℕ) : ℤ) < (Q : ℤ) := by
      intro x
      have := (finProdFinEquiv x).isLt
      exact_mod_cast this
    have hnn : ∀ x : Fin (2 ^ K) × Fin L, (0 : ℤ) ≤ ((finProdFinEquiv x : ℕ) : ℤ) := by
      intro x; positivity
    have hne : ((finProdFinEquiv i : ℕ) : ℤ) ≠ ((finProdFinEquiv j : ℕ) : ℤ) := by
      intro h
      exact hij (finProdFinEquiv.injective (Fin.ext (by exact_mod_cast h)))
    refine ⟨sub_ne_zero_of_ne hne, ?_⟩
    have hTk : (T : ℤ) ≤ (T : ℤ) ^ (k + 1) := by
      have : (T : ℕ) ≤ T ^ (k + 1) := Nat.le_self_pow (by omega) _
      exact_mod_cast this
    have hQTz : (Q : ℤ) < (T : ℤ) := by exact_mod_cast hQT
    have habs : |((finProdFinEquiv i : ℕ) : ℤ) - ((finProdFinEquiv j : ℕ) : ℤ)| < (T : ℤ) ^ (k + 1) := by
      rw [abs_lt]
      constructor
      · have := hlt j; have := hnn i; linarith
      · have := hlt i; have := hnn j; linarith
    show (((finProdFinEquiv i : ℕ) : ℤ) - ((finProdFinEquiv j : ℕ) : ℤ)).natAbs < T ^ (k + 1)
    have hz : ((((finProdFinEquiv i : ℕ) : ℤ) - ((finProdFinEquiv j : ℕ) : ℤ)).natAbs : ℤ)
        < ((T ^ (k + 1) : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      push_cast
      exact habs
    exact Nat.cast_lt.mp hz

end NormalNumbers.G4.Capture

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Confine NormalNumbers.G4.RowBalance
open NormalNumbers.G4.RowVariance

/-- **The verdict with the budget supplying its own hypothesis.**  A family of samplers at scale
`i` of the schedule, each of which (a) sits inside the capture budget and (b) cancels its first
`K′` layers, reads below `L` at most `L / dmin^{H/2} + (2 dmax+1)^{2E} · H · m` positions.  The
`2 ≤ K′` that `cancelled_union_le` assumes is **derived** here, from `InsideCapture`. -/
theorem budget_confines (i : ℕ)
    {κ : Type*} [DecidableEq κ] (𝓕 : Finset κ)
    (d t : κ → (gridAt i).Atom → ℕ) (P : κ → Finset ℕ) (K' : κ → ℕ)
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (hbudget : ∀ ν ∈ 𝓕, Capture.InsideCapture (KK i) (K' ν))
    (hcancel : ∀ ν ∈ 𝓕,
      LayersCancelled (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ)) (K' ν))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin i ≤ d ν α ∧ d ν α ≤ dmax i)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax i)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ n ∈ P ν, ∀ α, n % d ν α = t ν α)
    (U : ℕ → Prop) [DecidablePred U] {L : ℕ}
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ n ∈ P ν, ∃ α, ∃ h < kk i,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i / 2)
        + ((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
            * (((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i) :=
  cancelled_union_le i 𝓕 d t P hinj K'
    (fun ν hν => Capture.two_le_of_insideCapture (by have := KK_ge i; omega) (hbudget ν hν))
    hcancel hd ht hcop hP U hcov

/-- **The grouped verdict with the budget supplying its own hypothesis.**  Same statement with
the atoms cut into `G` blocks of size `≥ w ≥ 8E + 5`, each block sharing one sample point: the
rate is `dmin^{−w/2}`, and `grouped_block_count_le` caps `G` at `(K²+1)/(8K)`. -/
theorem grouped_budget_confines (i : ℕ) {G : ℕ} (grp : (gridAt i).Atom → Fin G)
    {κ : Type*} [DecidableEq κ] (𝓕 : Finset κ)
    (d t : κ → (gridAt i).Atom → ℕ) (P : κ → Fin G → Finset ℕ) (K' : κ → ℕ) {w L : ℕ}
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (hbudget : ∀ ν ∈ 𝓕, Capture.InsideCapture (KK i) (K' ν))
    (hcancel : ∀ ν ∈ 𝓕,
      LayersCancelled (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ)) (K' ν))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin i ≤ d ν α ∧ d ν α ≤ dmax i)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax i)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ g, ∀ n ∈ P ν g, ∀ α, grp α = g → n % d ν α = t ν α)
    (hwg : ∀ g : Fin G, w ≤ Fintype.card {α : (gridAt i).Atom // grp α = g})
    (hGH : G ≤ (KK i ^ 2 + 1) ^ KK i)
    (hw : 8 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 5 ≤ w)
    (U : ℕ → Prop) [DecidablePred U]
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ g, ∃ n ∈ P ν g, ∃ α, grp α = g ∧ ∃ h < kk i,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin i : ℝ) ^ (w / 2)
        + (G : ℝ) * (((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
            * (((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i)) :=
  grouped_balanced_union_le i grp 𝓕 d t P hinj
    (fun ν hν => two_balanced_of_cancelled (hcancel ν hν)
      (Capture.two_le_of_insideCapture (by have := KK_ge i; omega) (hbudget ν hν)))
    hd ht hcop hP hwg hGH hw U hcov

end NormalNumbers.G4.Sched
