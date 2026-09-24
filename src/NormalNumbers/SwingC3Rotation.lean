/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CastingOut
import NormalNumbers.SwingC3Split
import NormalNumbers.SwingC3Lambert
import NormalNumbers.SwingC3Cover

/-!
# The rotation route to `ConjC3`, split into two named leaves

`SwingC3.lean` reduced `ConjC3` to `LargeTailLaw`: the existence of a *limit law* for the
large-prime tail, the same in every steering class.  That hypothesis is stronger than the
argument needs in two independent ways, and both cost real mathematics:

* it asks for genuine limits, so the analytic leaf has to *identify* something;
* it asks the steering constants `θ(a) = tailSmall P b a` to be exactly the `b^ℓ` multiples of
  `b^{−ℓ}`, which they are not — the window slots `j > ℓ` contribute an uncontrolled
  `O(π(P)·b^{−ℓ})`.

This file replaces it by the two things the covering argument actually uses.

* **`RotationCover`** (Leaf A, arithmetic).  A finite family of residue classes, distinct
  modulo `Q`, whose small-prime rotations `tailSmall P b (a k)` *cover* the circle at scale
  `len`: every point is carried into the target arc by at least one of them.  No exactness, no
  grid — a `len`-net suffices, and the CRT steering of `SwingC3Split.exists_crt_pattern` builds
  one (with `ℓ' ≫ ℓ` slots so that the uncontrolled remainder is below the net spacing).
* **`TailLargeDecouple`** (Leaf B, analytic).  The empirical distribution of
  `fract (θ + tailLarge P b n)` over `n < N` is asymptotically the same on each residue class
  mod `Q` as it is globally.  *No limit is asserted to exist.*  Since every prime factor of `Q`
  is `≤ P` and `tailLarge` sees only primes `> P`, this is the fundamental-lemma-of-the-sieve
  statement that large primes do not see small ones; it is not Selberg–Delange, and it is not a
  correlation (Chowla-type) statement about `ω` at shifted arguments.

`isRich_of_rotationRoute` below is the covering argument and is **proved**.  The structure is:
for the `M` classes, `∑_k #{n < N : n ≡ a k, fract(θ_k + tailLarge n) ∈ I}` is at least
`(1/Q)·∑_k #{n < N : fract(θ_k + tailLarge n) ∈ I} + o(N)` by Leaf B, the inner sum is at least
`N` by Leaf A (covering: every `n` is caught by some `k`), and the `M` counted sets are pairwise
disjoint because the classes are.  So the word's occurrence count is at least `N/(2Q)`.

Covering — not partition — is the right notion: a sum of masses dominates the mass of the
union, and that is all the lower bound needs.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

open PrimeLambert

/-! ### The two leaves -/

/-- **Leaf A, as a property of a family of classes.**  The rotations `tailSmall P b (a k)`,
`k < M`, cover the arc `[α, α + len)`: every real `y` is carried into the arc by one of them.
Only the `M` values `tailSmall P b (a k)` matter, so this is a statement about a finite set of
rotation constants being a `len`-net of the circle. -/
def RotationCover (b P M : ℕ) (a : ℕ → ℕ) (α len : ℝ) : Prop :=
  ∀ y : ℝ, ∃ k, k < M ∧ Int.fract (tailSmall P b (a k) + y) ∈ Set.Ico α (α + len)

open Classical in
/-- **Leaf B.**  The large-prime tail decouples from the residue class mod `Q`: for every
class `r`, every rotation `θ` and every arc, the count on the class is `1/Q` of the global
count, up to `o(N)`.  No limit law is asserted — only that the two counting functions agree
after the natural normalisation.

This is the exact analytic content of "primes `> P` do not see the residue class mod `Q`"
when every prime factor of `Q` is `≤ P`.  At the level of individual divisibility patterns it
is *exactly* true by the Chinese remainder theorem; the content is the passage from patterns to
the real-valued functional `tailLarge`, i.e. a fundamental-lemma truncation. -/
def TailLargeDecouple (b P Q : ℕ) : Prop :=
  ∀ (r : ℕ) (θ α len : ℝ),
    Tendsto (fun N : ℕ =>
      ((((range N).filter (fun n => n ≡ r [MOD Q] ∧
            Int.fract (θ + tailLarge P b n) ∈ Set.Ico α (α + len))).card : ℝ)
        - (((range N).filter (fun n =>
            Int.fract (θ + tailLarge P b n) ∈ Set.Ico α (α + len))).card : ℝ) / (Q : ℝ)) / N)
      atTop (𝓝 0)

/-- **Leaf B is a statement about ONE real number's orbit.**  `fract (tailLarge P b n)` is
literally `orbit b (L_P) n` (`SwingC3Lambert.fract_tailLarge_eq_orbit`), so `TailLargeDecouple`
says: the `×b` orbit of the large-prime Lambert number `L_P` has the same empirical law on every
residue class mod `Q`.  Combined with `SwingC3Lambert.orbit_succ_eq` — class `r+1` is the `×b`
image of class `r` — this is equivalent to saying that every weak limit of the
`×b^Q`-empirical measures of `L_P` is `×b`-invariant. -/
theorem tailLargeDecouple_iff_orbit {b : ℕ} (hb : 2 ≤ b) (P Q : ℕ) :
    TailLargeDecouple b P Q ↔
    ∀ (r : ℕ) (θ α len : ℝ),
      Tendsto (fun N : ℕ =>
        ((((range N).filter (fun n => n ≡ r [MOD Q] ∧
              Int.fract (θ + orbit b (largeLambert P b) n) ∈ Set.Ico α (α + len))).card : ℝ)
          - (((range N).filter (fun n =>
              Int.fract (θ + orbit b (largeLambert P b) n) ∈ Set.Ico α (α + len))).card : ℝ)
            / (Q : ℝ)) / N)
        atTop (𝓝 0) := by
  classical
  have key : ∀ (θ : ℝ) (n : ℕ), Int.fract (θ + tailLarge P b n)
      = Int.fract (θ + orbit b (largeLambert P b) n) := by
    intro θ n
    rw [← fract_tailLarge_eq_orbit hb, fract_add_fract_right]
  constructor
  · intro h r θ α len
    simpa only [key] using h r θ α len
  · intro h r θ α len
    simpa only [← key] using h r θ α len

/-- The two leaves packaged for one arc. -/
def RotationRoute (b : ℕ) : Prop :=
  ∀ α len : ℝ, 0 ≤ α → 0 < len → α + len ≤ 1 →
    ∃ (P Q M : ℕ) (a : ℕ → ℕ), 0 < Q ∧ 0 < M ∧
      (∀ p, p ≤ P → p.Prime → p ∣ Q) ∧
      (∀ k, k < M → ∀ k', k' < M → a k ≡ a k' [MOD Q] → k = k') ∧
      RotationCover b P M a α len ∧ TailLargeDecouple b P Q

/-! ### The counting core

A purely numerical lemma: `M` counting families `A k`, `B k` with `A k` decoupled from `B k`
at rate `1/Q`, `∑ B k ≥ N` (covering) and `∑ A k ≤ C N` (disjointness) force `C N ≥ N/(2Q)`. -/

lemma density_lower_of_decouple {Q M : ℕ} (hQ : 0 < Q) (A B : ℕ → ℕ → ℕ) (C : ℕ → ℕ)
    (hdec : ∀ k, k < M →
      Tendsto (fun N : ℕ => (((A k N : ℝ) - (B k N : ℝ) / Q) / N)) atTop (𝓝 0))
    (hcov : ∀ N, N ≤ ∑ k ∈ range M, B k N)
    (hdisj : ∀ N, ∑ k ∈ range M, A k N ≤ C N) :
    ∀ᶠ N in atTop, (1 / (2 * (Q : ℝ))) * N ≤ (C N : ℝ) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hg : Tendsto (fun N : ℕ => ∑ k ∈ range M, (((A k N : ℝ) - (B k N : ℝ) / Q) / N))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (range M) (fun k hk => hdec k (mem_range.1 hk))
    simpa using this
  have hneg : -(1 / (2 * (Q : ℝ))) < 0 := by
    have : (0 : ℝ) < 1 / (2 * Q) := by positivity
    linarith
  have hev := Filter.Tendsto.eventually_const_lt hneg hg
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hQ' : (Q : ℝ) ≠ 0 := ne_of_gt hQR
  have hN' : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hsplit : ∑ k ∈ range M, (((A k N : ℝ) - (B k N : ℝ) / Q) / N)
      = (∑ k ∈ range M, (A k N : ℝ)) / N - (∑ k ∈ range M, (B k N : ℝ)) / (Q * N) := by
    have hterm : ∀ k : ℕ, (((A k N : ℝ) - (B k N : ℝ) / Q) / N)
        = (A k N : ℝ) / N - (B k N : ℝ) / (Q * N) := by
      intro k; field_simp
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  rw [hsplit] at hN
  have hB : (N : ℝ) ≤ ∑ k ∈ range M, (B k N : ℝ) := by
    have := hcov N
    push_cast
    exact_mod_cast this
  have hBd : (1 : ℝ) / Q ≤ (∑ k ∈ range M, (B k N : ℝ)) / (Q * N) := by
    rw [div_le_div_iff₀ hQR (by positivity)]
    nlinarith
  have hhalf : (1 : ℝ) / (2 * Q) + 1 / (2 * Q) = 1 / Q := by field_simp; ring
  have hA : (1 : ℝ) / (2 * Q) ≤ (∑ k ∈ range M, (A k N : ℝ)) / N := by linarith
  have hAC : (∑ k ∈ range M, (A k N : ℝ)) ≤ (C N : ℝ) := by
    have := hdisj N
    push_cast
    exact_mod_cast this
  have := (le_div_iff₀ hNR).1 hA
  linarith

/-! ### The covering argument -/

/-- **`IsRich` from the rotation route.**  Proved: the whole covering argument, with the two
leaves as hypotheses. -/
theorem isRich_of_rotationRoute {b : ℕ} (hb : 2 ≤ b) (H : RotationRoute b) :
    IsRich b (primeLambertAtBase b) := by
  classical
  intro w hw
  have hb0 : 0 < b := by omega
  have hbR : (0 : ℝ) < (b : ℝ) ^ w.length := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
    positivity
  have hVlt : blockNatVal b w < b ^ w.length := blockNatVal_lt b w hw
  set V : ℕ := blockNatVal b w with hV
  set α : ℝ := (V : ℝ) / (b : ℝ) ^ w.length with hα
  set len : ℝ := 1 / (b : ℝ) ^ w.length with hlen
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hlen0 : 0 < len := by rw [hlen]; positivity
  have hsum : α + len = ((V : ℝ) + 1) / (b : ℝ) ^ w.length := by
    rw [hα, hlen]; ring
  have hαlen : α + len ≤ 1 := by
    rw [hsum, div_le_one hbR]
    have : (V : ℝ) + 1 ≤ ((b ^ w.length : ℕ) : ℝ) := by exact_mod_cast hVlt
    simpa using this
  obtain ⟨P, Q, M, a, hQ0, hM0, hQP, hinj, hcov, hdec⟩ := H α len hα0 hlen0 hαlen
  set θ : ℕ → ℝ := fun k => tailSmall P b (a k) with hθ
  set A : ℕ → ℕ → ℕ := fun k N =>
    ((range N).filter (fun n => n ≡ a k [MOD Q] ∧
      Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len))).card with hA
  set B : ℕ → ℕ → ℕ := fun k N =>
    ((range N).filter (fun n =>
      Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len))).card with hB
  set C : ℕ → ℕ := fun N =>
    ((range N).filter (fun n => OccursAt b (primeLambertAtBase b) w n)).card with hC
  -- covering: every `n` is caught by at least one class
  have hcovN : ∀ N, N ≤ ∑ k ∈ range M, B k N := by
    intro N
    have hsub : (range N) ⊆ (range M).biUnion (fun k =>
        (range N).filter (fun n =>
          Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len))) := by
      intro n hn
      obtain ⟨k, hkM, hk⟩ := hcov (tailLarge P b n)
      exact Finset.mem_biUnion.2 ⟨k, mem_range.2 hkM, mem_filter.2 ⟨hn, hk⟩⟩
    calc N = (range N).card := (card_range N).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ k ∈ range M, B k N := Finset.card_biUnion_le
  -- disjointness: distinct classes, and each counted point is an occurrence
  have hdisjN : ∀ N, ∑ k ∈ range M, A k N ≤ C N := by
    intro N
    rw [hA, hC]
    simp only
    rw [← Finset.card_biUnion]
    · refine Finset.card_le_card fun n hn => ?_
      rw [Finset.mem_biUnion] at hn
      obtain ⟨k, -, hk⟩ := hn
      rw [mem_filter] at hk ⊢
      refine ⟨hk.1, ?_⟩
      rw [occursAt_iff_orbit_mem b hb _ w hw n,
        orbit_eq_rotation hb hQP hk.2.1, ← hV, ← hα, ← hsum]
      exact hk.2.2
    · intro k hk k' hk' hne
      refine Finset.disjoint_left.2 fun n hn hn' => ?_
      rw [mem_filter] at hn hn'
      exact hne (hinj k (mem_range.1 hk) k' (mem_range.1 hk') (hn.2.1.symm.trans hn'.2.1))
  refine ⟨1 / (2 * (Q : ℝ)), by positivity, ?_⟩
  exact density_lower_of_decouple hQ0 A B C (fun k _ => hdec (a k) (θ k) α len) hcovN hdisjN

/-! ### The leaves, open

Both are stated at full strength and neither is used anywhere else. -/

/-- **Leaf A — PROVED** (`SwingC3Cover.exists_rotationCover_core`).  The steering classes exist
and their rotations cover any arc.

*The construction.*  Fix `ℓ'` with `b^{ℓ'} ≫ ℓ' / len`.  Let `R = ∏_{p ≤ ℓ'+1} p` and let `S`
be the set of primes in `(ℓ'+1, P]`, where `P` is chosen so that `|S| = (b−1)·ℓ'`.  Put
`Q = R · ∏_{p ∈ S} p = ∏_{p ≤ P} p`.  For each vector `k ∈ {0,…,b−1}^{ℓ'}` use
`SwingC3Split.exists_crt_pattern` (with window length `ℓ'+1`, dumping the unused primes of `S`
into slot `ℓ'+1`) together with a fixed residue mod `R`, to get a class `a` with
`ω_{≤P}(a+j) = c_j + k_j` for `j ≤ ℓ'`, where `c_j = #{p ≤ ℓ'+1 : p ∣ a₀+j}` is a constant.
Then `tailSmall P b a = C + ∑_{j ≤ ℓ'} k_j b^{−j} + ρ_a` with `0 ≤ ρ_a ≤ π(P)·b^{−ℓ'}/(b−1)`.
The head runs over *every* multiple of `b^{−ℓ'}`, so the constants form a grid of spacing
`b^{−ℓ'}` perturbed by at most `ρ`; since `b^{−ℓ'}(1 + π(P)) < len` by the choice of `ℓ'`
(`π(P) ≤ b·ℓ' + 1`), that family is a `len`-net and covers the arc.

Nothing here is deep; it is a finite CRT computation plus Bertrand-type prime counting. -/
theorem exists_rotationCover (b : ℕ) (hb : 2 ≤ b) (α len : ℝ) (hα : 0 ≤ α) (hlen : 0 < len)
    (hαlen : α + len ≤ 1) :
    ∃ (P Q M : ℕ) (a : ℕ → ℕ), 0 < Q ∧ 0 < M ∧
      (∀ p, p ≤ P → p.Prime → p ∣ Q) ∧
      (∀ p, p.Prime → p ∣ Q → p ≤ P) ∧
      (∀ k, k < M → ∀ k', k' < M → a k ≡ a k' [MOD Q] → k = k') ∧
      RotationCover b P M a α len :=
  exists_rotationCover_core hb α len hα hlen hαlen

/-- **Leaf B — open (the analytic crux).**  Every prime factor of `Q` is `≤ P`, and
`tailLarge P b` is built only from primes `> P`; so the class of `n` mod `Q` and the value of
`tailLarge P b n` are arithmetically independent, and the counting functions decouple.

*Why this is not Selberg–Delange.*  At the level of a finite divisibility pattern
`p_1 ∣ n+j_1, …, p_r ∣ n+j_r` with all `p_i > P`, the moduli are coprime to `Q` and the Chinese
remainder theorem gives the density `1/(Q·∏ p_i)` **exactly**.  The whole content is the
passage from patterns to the functional `tailLarge`, i.e. a fundamental-lemma truncation with
the primes up to `N` handled by a level-of-distribution argument, not the identification of any
law (which is what `ω mod b` — Selberg–Delange — or `ω(n), ω(n+1)` jointly — Chowla — would
require, and the rotation route deliberately avoids both). -/
theorem tailLargeDecouple_holds (b P Q : ℕ) (hb : 2 ≤ b) (hQ : 0 < Q)
    (hQP : ∀ p, p.Prime → p ∣ Q → p ≤ P) : TailLargeDecouple b P Q := by
  sorry

/-- The rotation route holds, given the two leaves. -/
theorem rotationRoute_holds (b : ℕ) (hb : 2 ≤ b) : RotationRoute b := by
  intro α len hα hlen hαlen
  obtain ⟨P, Q, M, a, hQ0, hM0, hQP, hPQ, hinj, hcov⟩ :=
    exists_rotationCover b hb α len hα hlen hαlen
  exact ⟨P, Q, M, a, hQ0, hM0, hQP, hinj, hcov, tailLargeDecouple_holds b P Q hb hQ0 hPQ⟩

end NormalNumbers.CastingOut
