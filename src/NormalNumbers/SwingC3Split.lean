/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Carry

/-!
# Small/large prime splitting of `ω`, and the transitivity route to `OmegaCarryJoint`

The crux `OmegaCarryJoint` (`SwingC3.lean`) asks that one residue class of the carry be
compatible, at positive lower density, with every prescribed residue vector for `ω`.  Attacking
it through equidistribution of `ω mod b` means Selberg–Delange.  There is a softer route, and
this file sets up its algebra.

Split `ω = ω_{≤P} + ω_{>P}` (`omegaSmall`, `omegaLarge`, `omegaSmall_add_omegaLarge`).  The
small part is **periodic**: `omegaSmall P m` depends only on `m` modulo the primes `≤ P`
(`omegaSmall_congr`).  So on an arithmetic progression `n ≡ a (mod Q)`, `Q = ∏_{p ≤ P} p`, the
whole vector `(ω_{≤P}(n+1), …, ω_{≤P}(n+L))` is a CONSTANT determined by `a`, and — choosing `a`
by CRT, with primes `> L` so no prime divides two window entries — that constant vector can be
made **any** vector of counts we like.

By `SwingC3Carry.omegaCarry_succ` the digit window is the base-`b` adder automaton run on
`ω = ω_{≤P} + ω_{>P}`, so moving `a` translates the digit window by an arbitrary amount while
leaving the `ω_{>P}` input alone.  Hence the digit-window law is a mixture, over `a`, of
*shifted copies of a single law*, and every word picks up positive density — **without ever
identifying that law**.  The one thing this needs is

    `OmegaLargeDecouple`: the joint law of `(ω_{>P}(n+1), …, ω_{>P}(n+L))` along
    `n ≡ a (mod Q)` is asymptotically independent of the class `a`,

which is the fundamental lemma of the sieve / Kubilius model territory, not Selberg–Delange.
That is the leaf the next lap should attack.
-/

open Finset

namespace NormalNumbers

open PrimeLambert

/-- `ω_{≤P}(m)`: the number of distinct prime factors of `m` that are `≤ P`. -/
def omegaSmall (P m : ℕ) : ℕ := (m.primeFactors.filter (fun p => p ≤ P)).card

/-- `ω_{>P}(m)`: the number of distinct prime factors of `m` that exceed `P`. -/
def omegaLarge (P m : ℕ) : ℕ := (m.primeFactors.filter (fun p => ¬ p ≤ P)).card

@[simp] theorem omegaSmall_add_omegaLarge (P m : ℕ) :
    omegaSmall P m + omegaLarge P m = ArithmeticFunction.cardDistinctFactors m := by
  rw [omegaSmall, omegaLarge, cardDistinctFactors_eq_card_primeFactors]
  exact Finset.card_filter_add_card_filter_not (fun p => p ≤ P)

/-- **Periodicity of the small part.**  If `m` and `m'` are divisible by exactly the same primes
`≤ P`, their small `ω`-counts agree. -/
theorem omegaSmall_congr {P m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (h : ∀ p ≤ P, p.Prime → (p ∣ m ↔ p ∣ m')) : omegaSmall P m = omegaSmall P m' := by
  unfold omegaSmall
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hpm, -⟩, hle⟩
    exact ⟨⟨hp, (h p hle hp).1 hpm, hm'⟩, hle⟩
  · rintro ⟨⟨hp, hpm, -⟩, hle⟩
    exact ⟨⟨hp, (h p hle hp).2 hpm, hm⟩, hle⟩

/-- The congruence hypothesis of `omegaSmall_congr` holds whenever `m ≡ m'` modulo a number `Q`
that every prime `≤ P` divides. -/
theorem omegaSmall_congr_of_modEq {P Q m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hQ : ∀ p ≤ P, p.Prime → p ∣ Q) (h : m ≡ m' [MOD Q]) :
    omegaSmall P m = omegaSmall P m' :=
  omegaSmall_congr hm hm' fun p hp hpp => by
    have hpQ := hQ p hp hpp
    have h' : m ≡ m' [MOD p] := Nat.ModEq.of_dvd hpQ h
    constructor
    · intro hd
      exact (Nat.modEq_zero_iff_dvd).1 (h'.symm.trans ((Nat.modEq_zero_iff_dvd).2 hd))
    · intro hd
      exact (Nat.modEq_zero_iff_dvd).1 (h'.trans ((Nat.modEq_zero_iff_dvd).2 hd))

/-- The digit window of `G_b` at `n` is driven by `ω_{≤P} + ω_{>P}`: restating
`SwingC3Carry.omegaCarry_succ` in the split form, which is where the translation by the
residue class enters. -/
theorem omegaCarry_succ_split {b : ℕ} (hb : 2 ≤ b) (P k : ℕ) :
    omegaCarry b k = (omegaSmall P (k + 1) + omegaLarge P (k + 1) + omegaCarry b (k + 1)) / b := by
  rw [omegaSmall_add_omegaLarge]; exact omegaCarry_succ hb k

/-! ### The tail splits, and the small half is a periodic ROTATION

This is the correct form of the route.  The digit window of `G_b` at `n` is determined by the
orbit point `T_b(n) mod 1`, and `T_b(n) = tailSmall P b n + tailLarge P b n` with `tailSmall`
**periodic modulo `Q`**.  So along `n ≡ a (mod Q)` the orbit point is the large-prime tail
*rotated by the constant* `tailSmall P b a`.  Choosing `ω_{≤P}(a+j) = k_j` for `j = 1, …, ℓ` by
CRT puts that constant at `∑_{j≤ℓ} k_j b^{−j} + (tail)`, and the head runs over EVERY multiple of
`b^{−ℓ}`.  Rotating any fixed law by all `b^ℓ` multiples of `b^{−ℓ}` gives every length-`ℓ`
cylinder positive mass — so every word occurs at positive density, whatever the law of
`tailLarge` is. -/

/-- The small-prime half of the tail. -/
noncomputable def tailSmall (P b n : ℕ) : ℝ :=
  ∑' i : ℕ, (omegaSmall P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

/-- The large-prime half of the tail. -/
noncomputable def tailLarge (P b n : ℕ) : ℝ :=
  ∑' i : ℕ, (omegaLarge P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

lemma summable_tailSmall {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) :
    Summable (fun i : ℕ => (omegaSmall P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (G4.summable_tailB hb n)
  have : (omegaSmall P (n + i + 1) : ℝ) ≤ omegaR (n + i + 1) := by
    rw [omegaR, cardDistinctFactors_eq_card_primeFactors]
    exact_mod_cast Finset.card_filter_le _ _
  gcongr

lemma summable_tailLarge {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) :
    Summable (fun i : ℕ => (omegaLarge P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (G4.summable_tailB hb n)
  have : (omegaLarge P (n + i + 1) : ℝ) ≤ omegaR (n + i + 1) := by
    rw [omegaR, cardDistinctFactors_eq_card_primeFactors]
    exact_mod_cast Finset.card_filter_le _ _
  gcongr

/-- **The tail splits.** -/
theorem tailB_eq_small_add_large {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) :
    G4.tailB b n = tailSmall P b n + tailLarge P b n := by
  rw [tailSmall, tailLarge, ← Summable.tsum_add (summable_tailSmall hb P n)
    (summable_tailLarge hb P n), G4.tailB]
  refine tsum_congr fun i => ?_
  have hsum := omegaSmall_add_omegaLarge P (n + i + 1)
  have : omegaR (n + i + 1)
      = (omegaSmall P (n + i + 1) : ℝ) + (omegaLarge P (n + i + 1) : ℝ) := by
    rw [omegaR, ← Nat.cast_add, hsum]
  rw [this, add_div]

/-- **The small half is `Q`-periodic**: it is a constant rotation along each class mod `Q`. -/
theorem tailSmall_congr {b P Q n n' : ℕ} (hQ : ∀ p ≤ P, p.Prime → p ∣ Q)
    (h : n ≡ n' [MOD Q]) : tailSmall P b n = tailSmall P b n' := by
  refine tsum_congr fun i => ?_
  congr 2
  exact omegaSmall_congr_of_modEq (by omega) (by omega) hQ (h.add_right (i + 1))

/-! ### CRT prescription: an explicit residue class realising any divisibility pattern

The rotation argument needs to place a prescribed number of small primes into each window slot.
Since every prime used is `> L`, it can divide at most one of `a+1, …, a+L`, so the slots are
independent and CRT solves them simultaneously. -/

/-- **CRT prescription.**  Given distinct primes all exceeding `L` and an assignment `f` sending
each to a window slot in `[1, L]`, there is a residue `a` for which the primes dividing `a + j`
are exactly those assigned to slot `j`. -/
theorem exists_crt_pattern (L : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hSL : ∀ p ∈ S, L < p) (f : ℕ → ℕ) (hf1 : ∀ p ∈ S, 1 ≤ f p) (hfL : ∀ p ∈ S, f p ≤ L) :
    ∃ a : ℕ, ∀ p ∈ S, ∀ j, 1 ≤ j → j ≤ L → (p ∣ a + j ↔ j = f p) := by
  classical
  have hs : ∀ p ∈ S, (id p : ℕ) ≠ 0 := fun p hp => (hS p hp).pos.ne'
  have pp : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime (id : ℕ → ℕ)) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (hS p hp) (hS q hq)).2 hne
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun p => p - f p) id S hs pp
  refine ⟨a, fun p hp j hj1 hjL => ?_⟩
  have hfp : f p ≤ p := le_trans (hfL p hp) (hSL p hp).le
  have hzero : p ∣ a + f p := by
    have h1 : a ≡ p - f p [MOD p] := ha p hp
    have h2 : a + f p ≡ (p - f p) + f p [MOD p] := h1.add_right _
    have h3 : (p - f p) + f p = p := by omega
    rw [h3] at h2
    have : a + f p ≡ 0 [MOD p] := h2.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
    exact Nat.modEq_zero_iff_dvd.1 this
  constructor
  · intro hdvd
    have e1 : a + j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 hdvd
    have e2 : a + f p ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 hzero
    have e3 : a + j ≡ a + f p [MOD p] := e1.trans e2.symm
    have e4 : j ≡ f p [MOD p] := Nat.ModEq.add_left_cancel' a e3
    have hjp : j < p := lt_of_le_of_lt hjL (hSL p hp)
    have hfpp : f p < p := lt_of_le_of_lt (hfL p hp) (hSL p hp)
    unfold Nat.ModEq at e4
    rwa [Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt hfpp] at e4
  · rintro rfl
    exact hzero

/-! ### The orbit IS the tail, mod one

`orbit b G_b n = fract (T_b n)`, so combining with `tailB_eq_small_add_large` the orbit point
along `n ≡ a (mod Q)` is literally `fract (θ(a) + tailLarge P b n)` with `θ(a) = tailSmall P b a`
a constant.  This is the exact sense in which the small primes act by rotation. -/

open PrimeLambert in
/-- The orbit point of `G_b` at `n` is the fractional part of the tail. -/
theorem orbit_eq_fract_tailB {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    orbit b (primeLambertAtBase b) n = Int.fract (G4.tailB b n) := by
  rw [G4.tailB_eq hb n, orbit, mul_comm]
  exact (Int.fract_sub_natCast _ _).symm

open PrimeLambert in
/-- **The rotation form of the orbit.**  Along the class `n ≡ a (mod Q)` the orbit point is the
large-prime tail rotated by the constant `tailSmall P b a`. -/
theorem orbit_eq_rotation {b : ℕ} (hb : 2 ≤ b) {P Q : ℕ} (hQ : ∀ p ≤ P, p.Prime → p ∣ Q)
    {a n : ℕ} (h : n ≡ a [MOD Q]) :
    orbit b (primeLambertAtBase b) n = Int.fract (tailSmall P b a + tailLarge P b n) := by
  rw [orbit_eq_fract_tailB hb n, tailB_eq_small_add_large hb P n,
    tailSmall_congr (b := b) hQ h]

/-! ### The partition engine: rotating a cylinder by all `k/M` tiles the circle

This is the combinatorial heart of the rotation route.  Whatever the law of the large-prime
tail, rotating a fixed cylinder of length `1/M` by the `M` shifts `k/M` sweeps every point of
the circle exactly once — so summing the rotated masses gives the total mass `1`, and every
cylinder inherits positive density. -/

/-- A shifted fractional part lands in the cylinder `[w/M, (w+1)/M)` exactly when the shift
matches the residue. -/
theorem fract_add_mem_cylinder_iff {M : ℕ} (hM : 0 < M) (w k : ℕ) (hw : w < M)
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    Int.fract (y + (k : ℝ) / M) ∈ Set.Ico ((w : ℝ) / M) (((w : ℝ) + 1) / M)
      ↔ ((⌊y * M⌋).toNat + k) % M = w := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set m : ℕ := (⌊y * M⌋).toNat with hmdef
  have hfl : (⌊y * (M : ℝ)⌋) = (m : ℤ) := by
    rw [hmdef, Int.toNat_of_nonneg (Int.floor_nonneg.2 (by positivity))]
  set z : ℝ := y + (k : ℝ) / M with hz
  have hzM : z * M = y * M + k := by rw [hz]; field_simp
  -- `⌊z⌋` is the integer quotient of `m + k` by `M`
  have hfz : (⌊z⌋ : ℤ) = ((m + k : ℕ) : ℤ) / (M : ℤ) := by
    have : z = (y * M + k) / M := by rw [← hzM]; field_simp
    rw [this, Int.floor_div_natCast]
    congr 1
    rw [Int.floor_add_natCast, hfl]
    push_cast; ring
  -- the scaled fractional part has floor `(m + k) % M`
  have hfloor : ⌊(M : ℝ) * Int.fract z⌋ = ((m + k : ℕ) : ℤ) % (M : ℤ) := by
    rw [Int.fract, mul_sub, mul_comm (M : ℝ) z, hzM]
    rw [show (y * M + k) - (M : ℝ) * (⌊z⌋ : ℤ) = (y * M) + ((k : ℤ) - (M : ℤ) * ⌊z⌋ : ℤ) by
      push_cast; ring]
    rw [Int.floor_add_intCast, hfl, hfz, Int.emod_def]
    push_cast; ring
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hM0] at h1
    rw [lt_div_iff₀ hM0] at h2
    have hfe : ⌊(M : ℝ) * Int.fract z⌋ = (w : ℤ) := by
      rw [Int.floor_eq_iff]
      rw [mul_comm]
      push_cast
      exact ⟨h1, h2⟩
    rw [hfloor] at hfe
    rw [← Int.natCast_mod] at hfe
    exact_mod_cast hfe
  · intro h
    have hfe : ⌊(M : ℝ) * Int.fract z⌋ = (w : ℤ) := by
      rw [hfloor, ← Int.natCast_mod, h]
    rw [Int.floor_eq_iff] at hfe
    obtain ⟨h1, h2⟩ := hfe
    rw [mul_comm] at h1 h2
    push_cast at h1 h2
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hM0]; linarith
    · rw [lt_div_iff₀ hM0]; linarith

/-- **Every point is swept.**  For `y ∈ [0,1)` some shift `k < M` puts `y + k/M` into the
cylinder `[w/M, (w+1)/M)`.  Covering is all the route needs — the rotated masses then sum to at
least the measure of the whole circle, so every cylinder gets positive mass whatever the law. -/
theorem exists_shift_mem_cylinder {M : ℕ} (hM : 0 < M) (w : ℕ) (hw : w < M)
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    ∃ k < M, Int.fract (y + (k : ℝ) / M)
      ∈ Set.Ico ((w : ℝ) / M) (((w : ℝ) + 1) / M) := by
  set m : ℕ := (⌊y * M⌋).toNat with hmdef
  have hs : m % M < M := Nat.mod_lt _ hM
  have hmod : ∀ k : ℕ, (m + k) % M = (m % M + k) % M := fun k => by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.mod_mod_of_dvd _ dvd_rfl]
  rcases le_or_gt (m % M) w with hle | hgt
  · refine ⟨w - m % M, by omega, ?_⟩
    rw [fract_add_mem_cylinder_iff hM w _ hw hy hy1, hmod]
    rw [show m % M + (w - m % M) = w from by omega, Nat.mod_eq_of_lt hw]
  · refine ⟨w + M - m % M, by omega, ?_⟩
    rw [fract_add_mem_cylinder_iff hM w _ hw hy hy1, hmod]
    rw [show m % M + (w + M - m % M) = w + M from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hw]

end NormalNumbers
