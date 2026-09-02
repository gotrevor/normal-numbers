/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Furstenberg's ×p×q topological rigidity (1967), proved 🌀

A closed subset of the circle carried into itself by two multiplicatively
independent multiplication maps is finite or everything; hence the
`⟨p, q⟩`-orbit of every non-torsion point is dense
(`dense_orbit_of_not_isOfFinAddOrder`).  The ledger node
`Literature.furstenberg_dense_orbit` (the `Int.fract` form for `p = 2`,
`q = 3` and irrational `x`) is wired from it in `LiteratureFurstenberg.lean`.

**Provenance.**  Furstenberg, *Disjointness in ergodic theory, minimal sets, and
a problem in Diophantine approximation* (1967), Theorem IV.1.  The proof
follows the elementary route of Boshernitzan (*Elementary proof of Furstenberg's
Diophantine result*, Proc. AMS 122 (1994) 67-70) as presented in Manners,
*A solution to the pyjama problem* (arXiv:1305.1514), §4.  Everything is
elementary: no measure theory, no entropy, no disjointness.

**Source.**  This file is a verbatim re-homing (namespace + two lint fixes) of
`CollatzMoonshot/Rigidity/Furstenberg.lean` from the sibling repo
`collatz-moonshot` (same author, commit `4727694`, identical mathlib pin
`0df444a3` / Lean `v4.33.1`), where it discharged an axiom of the Collatz
project.  It is re-checked by this repo's kernel; every theorem audits
`[propext, Classical.choice, Quot.sound]`.

**Architecture** (Manners §4):
1. arithmetic: multiplicative independence, irrationality of `log p / log q`;
2. rotation: an irrational rotation has small nonzero ℕ-multiples, and a small
   step walks δ-densely around the circle;
3. the climb (Furstenberg's Lemma IV.1 / Manners' Lemma 4.2): the ⟨p,q⟩-orbit
   of a small positive real is δ-dense mod 1, via density of the additive
   semigroup `{r log p + s log q}` in a tail of the half-line;
4. small-points corollary (Manners' Corollary 4.3): a closed invariant set
   accumulating at `0` is everything; likewise at a torsion point (translate
   trick);
5. the intersection induction (Manners' proof of Theorem 4.1): if the derived
   set is torsion-free, intersect its translates along a δ-dense grid of
   torsion points fixed by a sub-semigroup `⟨p^m, q^m⟩`; each stage is infinite,
   so its difference set is compact, invariant, accumulates at `0`, hence is
   everything, which hands the next stage its witness.

The two multiplication maps are `(p • ·)` and `(q • ·)` (ℕ-scalar action on
`UnitAddCircle`).
-/

namespace NormalNumbers
namespace Furstenberg

open Set Filter Topology

/-! ## §1  Multiplicative independence arithmetic -/

/-- Two naturals are multiplicatively independent: no nontrivial power of one
equals a power of the other. -/
def MultIndep (p q : ℕ) : Prop := ∀ a b : ℕ, p ^ a = q ^ b → a = 0 ∧ b = 0

theorem multIndep_two_three : MultIndep 2 3 := by
  intro a b h
  have hb : b = 0 := by
    by_contra hb
    have h3 : (3 : ℕ) ∣ 2 ^ a := h ▸ dvd_pow_self 3 hb
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  subst hb
  simp only [pow_zero] at h
  rcases Nat.pow_eq_one.mp h with h2 | ha
  · omega
  · exact ⟨ha, rfl⟩

theorem MultIndep.pow {p q : ℕ} (h : MultIndep p q) {m : ℕ} (hm : 0 < m) :
    MultIndep (p ^ m) (q ^ m) := by
  intro a b hab
  rw [← pow_mul, ← pow_mul] at hab
  obtain ⟨ha, hb⟩ := h _ _ hab
  exact ⟨(Nat.mul_eq_zero.mp ha).resolve_left (by omega),
    (Nat.mul_eq_zero.mp hb).resolve_left (by omega)⟩

/-- `p^a = 1` forces `a = 0` when `2 ≤ p`. -/
private theorem pow_eq_one_forces {p a : ℕ} (hp : 2 ≤ p) (h : p ^ a = 1) : a = 0 := by
  rcases Nat.pow_eq_one.mp h with h2 | ha
  · omega
  · exact ha

/-- Multiplicative independence forces distinct semigroup elements to be
distinct as naturals: `p^r * q^s` determines `(r, s)`. -/
theorem MultIndep.pow_mul_pow_injective {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : MultIndep p q) {r s r' s' : ℕ}
    (hrs : p ^ r * q ^ s = p ^ r' * q ^ s') : r = r' ∧ s = s' := by
  have key : ∀ {r s r' s' : ℕ}, r ≤ r' → p ^ r * q ^ s = p ^ r' * q ^ s' →
      r = r' ∧ s = s' := by
    intro r s r' s' hr hrs
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hr
    have hp0 : 0 < p ^ r := pow_pos (by omega) r
    rw [pow_add, mul_assoc] at hrs
    have h1 : q ^ s = p ^ c * q ^ s' := Nat.eq_of_mul_eq_mul_left hp0 hrs
    rcases le_total s' s with hs | hs
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hs
      have hq0 : 0 < q ^ s' := pow_pos (by omega) s'
      have h1' : q ^ e * q ^ s' = p ^ c * q ^ s' := by
        rw [← pow_add, add_comm e s']
        exact h1
      have h2 : q ^ e = p ^ c := Nat.eq_of_mul_eq_mul_right hq0 h1'
      obtain ⟨hc, he⟩ := h _ _ h2.symm
      omega
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hs
      have hq0 : 0 < q ^ s := pow_pos (by omega) s
      have h1' : q ^ s * 1 = q ^ s * (p ^ c * q ^ e) := by
        rw [mul_one]
        nth_rewrite 1 [h1]
        ring
      have h2 : 1 = p ^ c * q ^ e := Nat.eq_of_mul_eq_mul_left hq0 h1'
      have hc : c = 0 := pow_eq_one_forces hp (Nat.dvd_one.mp ⟨q ^ e, h2⟩)
      have he : e = 0 := pow_eq_one_forces hq (Nat.dvd_one.mp ⟨p ^ c, by rw [h2]; ring⟩)
      omega
  rcases le_total r r' with hr | hr
  · exact key hr hrs
  · obtain ⟨h1, h2⟩ := key hr hrs.symm
    omega

/-- Multiplicative independence of `p, q ≥ 2` makes `log p / log q` irrational.
This feeds the irrational-rotation machinery. -/
theorem MultIndep.irrational_log_div_log {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : MultIndep p q) : Irrational (Real.log p / Real.log q) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  rw [irrational_iff_ne_rational]
  rintro a b hb hab
  have hb' : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hcross : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    field_simp at hab
    linarith
  have hsign : 0 < (a : ℝ) / (b : ℝ) := hab ▸ div_pos hlp hlq
  -- `a` and `b` share a sign, so their absolute values satisfy the same relation.
  have habs : (b.natAbs : ℝ) * Real.log p = (a.natAbs : ℝ) * Real.log q := by
    rcases lt_or_gt_of_ne hb' with hbneg | hbpos
    · have haneg : (a : ℝ) < 0 := by
        rcases lt_trichotomy (a : ℝ) 0 with h' | h' | h'
        · exact h'
        · rw [h', zero_div] at hsign; exact absurd hsign (lt_irrefl 0)
        · exfalso
          have : (a : ℝ) / b < 0 := div_neg_of_pos_of_neg h' hbneg
          linarith
      have hbz : b < 0 := by exact_mod_cast hbneg
      have haz : a < 0 := by exact_mod_cast haneg
      have h1 : (b.natAbs : ℝ) = -(b : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((b.natAbs : ℤ)) = -b by omega, Int.cast_neg]
      have h2 : (a.natAbs : ℝ) = -(a : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((a.natAbs : ℤ)) = -a by omega, Int.cast_neg]
      rw [h1, h2]; linarith
    · have hapos : 0 < (a : ℝ) := by
        rcases lt_trichotomy (a : ℝ) 0 with h' | h' | h'
        · exfalso
          have : (a : ℝ) / b < 0 := div_neg_of_neg_of_pos h' hbpos
          linarith
        · rw [h', zero_div] at hsign; exact absurd hsign (lt_irrefl 0)
        · exact h'
      have hbz : 0 < b := by exact_mod_cast hbpos
      have haz : 0 < a := by exact_mod_cast hapos
      have h1 : (b.natAbs : ℝ) = (b : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((b.natAbs : ℤ)) = b by omega]
      have h2 : (a.natAbs : ℝ) = (a : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((a.natAbs : ℤ)) = a by omega]
      rw [h1, h2]; linarith
  have hpow : (p : ℝ) ^ b.natAbs = (q : ℝ) ^ a.natAbs := by
    have hlog : Real.log ((p : ℝ) ^ b.natAbs) = Real.log ((q : ℝ) ^ a.natAbs) := by
      rw [Real.log_pow, Real.log_pow]
      exact_mod_cast habs
    have hppos : (0 : ℝ) < (p : ℝ) ^ b.natAbs := pow_pos (by linarith) _
    have hqpos : (0 : ℝ) < (q : ℝ) ^ a.natAbs := pow_pos (by linarith) _
    exact Real.log_injOn_pos (mem_Ioi.mpr hppos) (mem_Ioi.mpr hqpos) hlog
  have hnat : p ^ b.natAbs = q ^ a.natAbs := by exact_mod_cast hpow
  exact Int.natAbs_ne_zero.mpr hb (h _ _ hnat).1

/-! ## §2  Rotation: small steps and the walk -/

/-- Distance between real coercions to the unit circle is at most the real
distance. -/
theorem dist_coe_le (a b : ℝ) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) ≤ |a - b| := by
  rw [dist_eq_norm]
  have hcast : (a : UnitAddCircle) - (b : UnitAddCircle) = ((a - b : ℝ) : UnitAddCircle) :=
    (QuotientAddGroup.mk_sub _ a b).symm
  rw [hcast, UnitAddCircle.norm_eq]
  simpa using round_le (a - b) 0

/-- Norm of a real coercion is bounded by the real absolute value. -/
theorem norm_coe_le (a : ℝ) : ‖(a : UnitAddCircle)‖ ≤ |a| := by
  simpa using dist_coe_le a 0

/-- An irrational rotation has arbitrarily small nonzero ℕ-multiples. -/
theorem exists_nsmul_norm_small {θ : ℝ} (hθ : Irrational θ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℕ, 0 < s ∧ (s • (θ : UnitAddCircle)) ≠ 0 ∧
      ‖s • (θ : UnitAddCircle)‖ < δ := by
  set τ : ℝ := min δ (1 / 2) with hτdef
  have hτpos : 0 < τ := lt_min hδ (by norm_num)
  have hτδ : τ ≤ δ := min_le_left _ _
  have hτle : τ ≤ 1 / 2 := min_le_right _ _
  have hdense : DenseRange (· • ((θ : ℝ) : UnitAddCircle) : ℤ → UnitAddCircle) := by
    have hirr : Irrational (θ / 1) := by simpa using hθ
    exact AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  set y : UnitAddCircle := ((τ / 2 : ℝ) : UnitAddCircle) with hydef
  have hynorm : ‖y‖ = τ / 2 := by
    rw [hydef, (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
      (by rw [abs_of_pos (by linarith), abs_one]; linarith)]
    exact abs_of_pos (by linarith)
  obtain ⟨w, hwmem, hwdist⟩ := Metric.mem_closure_iff.mp (hdense y) (τ / 4) (by linarith)
  obtain ⟨z, rfl⟩ := hwmem
  set w : UnitAddCircle := z • ((θ : ℝ) : UnitAddCircle) with hwdef
  have hband : |‖w‖ - τ / 2| < τ / 4 := by
    have hd : |‖w‖ - ‖y‖| ≤ ‖w - y‖ := abs_norm_sub_norm_le w y
    have hd' : ‖w - y‖ < τ / 4 := by
      rw [← dist_eq_norm, dist_comm]
      exact hwdist
    rw [hynorm] at hd
    linarith [lt_of_le_of_lt hd hd']
  have h2 : ‖w‖ < δ := by
    have := abs_lt.mp hband
    linarith
  have h3 : 0 < ‖w‖ := by
    have := abs_lt.mp hband
    linarith
  have hwne : w ≠ 0 := fun h0 => by rw [h0, norm_zero] at h3; exact lt_irrefl 0 h3
  have hz : z ≠ 0 := by
    rintro rfl
    exact hwne (zero_zsmul _)
  have hkey : z.natAbs • ((θ : ℝ) : UnitAddCircle) = w ∨
      z.natAbs • ((θ : ℝ) : UnitAddCircle) = -w := by
    rcases Int.natAbs_eq z with hz' | hz'
    · left
      rw [hwdef, ← natCast_zsmul, ← hz']
    · right
      have hww : w = -((z.natAbs : ℤ) • ((θ : ℝ) : UnitAddCircle)) := by
        rw [hwdef, ← neg_zsmul, ← hz']
      rw [hww, neg_neg, natCast_zsmul]
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_, ?_⟩
  · rcases hkey with hk | hk <;> rw [hk]
    · exact hwne
    · simpa using hwne
  · rcases hkey with hk | hk <;> rw [hk]
    · exact h2
    · rw [norm_neg]
      exact h2

/-- Integer coercions vanish on the unit circle. -/
theorem intCast_coe_eq_zero (z : ℤ) : (((z : ℝ)) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨z, by simp⟩

/-- The fractional part represents the same circle point. -/
theorem coe_fract (x : ℝ) : ((Int.fract x : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  have h : ((Int.fract x : ℝ) : UnitAddCircle) =
      (x : UnitAddCircle) - (((⌊x⌋ : ℝ)) : UnitAddCircle) :=
    QuotientAddGroup.mk_sub _ x (⌊x⌋ : ℝ)
  rw [h, intCast_coe_eq_zero, sub_zero]

/-- Walking upward: the ℕ-multiples of a small positive real step past every
target within one step. -/
theorem walk_up {u : ℝ} (hu0 : 0 < u) {δ : ℝ} (huδ : u < δ) (y : UnitAddCircle) :
    ∃ k : ℕ, dist y (k • ((u : ℝ) : UnitAddCircle)) < δ := by
  obtain ⟨v₀, rfl⟩ := QuotientAddGroup.mk_surjective y
  set v : ℝ := Int.fract v₀ with hvdef
  have hv0 : 0 ≤ v := Int.fract_nonneg v₀
  refine ⟨⌈v / u⌉₊, ?_⟩
  have h1 : v ≤ (⌈v / u⌉₊ : ℝ) * u := by
    calc v = (v / u) * u := (div_mul_cancel₀ v hu0.ne').symm
    _ ≤ (⌈v / u⌉₊ : ℝ) * u := mul_le_mul_of_nonneg_right (Nat.le_ceil (v / u)) hu0.le
  have h2 : (⌈v / u⌉₊ : ℝ) * u < v + u := by
    have h3 : (⌈v / u⌉₊ : ℝ) < v / u + 1 := Nat.ceil_lt_add_one (div_nonneg hv0 hu0.le)
    calc (⌈v / u⌉₊ : ℝ) * u < (v / u + 1) * u := mul_lt_mul_of_pos_right h3 hu0
    _ = v + u := by field_simp
  have hsmul : (⌈v / u⌉₊ : ℕ) • ((u : ℝ) : UnitAddCircle) =
      (((⌈v / u⌉₊ : ℝ) * u : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  rw [hsmul, ← coe_fract v₀, ← hvdef]
  calc dist ((v : ℝ) : UnitAddCircle) (((⌈v / u⌉₊ : ℝ) * u : ℝ) : UnitAddCircle)
      ≤ |v - (⌈v / u⌉₊ : ℝ) * u| := dist_coe_le _ _
    _ < δ := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith

/-- The ℕ-multiples of any nonzero circle point of norm `< δ` form a δ-net. -/
theorem walk_dense {t : UnitAddCircle} (ht : t ≠ 0) {δ : ℝ} (hn : ‖t‖ < δ)
    (y : UnitAddCircle) : ∃ k : ℕ, dist y (k • t) < δ := by
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg t) hn
  obtain ⟨u₀, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [← coe_fract u₀] at ht hn ⊢
  set u : ℝ := Int.fract u₀ with hudef
  have hu0 : 0 ≤ u := Int.fract_nonneg u₀
  have hu1 : u < 1 := Int.fract_lt_one u₀
  have hune : u ≠ 0 := by
    rintro h0
    apply ht
    rw [h0]
    norm_num
  rcases le_or_gt u (1 / 2) with hhalf | hhalf
  · -- positive representative: `‖t‖ = u`, walk up.
    have hnorm : ‖((u : ℝ) : UnitAddCircle)‖ = u := by
      rw [(AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
        (by rw [abs_of_nonneg hu0, abs_one]; linarith)]
      exact abs_of_nonneg hu0
    rw [hnorm] at hn
    exact walk_up (lt_of_le_of_ne hu0 (Ne.symm hune)) hn y
  · -- negative representative: `t = -coe(1-u)`, walk the mirror.
    set u' : ℝ := 1 - u with hu'def
    have hu'0 : 0 < u' := by simp [hu'def]; linarith
    have hneg : ((u : ℝ) : UnitAddCircle) = -((u' : ℝ) : UnitAddCircle) := by
      have hsum : ((u : ℝ) : UnitAddCircle) + ((u' : ℝ) : UnitAddCircle) = 0 := by
        rw [← QuotientAddGroup.mk_add]
        have : u + u' = (1 : ℝ) := by rw [hu'def]; ring
        rw [this]
        exact intCast_coe_eq_zero 1 |>.symm ▸ (by norm_num [intCast_coe_eq_zero])
      linear_combination (norm := abel_nf) hsum
    have hnorm : ‖((u : ℝ) : UnitAddCircle)‖ = u' := by
      rw [hneg, norm_neg,
        (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
          (by rw [abs_of_nonneg hu'0.le, abs_one, hu'def]; linarith)]
      exact abs_of_nonneg hu'0.le
    rw [hnorm] at hn
    obtain ⟨k, hk⟩ := walk_up hu'0 hn (-y)
    refine ⟨k, ?_⟩
    rw [hneg, smul_neg, ← dist_neg_neg y (-(k • ((u' : ℝ) : UnitAddCircle))), neg_neg]
    exact hk

/-- Finite-index rotation net: some finite prefix of the ℕ-multiples of an
irrational rotation is δ-dense on the circle. -/
theorem exists_rotation_net {θ : ℝ} (hθ : Irrational θ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ y : UnitAddCircle, ∃ s : ℕ, s ≤ N ∧
      dist y (s • ((θ : ℝ) : UnitAddCircle)) < δ := by
  have hpt : ∀ y : UnitAddCircle, ∃ s : ℕ,
      dist y (s • ((θ : ℝ) : UnitAddCircle)) < δ / 2 := by
    intro y
    obtain ⟨s₀, _, hne, hsmall⟩ := exists_nsmul_norm_small hθ (half_pos hδ)
    obtain ⟨k, hk⟩ := walk_dense hne hsmall y
    exact ⟨s₀ * k, by rwa [mul_nsmul]⟩
  choose f hf using hpt
  obtain ⟨F, hFfin, hFcov⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ (X := UnitAddCircle)).totallyBounded (δ / 2) (half_pos hδ)
  refine ⟨hFfin.toFinset.sup f, fun y => ?_⟩
  have hy : y ∈ ⋃ c ∈ F, Metric.ball c (δ / 2) := hFcov (mem_univ y)
  obtain ⟨c, hcF, hyc⟩ := mem_iUnion₂.mp hy
  refine ⟨f c, Finset.le_sup (hFfin.mem_toFinset.mpr hcF), ?_⟩
  calc dist y (f c • ((θ : ℝ) : UnitAddCircle))
      ≤ dist y c + dist c (f c • ((θ : ℝ) : UnitAddCircle)) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add (Metric.mem_ball.mp hyc) (hf c)
    _ = δ := by ring

/-! ## §3  The multiplicative climb -/

/-- Density of the additive semigroup `{r·log p + s·log q}` in a tail of the
half-line (the quantitative heart of non-lacunarity). -/
theorem log_lattice_tail_dense {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : MultIndep p q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, C ≤ x →
      ∃ r s : ℕ, |((r : ℝ) * Real.log p + (s : ℝ) * Real.log q) - x| < ε := by
  have hlq : (0 : ℝ) < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  set θ : ℝ := Real.log p / Real.log q with hθdef
  have hθirr : Irrational θ := h.irrational_log_div_log hp hq
  have hθpos : 0 < θ := div_pos hlp hlq
  set ε' : ℝ := min (ε / (2 * Real.log q)) (1 / 4) with hε'def
  have hε'pos : 0 < ε' := lt_min (by positivity) (by norm_num)
  obtain ⟨N, hN⟩ := exists_rotation_net hθirr hε'pos
  refine ⟨Real.log q * ((N : ℝ) * θ + 2), by positivity, fun x hx => ?_⟩
  set ξ : ℝ := x / Real.log q with hξdef
  have hξlarge : (N : ℝ) * θ + 2 ≤ ξ := by
    rw [hξdef, le_div_iff₀ hlq]
    calc ((N : ℝ) * θ + 2) * Real.log q = Real.log q * ((N : ℝ) * θ + 2) := by ring
    _ ≤ x := hx
  obtain ⟨r, hrN, hrdist⟩ := hN ((ξ : ℝ) : UnitAddCircle)
  -- Extract the integer `j` with `|r·θ + j - ξ| < ε'`.
  have hsmul : (r : ℕ) • ((θ : ℝ) : UnitAddCircle) = (((r : ℝ) * θ : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  rw [hsmul] at hrdist
  have hdist_norm : ‖((ξ - (r : ℝ) * θ : ℝ) : UnitAddCircle)‖ < ε' := by
    rw [QuotientAddGroup.mk_sub, ← dist_eq_norm]
    exact hrdist
  rw [UnitAddCircle.norm_eq] at hdist_norm
  set j : ℤ := round (ξ - (r : ℝ) * θ) with hjdef
  have hjapprox : |ξ - (r : ℝ) * θ - (j : ℝ)| < ε' := hdist_norm
  have hrθ : (r : ℝ) * θ ≤ (N : ℝ) * θ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hrN) hθpos.le
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
    have h1 : ξ - (r : ℝ) * θ ≥ 2 := by linarith
    have h2 := abs_lt.mp hjapprox
    have hε'le : ε' ≤ 1 / 4 := min_le_right _ _
    linarith
  set s : ℕ := j.toNat with hsdef
  have hsj : (s : ℝ) = (j : ℝ) := by
    have : (0 : ℤ) ≤ j := by exact_mod_cast (by linarith : (0 : ℝ) ≤ (j : ℝ))
    exact_mod_cast Int.toNat_of_nonneg this
  refine ⟨r, s, ?_⟩
  have hexpand : (r : ℝ) * Real.log p + (s : ℝ) * Real.log q - x =
      Real.log q * (((r : ℝ) * θ + (j : ℝ)) - ξ) := by
    rw [hsj, hθdef, hξdef]
    field_simp
  rw [hexpand, abs_mul, abs_of_pos hlq]
  have hε'le : ε' ≤ ε / (2 * Real.log q) := min_le_left _ _
  calc Real.log q * |(r : ℝ) * θ + (j : ℝ) - ξ|
      < Real.log q * ε' := by
        apply mul_lt_mul_of_pos_left _ hlq
        rw [show (r : ℝ) * θ + (j : ℝ) - ξ = -(ξ - (r : ℝ) * θ - (j : ℝ)) by ring, abs_neg]
        exact hjapprox
    _ ≤ Real.log q * (ε / (2 * Real.log q)) := mul_le_mul_of_nonneg_left hε'le hlq.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- One-sided exponential Lipschitz bound (true without any order hypothesis). -/
private theorem exp_sub_exp_le (a b : ℝ) :
    Real.exp a - Real.exp b ≤ (a - b) * Real.exp a := by
  have h1 : 1 - Real.exp (b - a) ≤ a - b := by
    have := Real.add_one_le_exp (b - a)
    linarith
  have h2 : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, show a + (b - a) = b by ring]
  rw [h2, mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos a).le

/-- The multiplicative climb (Furstenberg's Lemma IV.1 / Manners' Lemma 4.2):
below a threshold `η`, the ⟨p,q⟩-orbit of any positive real `u < η` lands
within `δ` of every point of `[δ, 1]`. -/
theorem climb {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : MultIndep p q)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ u : ℝ, 0 < u → u < η →
      ∀ v : ℝ, δ ≤ v → v ≤ 1 →
        ∃ r s : ℕ, |(p : ℝ) ^ r * (q : ℝ) ^ s * u - v| < δ := by
  set ε : ℝ := δ / 2 with hεdef
  have hε : 0 < ε := half_pos hδ
  have hεq : ε ≤ 1 / 4 := by rw [hεdef]; linarith
  obtain ⟨C, hCpos, hC⟩ := log_lattice_tail_dense hp hq h hε
  refine ⟨δ * Real.exp (-C), by positivity, fun u hu0 huη v hvδ hv1 => ?_⟩
  have hv0 : 0 < v := lt_of_lt_of_le hδ hvδ
  set x : ℝ := Real.log v - Real.log u with hxdef
  have hxlarge : C ≤ x := by
    have h1 : Real.log u < Real.log δ + (-C) := by
      calc Real.log u < Real.log (δ * Real.exp (-C)) := Real.log_lt_log hu0 huη
      _ = Real.log δ + (-C) := by rw [Real.log_mul (by positivity) (by positivity),
        Real.log_exp]
    have h2 : Real.log δ ≤ Real.log v := Real.log_le_log hδ hvδ
    rw [hxdef]
    linarith
  obtain ⟨r, s, hrs⟩ := hC x hxlarge
  refine ⟨r, s, ?_⟩
  set a : ℝ := Real.log ((p : ℝ) ^ r * (q : ℝ) ^ s * u) with hadef
  set b : ℝ := Real.log v with hbdef
  have hppos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by positivity) r
  have hqpos : (0 : ℝ) < (q : ℝ) ^ s := pow_pos (by positivity) s
  have haval : a = (r : ℝ) * Real.log p + (s : ℝ) * Real.log q + Real.log u := by
    rw [hadef, Real.log_mul (by positivity) hu0.ne', Real.log_mul hppos.ne' hqpos.ne',
      Real.log_pow, Real.log_pow]
  have hab : |a - b| < ε := by
    rw [haval, hbdef, show (r : ℝ) * Real.log p + (s : ℝ) * Real.log q + Real.log u -
      Real.log v = (r : ℝ) * Real.log p + (s : ℝ) * Real.log q - x by rw [hxdef]; ring]
    exact hrs
  -- Values stay below `exp ε ≤ 4/3`, so the exponential is `4/3`-Lipschitz here.
  have hble : b ≤ 0 := by
    rw [hbdef, ← Real.log_one]
    exact Real.log_le_log hv0 hv1
  have hexpb : Real.exp b = v := by rw [hbdef, Real.exp_log hv0]
  have hexpa : Real.exp a = (p : ℝ) ^ r * (q : ℝ) ^ s * u := by
    rw [hadef, Real.exp_log (by positivity)]
  have hmax : Real.exp (max a b) ≤ Real.exp ε := by
    apply Real.exp_le_exp.mpr
    rcases max_cases a b with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]
      have := abs_lt.mp hab
      linarith
    · rw [hm]
      linarith [hε.le]
  have hexpε : Real.exp ε ≤ 4 / 3 := by
    have h1 := Real.add_one_le_exp (-ε)
    have h2 : (3 / 4 : ℝ) ≤ Real.exp (-ε) := by linarith
    have h3 : Real.exp ε * Real.exp (-ε) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos ε, Real.exp_pos (-ε)]
  have hfinal : |Real.exp a - Real.exp b| ≤ |a - b| * (4 / 3) := by
    rcases le_total b a with hba | hba
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba))]
      calc Real.exp a - Real.exp b ≤ (a - b) * Real.exp a := exp_sub_exp_le a b
      _ ≤ |a - b| * (4 / 3) := by
        apply mul_le_mul (le_abs_self _) _ (Real.exp_pos a).le (abs_nonneg _)
        calc Real.exp a ≤ Real.exp (max a b) := Real.exp_le_exp.mpr (le_max_left a b)
        _ ≤ Real.exp ε := hmax
        _ ≤ 4 / 3 := hexpε
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hba)), neg_sub]
      calc Real.exp b - Real.exp a ≤ (b - a) * Real.exp b := exp_sub_exp_le b a
      _ ≤ |a - b| * (4 / 3) := by
        apply mul_le_mul _ _ (Real.exp_pos b).le (abs_nonneg _)
        · rw [abs_sub_comm]; exact le_abs_self _
        calc Real.exp b ≤ Real.exp (max a b) := Real.exp_le_exp.mpr (le_max_right a b)
        _ ≤ Real.exp ε := hmax
        _ ≤ 4 / 3 := hexpε
  rw [← hexpa, ← hexpb]
  calc |Real.exp a - Real.exp b| ≤ |a - b| * (4 / 3) := hfinal
  _ < ε * (4 / 3) := by
    apply mul_lt_mul_of_pos_right hab
    norm_num
  _ ≤ δ := by rw [hεdef]; linarith

/-! ## §4  Circle dynamics: invariance, small points, torsion, the grid -/

variable {p q : ℕ} {Y : Set UnitAddCircle}

/-- Invariance under one generator extends to its powers. -/
theorem mapsTo_pow_smul (hP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Y Y)
    (r : ℕ) : MapsTo ((p ^ r) • · : UnitAddCircle → UnitAddCircle) Y Y := by
  induction r with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    show (p ^ (n + 1)) • x ∈ Y
    rw [pow_succ, mul_nsmul]
    exact hP (ih hx)

/-- Invariance under both generators extends to the whole semigroup. -/
theorem mapsTo_sigma_smul (hP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Y Y)
    (hQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) Y Y) (r s : ℕ) :
    MapsTo ((p ^ r * q ^ s) • · : UnitAddCircle → UnitAddCircle) Y Y := by
  intro x hx
  show (p ^ r * q ^ s) • x ∈ Y
  rw [mul_nsmul]
  exact mapsTo_pow_smul hQ s (mapsTo_pow_smul hP r hx)

/-- A closed invariant set containing positive representatives arbitrarily
close to `0` is dense (Manners' Corollary 4.3, the one-sided version). -/
theorem dense_of_small_pos_mem (hp : 2 ≤ p) (hq : 2 ≤ q) (h : MultIndep p q)
    (hP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Y Y)
    (hQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) Y Y)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ u : ℝ, 0 < u ∧ u < η ∧ ((u : ℝ) : UnitAddCircle) ∈ Y) :
    Dense Y := by
  rw [Metric.dense_iff]
  intro y ε hε
  set δ : ℝ := min (ε / 3) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨η, hη0, hclimb⟩ := climb hp hq h hδ0 hδhalf
  obtain ⟨u, hu0, huη, huY⟩ := hsmall η hη0
  -- Find a real target `v ∈ [δ, 1]` within `δ` of `y`.
  obtain ⟨v₀, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [← coe_fract v₀]
  set w : ℝ := Int.fract v₀ with hwdef
  have hw0 : 0 ≤ w := Int.fract_nonneg v₀
  have hw1 : w < 1 := Int.fract_lt_one v₀
  obtain ⟨v, hvδ, hv1, hvdist⟩ : ∃ v : ℝ, δ ≤ v ∧ v ≤ 1 ∧
      dist ((w : ℝ) : UnitAddCircle) ((v : ℝ) : UnitAddCircle) < δ := by
    rcases le_or_gt δ w with hcase | hcase
    · exact ⟨w, hcase, hw1.le, by simpa using hδ0⟩
    · refine ⟨1, by linarith, le_refl 1, ?_⟩
      have h1 : dist ((w : ℝ) : UnitAddCircle) ((1 : ℝ) : UnitAddCircle) ≤ |w - 1| :=
        dist_coe_le w 1
      have h2 : |w - 1| = 1 - w := by rw [abs_of_nonpos (by linarith)]; ring
      -- `1 - w > 1 - δ ≥ 1/2 ≥ δ` fails; instead use the wraparound distance.
      have h3 : ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
        rw [QuotientAddGroup.mk_zero]
        exact_mod_cast intCast_coe_eq_zero 1
      rw [h3]
      have h4 : dist ((w : ℝ) : UnitAddCircle) ((0 : ℝ) : UnitAddCircle) ≤ |w - 0| :=
        dist_coe_le w 0
      simp only [sub_zero] at h4
      calc dist ((w : ℝ) : UnitAddCircle) ((0 : ℝ) : UnitAddCircle)
          ≤ |w| := h4
        _ = w := abs_of_nonneg hw0
        _ < δ := hcase
  obtain ⟨r, s, hrs⟩ := hclimb u hu0 huη v hvδ hv1
  set σ : ℕ := p ^ r * q ^ s with hσdef
  have hσreal : ((σ : ℕ) : ℝ) = (p : ℝ) ^ r * (q : ℝ) ^ s := by
    rw [hσdef]
    push_cast
    ring
  have hmem : (σ • ((u : ℝ) : UnitAddCircle)) ∈ Y := mapsTo_sigma_smul hP hQ r s huY
  have hcoe : σ • ((u : ℝ) : UnitAddCircle) = (((σ : ℝ) * u : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  refine ⟨σ • ((u : ℝ) : UnitAddCircle), Metric.mem_ball.mpr ?_, hmem⟩
  rw [dist_comm]
  calc dist ((w : ℝ) : UnitAddCircle) (σ • ((u : ℝ) : UnitAddCircle))
      ≤ dist ((w : ℝ) : UnitAddCircle) ((v : ℝ) : UnitAddCircle) +
        dist ((v : ℝ) : UnitAddCircle) (σ • ((u : ℝ) : UnitAddCircle)) := dist_triangle _ _ _
    _ < δ + δ := by
        apply add_lt_add hvdist
        rw [hcoe]
        calc dist ((v : ℝ) : UnitAddCircle) (((σ : ℝ) * u : ℝ) : UnitAddCircle)
            ≤ |v - (σ : ℝ) * u| := dist_coe_le _ _
          _ < δ := by
              rw [abs_sub_comm, hσreal]
              exact hrs
    _ ≤ ε := by linarith [hδε]

/-- The `n`-torsion of the circle is finite. -/
theorem torsion_finite {n : ℕ} (hn : 0 < n) :
    {x : UnitAddCircle | n • x = 0}.Finite := by
  have himg : {x : UnitAddCircle | n • x = 0} ⊆
      (fun k : Fin n => ((((k : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle)) '' univ := by
    intro x hx
    obtain ⟨u₀, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← coe_fract u₀] at hx ⊢
    set u : ℝ := Int.fract u₀ with hudef
    have hu0 : 0 ≤ u := Int.fract_nonneg u₀
    have hu1 : u < 1 := Int.fract_lt_one u₀
    have hcoe : (n : ℕ) • ((u : ℝ) : UnitAddCircle) = (((n : ℝ) * u : ℝ) : UnitAddCircle) := by
      rw [← AddCircle.coe_nsmul]
      norm_num [nsmul_eq_mul]
    have hx' : (n : ℕ) • ((u : ℝ) : UnitAddCircle) = 0 := hx
    rw [hcoe, AddCircle.coe_eq_zero_iff] at hx'
    obtain ⟨z, hz⟩ := hx'
    have hz' : (z : ℝ) = (n : ℝ) * u := by
      have := hz
      simpa using this
    have hz0 : 0 ≤ z := by
      have : (0 : ℝ) ≤ (z : ℝ) := by rw [hz']; positivity
      exact_mod_cast this
    have hzn : z < n := by
      have hr : (z : ℝ) < (n : ℝ) := by
        rw [hz']
        have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        nlinarith
      exact_mod_cast hr
    refine ⟨⟨z.toNat, ?_⟩, mem_univ _, ?_⟩
    · omega
    · have hzt : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz0
      have : (((z.toNat : ℕ) : ℝ) / (n : ℝ)) = u := by
        rw [hzt, hz']
        field_simp
      simp only [this]
  exact (finite_range _).subset (himg.trans (image_subset_range _ _))

/-- Accumulation points push forward through multiplication maps that preserve
the set (the kernel is finite, so genuinely new points keep arriving). -/
theorem accPt_smul {n : ℕ} (hn : 0 < n)
    (hmaps : MapsTo (n • · : UnitAddCircle → UnitAddCircle) Y Y)
    {x : UnitAddCircle} (hx : AccPt x (𝓟 Y)) : AccPt (n • x) (𝓟 Y) := by
  rw [accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt] at hx ⊢
  set G : Set UnitAddCircle := {y | n • y = n • x} with hGdef
  have hGfin : G.Finite := by
    have himg : G ⊆ (fun z => z + x) '' {z : UnitAddCircle | n • z = 0} := by
      intro y hy
      refine ⟨y - x, ?_, by abel_nf⟩
      have : n • (y - x) = n • y - n • x := smul_sub n y x
      rw [Set.mem_ofPred_eq, this, hy, sub_self]
    exact ((torsion_finite hn).image _).subset himg
  have hstep1 : x ∈ closure (Y \ G) := by
    have hsplit : (Y \ {x}) ⊆ (Y \ G) ∪ (G \ {x}) := by
      intro y ⟨hyY, hyx⟩
      by_cases hyG : y ∈ G
      · exact Or.inr ⟨hyG, hyx⟩
      · exact Or.inl ⟨hyY, hyG⟩
    have h1 := closure_mono hsplit hx
    rw [closure_union, (hGfin.subset sdiff_subset).isClosed.closure_eq] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 (by simp)
  have hcont : Continuous (fun y : UnitAddCircle => n • y) := continuous_nsmul n
  have h2 : (n • x) ∈ closure ((fun y : UnitAddCircle => n • y) '' (Y \ G)) := by
    apply image_closure_subset_closure_image hcont
    exact ⟨x, hstep1, rfl⟩
  refine closure_mono ?_ h2
  rintro _ ⟨y, ⟨hyY, hyG⟩, rfl⟩
  exact ⟨hmaps hyY, fun heq => hyG heq⟩

/-- An invariant set containing a non-torsion point is infinite. -/
theorem infinite_of_mem_not_torsion (hp : 2 ≤ p)
    (hP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Y Y)
    {x : UnitAddCircle} (hx : x ∈ Y) (hnt : ¬ IsOfFinAddOrder x) : Y.Infinite := by
  have hinj : Function.Injective (fun r : ℕ => (p ^ r) • x) := by
    intro r r' hrr
    by_contra hne
    -- WLOG r < r'; then a positive multiple of x vanishes.
    wlog hlt : r < r' generalizing r r'
    · exact this hrr.symm (Ne.symm hne) (by omega)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
    have hple : p ^ r < p ^ r' := Nat.pow_lt_pow_right (by omega) hlt
    obtain ⟨e, he, hepos⟩ : ∃ e : ℕ, p ^ r' = p ^ r + e ∧ 0 < e :=
      ⟨p ^ r' - p ^ r, by omega, by omega⟩
    have : (p ^ r) • x = (p ^ r) • x + e • x := by
      calc (p ^ r) • x = (p ^ r') • x := hrr
      _ = (p ^ r + e) • x := by rw [he]
      _ = (p ^ r) • x + e • x := add_nsmul x _ _
    have hzero : e • x = 0 := by
      have := this.symm
      rwa [add_eq_left] at this
    exact hnt (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨e, hepos, hzero⟩)
  exact Set.infinite_of_injective_forall_mem hinj
    (fun r => mapsTo_pow_smul hP r hx)

/-- The difference set of an infinite closed set accumulates at `0`. -/
theorem accPt_zero_diff (hinf : Y.Infinite) :
    AccPt (0 : UnitAddCircle) (𝓟 (image2 (· - ·) Y Y)) := by
  obtain ⟨z, hz⟩ := hinf.exists_accPt_principal
  rw [accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt] at hz ⊢
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- two distinct points of `Y` within `ε/2` of `z`
  obtain ⟨y₁, hy₁, hy₁d⟩ := Metric.mem_closure_iff.mp hz (ε / 2) (by linarith)
  have hd₁ : 0 < dist z y₁ := by
    rcases eq_or_ne z y₁ with rfl | hne
    · exact absurd rfl hy₁.2
    · exact dist_pos.mpr hne
  obtain ⟨y₂, hy₂, hy₂d⟩ := Metric.mem_closure_iff.mp hz (min (ε / 2) (dist z y₁))
    (lt_min (by linarith) hd₁)
  have hy₂ε : dist z y₂ < ε / 2 := lt_of_lt_of_le hy₂d (min_le_left _ _)
  have hne : y₁ ≠ y₂ := by
    rintro rfl
    exact absurd (lt_of_lt_of_le hy₂d (min_le_right _ _)) (lt_irrefl _)
  refine ⟨y₁ - y₂, ?_, ?_⟩
  · constructor
    · exact mem_image2_of_mem hy₁.1 hy₂.1
    · simp only [mem_singleton_iff, sub_eq_zero]
      exact hne
  · rw [dist_zero_left]
    calc ‖y₁ - y₂‖ = dist y₁ y₂ := (dist_eq_norm y₁ y₂).symm
    _ ≤ dist y₁ z + dist z y₂ := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add _ hy₂ε
        rw [dist_comm]
        exact hy₁d
    _ = ε := by ring

/-- Representative dichotomy: a nonzero circle point of norm `< ρ` (with
`ρ ≤ 1/2`) has a positive real representative in `(0, ρ)`, either for itself or
for its negation. -/
theorem small_rep_dichotomy {t : UnitAddCircle} (ht : t ≠ 0) {ρ : ℝ}
    (_hρ : ρ ≤ 1 / 2) (hn : ‖t‖ < ρ) :
    (∃ u : ℝ, 0 < u ∧ u < ρ ∧ ((u : ℝ) : UnitAddCircle) = t) ∨
    (∃ u : ℝ, 0 < u ∧ u < ρ ∧ ((u : ℝ) : UnitAddCircle) = -t) := by
  obtain ⟨u₀, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [← coe_fract u₀] at ht hn ⊢
  set u : ℝ := Int.fract u₀ with hudef
  have hu0 : 0 ≤ u := Int.fract_nonneg u₀
  have hu1 : u < 1 := Int.fract_lt_one u₀
  have hune : u ≠ 0 := by
    rintro h0
    apply ht
    rw [h0]
    norm_num
  rcases le_or_gt u (1 / 2) with hhalf | hhalf
  · left
    have hnorm : ‖((u : ℝ) : UnitAddCircle)‖ = u := by
      rw [(AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
        (by rw [abs_of_nonneg hu0, abs_one]; linarith)]
      exact abs_of_nonneg hu0
    rw [hnorm] at hn
    exact ⟨u, lt_of_le_of_ne hu0 (Ne.symm hune), hn, rfl⟩
  · right
    set u' : ℝ := 1 - u with hu'def
    have hu'0 : 0 < u' := by rw [hu'def]; linarith
    have hneg : ((u : ℝ) : UnitAddCircle) = -((u' : ℝ) : UnitAddCircle) := by
      have hsum : ((u : ℝ) : UnitAddCircle) + ((u' : ℝ) : UnitAddCircle) = 0 := by
        rw [← QuotientAddGroup.mk_add]
        have huu : u + u' = (1 : ℝ) := by rw [hu'def]; ring
        rw [huu]
        exact_mod_cast intCast_coe_eq_zero 1
      linear_combination (norm := abel_nf) hsum
    have hnorm : ‖((u : ℝ) : UnitAddCircle)‖ = u' := by
      rw [hneg, norm_neg,
        (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
          (by rw [abs_of_nonneg hu'0.le, abs_one, hu'def]; linarith)]
      exact abs_of_nonneg hu'0.le
    rw [hnorm] at hn
    refine ⟨u', hu'0, hn, ?_⟩
    rw [hneg, neg_neg]

/-- Manners' Corollary 4.3, two-sided: a closed ⟨p,q⟩-invariant set accumulating
at `0` is everything. -/
theorem eq_univ_of_accPt_zero (hp : 2 ≤ p) (hq : 2 ≤ q) (h : MultIndep p q)
    (hcl : IsClosed Y)
    (hP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Y Y)
    (hQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) Y Y)
    (h0 : AccPt (0 : UnitAddCircle) (𝓟 Y)) : Y = univ := by
  by_cases hpos : ∀ η : ℝ, 0 < η → ∃ u : ℝ, 0 < u ∧ u < η ∧ ((u : ℝ) : UnitAddCircle) ∈ Y
  · rw [← hcl.closure_eq, (dense_of_small_pos_mem hp hq h hP hQ hpos).closure_eq]
  · push Not at hpos
    obtain ⟨η₀, hη₀, hbad⟩ := hpos
    set Z : Set UnitAddCircle := (fun x => -x) ⁻¹' Y with hZdef
    have hZcl : IsClosed Z := hcl.preimage continuous_neg
    have hZP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Z Z := by
      intro x hx
      show p • x ∈ Z
      simp only [hZdef, mem_preimage] at hx ⊢
      rw [← smul_neg]
      exact hP hx
    have hZQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) Z Z := by
      intro x hx
      show q • x ∈ Z
      simp only [hZdef, mem_preimage] at hx ⊢
      rw [← smul_neg]
      exact hQ hx
    have hZsmall : ∀ η : ℝ, 0 < η → ∃ u : ℝ, 0 < u ∧ u < η ∧
        ((u : ℝ) : UnitAddCircle) ∈ Z := by
      intro η hη
      set ρ : ℝ := min (min η η₀) (1 / 2) with hρdef
      have hρ0 : 0 < ρ := lt_min (lt_min hη hη₀) (by norm_num)
      have hρhalf : ρ ≤ 1 / 2 := min_le_right _ _
      have hρη : ρ ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
      have hρη₀ : ρ ≤ η₀ := le_trans (min_le_left _ _) (min_le_right _ _)
      obtain ⟨t, ht, htne⟩ := (accPt_iff_nhds.mp h0) (Metric.ball 0 ρ)
        (Metric.ball_mem_nhds 0 hρ0)
      have htY : t ∈ Y := ht.2
      have htnorm : ‖t‖ < ρ := by
        have := Metric.mem_ball.mp ht.1
        rwa [dist_zero_right] at this
      rcases small_rep_dichotomy htne hρhalf htnorm with ⟨u, hu0, huρ, hut⟩ | ⟨u, hu0, huρ, hut⟩
      · -- a positive representative of `t ∈ Y` this close to zero contradicts `hbad`
        exact absurd (hut ▸ htY) (hbad u hu0 (lt_of_lt_of_le huρ hρη₀))
      · -- `-t` provides the small member of `Z`
        refine ⟨u, hu0, lt_of_lt_of_le huρ hρη, ?_⟩
        simp only [hZdef, mem_preimage]
        rw [hut, neg_neg]
        exact htY
    have hZuniv : Z = univ := by
      rw [← hZcl.closure_eq, (dense_of_small_pos_mem hp hq h hZP hZQ hZsmall).closure_eq]
    ext x
    simp only [mem_univ, iff_true]
    have hxZ : -x ∈ Z := hZuniv ▸ mem_univ (-x)
    simpa [hZdef] using hxZ

/-! ## §5  The torsion translate trick and the grid -/

theorem MultIndep.pow' {p q : ℕ} (h : MultIndep p q) {e f : ℕ}
    (he : 0 < e) (hf : 0 < f) : MultIndep (p ^ e) (q ^ f) := by
  intro a b hab
  rw [← pow_mul, ← pow_mul] at hab
  obtain ⟨ha, hb⟩ := h _ _ hab
  exact ⟨(Nat.mul_eq_zero.mp ha).resolve_left (by omega),
    (Nat.mul_eq_zero.mp hb).resolve_left (by omega)⟩

/-- A torsion point's ⟨p,q⟩-orbit contains a point fixed by both `p^e•` and
`q^f•` for some positive `e, f` — by pigeonhole on the finite orbit and
commutativity of the two smuls.  No order arithmetic needed. -/
theorem exists_fixed_in_orbit {β : UnitAddCircle} (htor : IsOfFinAddOrder β)
    (p q : ℕ) (_hp : 2 ≤ p) (_hq : 2 ≤ q) :
    ∃ (e f r t : ℕ), 0 < e ∧ 0 < f ∧
      (p ^ e) • ((q ^ t) • ((p ^ r) • β)) = (q ^ t) • ((p ^ r) • β) ∧
      (q ^ f) • ((q ^ t) • ((p ^ r) • β)) = (q ^ t) • ((p ^ r) • β) := by
  -- Pigeonhole: `n ↦ n • β` takes finitely many values on a torsion point.
  have hfin : {x : UnitAddCircle | ∃ n : ℕ, n • β = x}.Finite := by
    have hord : 0 < addOrderOf β := htor.addOrderOf_pos
    have hsub : {x : UnitAddCircle | ∃ n : ℕ, n • β = x} ⊆
        (fun k : Fin (addOrderOf β) => (k : ℕ) • β) '' univ := by
      rintro x ⟨n, rfl⟩
      refine ⟨⟨n % addOrderOf β, Nat.mod_lt n hord⟩, mem_univ _, ?_⟩
      exact mod_addOrderOf_nsmul β n
    exact (finite_range _).subset (hsub.trans (image_subset_range _ _))
  -- direct pigeonhole for the `p`-powers acting on `β`
  have hpigeonP : ∃ r r' : ℕ, r < r' ∧ (p ^ r) • β = (p ^ r') • β := by
    have : ¬ Function.Injective (fun r : ℕ => (p ^ r) • β) := by
      intro hinj
      exact hfin.not_infinite (Set.infinite_of_injective_forall_mem hinj
        (fun r => ⟨p ^ r, rfl⟩))
    rw [Function.not_injective_iff] at this
    obtain ⟨r, r', heq, hne⟩ := this
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨r, r', hlt, heq⟩
    · exact ⟨r', r, hlt, heq.symm⟩
  obtain ⟨r, r', hrr, hreq⟩ := hpigeonP
  set e : ℕ := r' - r with hedef
  have he : 0 < e := by omega
  set β₁ : UnitAddCircle := (p ^ r) • β with hβ₁def
  have hβ₁fix : (p ^ e) • β₁ = β₁ := by
    rw [hβ₁def, ← mul_nsmul, ← pow_add]
    rw [show r + e = r' by omega]
    exact hreq.symm
  -- Repeat with `q`-powers on `β₁` (still torsion, orbit still finite).
  have hfin₁ : {x : UnitAddCircle | ∃ n : ℕ, n • β₁ = x}.Finite := by
    have hsub : {x : UnitAddCircle | ∃ n : ℕ, n • β₁ = x} ⊆
        {x : UnitAddCircle | ∃ n : ℕ, n • β = x} := by
      rintro x ⟨n, rfl⟩
      exact ⟨p ^ r * n, by rw [mul_nsmul]⟩
    exact hfin.subset hsub
  have hpigeonQ : ∃ t t' : ℕ, t < t' ∧ (q ^ t) • β₁ = (q ^ t') • β₁ := by
    have : ¬ Function.Injective (fun t : ℕ => (q ^ t) • β₁) := by
      intro hinj
      exact hfin₁.not_infinite (Set.infinite_of_injective_forall_mem hinj
        (fun t => ⟨q ^ t, rfl⟩))
    rw [Function.not_injective_iff] at this
    obtain ⟨t, t', heq, hne⟩ := this
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨t, t', hlt, heq⟩
    · exact ⟨t', t, hlt, heq.symm⟩
  obtain ⟨t, t', htt, hteq⟩ := hpigeonQ
  set f : ℕ := t' - t with hfdef
  have hf : 0 < f := by omega
  set β₂ : UnitAddCircle := (q ^ t) • β₁ with hβ₂def
  have hβ₂fixQ : (q ^ f) • β₂ = β₂ := by
    rw [hβ₂def, ← mul_nsmul, ← pow_add]
    rw [show t + f = t' by omega]
    exact hteq.symm
  have hβ₂fixP : (p ^ e) • β₂ = β₂ := by
    rw [hβ₂def, smul_comm ((p : ℕ) ^ e) ((q : ℕ) ^ t) β₁, hβ₁fix]
  exact ⟨e, f, r, t, he, hf, hβ₂fixP, hβ₂fixQ⟩

/-- A closed invariant set accumulating at a torsion point is everything
(the translate trick). -/
theorem eq_univ_of_accPt_torsion (hp : 2 ≤ p) (hq : 2 ≤ q) (h : MultIndep p q)
    (hcl : IsClosed Y)
    (hP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Y Y)
    (hQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) Y Y)
    {β : UnitAddCircle} (hβ : AccPt β (𝓟 Y)) (htor : IsOfFinAddOrder β) :
    Y = univ := by
  obtain ⟨e, f, r, t, he, hf, hfixP, hfixQ⟩ := exists_fixed_in_orbit htor p q hp hq
  set β₂ : UnitAddCircle := (q ^ t) • ((p ^ r) • β) with hβ₂def
  -- β₂ is still an accumulation point of Y.
  have hβ₂acc : AccPt β₂ (𝓟 Y) := by
    rw [hβ₂def]
    exact accPt_smul (pow_pos (by omega) t) (mapsTo_pow_smul hQ t)
      (accPt_smul (pow_pos (by omega) r) (mapsTo_pow_smul hP r) hβ)
  -- The translated set and the power pair.
  set P : ℕ := p ^ e with hPdef
  set Q : ℕ := q ^ f with hQdef
  have hP2 : 2 ≤ P := le_trans hp (Nat.le_self_pow (by omega) p)
  have hQ2 : 2 ≤ Q := le_trans hq (Nat.le_self_pow (by omega) q)
  have hPQind : MultIndep P Q := h.pow' he hf
  set T : Set UnitAddCircle := (· + β₂) ⁻¹' Y with hTdef
  have hTcl : IsClosed T := hcl.preimage (continuous_add_const β₂)
  have hTP : MapsTo (P • · : UnitAddCircle → UnitAddCircle) T T := by
    intro x hx
    show P • x ∈ T
    simp only [hTdef, mem_preimage] at hx ⊢
    have : P • x + β₂ = P • (x + β₂) := by
      rw [smul_add, hPdef, hfixP]
    rw [this]
    exact mapsTo_pow_smul hP e hx
  have hTQ : MapsTo (Q • · : UnitAddCircle → UnitAddCircle) T T := by
    intro x hx
    show Q • x ∈ T
    simp only [hTdef, mem_preimage] at hx ⊢
    have : Q • x + β₂ = Q • (x + β₂) := by
      rw [smul_add, hQdef, hfixQ]
    rw [this]
    exact mapsTo_pow_smul hQ f hx
  have hT0 : AccPt (0 : UnitAddCircle) (𝓟 T) := by
    rw [accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt] at hβ₂acc ⊢
    have hcont : Continuous (fun x : UnitAddCircle => x - β₂) :=
      continuous_sub_right β₂
    have h0 : (0 : UnitAddCircle) ∈ closure ((fun x => x - β₂) '' (Y \ {β₂})) := by
      apply image_closure_subset_closure_image hcont
      exact ⟨β₂, hβ₂acc, sub_self β₂⟩
    refine closure_mono ?_ h0
    rintro _ ⟨y, ⟨hyY, hyne⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [hTdef, mem_preimage, sub_add_cancel]
      exact hyY
    · simp only [mem_singleton_iff, sub_eq_zero]
      simpa using hyne
  have hTuniv : T = univ := eq_univ_of_accPt_zero hP2 hQ2 hPQind hTcl hTP hTQ hT0
  ext y
  simp only [mem_univ, iff_true]
  have : (y - β₂) ∈ T := hTuniv ▸ mem_univ _
  simpa [hTdef] using this

/-- Grids with denominator coprime to both generators exist at every scale. -/
theorem exists_grid (hp : 2 ≤ p) (hq : 2 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, 1 < d ∧ (1 : ℝ) / d < δ ∧ Nat.Coprime p d ∧ Nat.Coprime q d := by
  set L : ℕ := max 1 ⌈1 / δ⌉₊ with hLdef
  have hL1 : 1 ≤ L := le_max_left _ _
  set d : ℕ := (p * q) ^ L + 1 with hddef
  have hpq1 : 1 < p * q := by nlinarith
  have hLd : L < d := by
    have := Nat.lt_pow_self hpq1 (n := L)
    omega
  have hd1 : 1 < d := by
    have : 1 ≤ L := hL1
    omega
  have hcop : ∀ a : ℕ, a ∣ p * q → Nat.Coprime a d := by
    intro a ha
    have hdvd : a ∣ (p * q) ^ L := ha.trans (dvd_pow_self _ (by omega))
    have : Nat.gcd a d ∣ 1 := by
      have h1 : Nat.gcd a d ∣ (p * q) ^ L := (Nat.gcd_dvd_left a d).trans hdvd
      have h2 : Nat.gcd a d ∣ (p * q) ^ L + 1 := Nat.gcd_dvd_right a d
      exact (Nat.dvd_add_right h1).mp h2
    exact Nat.dvd_one.mp this
  refine ⟨d, hd1, ?_, hcop p (dvd_mul_right p q), hcop q (dvd_mul_left q p)⟩
  have hd' : (1 : ℝ) / δ < (d : ℝ) := by
    calc (1 : ℝ) / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (L : ℝ) := by exact_mod_cast le_max_right _ _
    _ < (d : ℝ) := by exact_mod_cast hLd
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hd'
  linarith

/-- Euler: a common exponent making both generators `≡ 1` mod `d`. -/
theorem exists_common_one_mod {d : ℕ} (hd : 1 < d)
    (hpd : Nat.Coprime p d) (hqd : Nat.Coprime q d) :
    ∃ m : ℕ, 0 < m ∧ p ^ m ≡ 1 [MOD d] ∧ q ^ m ≡ 1 [MOD d] :=
  ⟨d.totient, Nat.totient_pos.mpr (by omega),
    Nat.ModEq.pow_totient hpd, Nat.ModEq.pow_totient hqd⟩

/-- A multiplier `≡ 1 (mod d)` fixes every grid point `i/d` on the circle. -/
theorem smul_grid_fix {n d i : ℕ} (hd : 0 < d) (hmod : n ≡ 1 [MOD d]) :
    n • ((((i : ℝ) / (d : ℝ)) : ℝ) : UnitAddCircle) =
      ((((i : ℝ) / (d : ℝ)) : ℝ) : UnitAddCircle) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (n : ℤ) = 1 + (d : ℤ) * k := by
    obtain ⟨k', hk'⟩ := (hmod.dvd : (d : ℤ) ∣ (1 : ℤ) - (n : ℤ))
    exact ⟨-k', by push_cast at hk' ⊢; linear_combination -hk'⟩
  have hcoe : n • ((((i : ℝ) / d) : ℝ) : UnitAddCircle) =
      ((((n : ℝ) * ((i : ℝ) / d)) : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  rw [hcoe]
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have hdiff : (n : ℝ) * ((i : ℝ) / d) - (i : ℝ) / d = (((k * i : ℤ) : ℝ)) := by
    have hn' : (n : ℝ) = 1 + (d : ℝ) * (k : ℝ) := by exact_mod_cast hk
    push_cast
    field_simp [hn']
    linear_combination (i : ℝ) * hn'
  have hsub : ((((n : ℝ) * ((i : ℝ) / d)) : ℝ) : UnitAddCircle) -
      ((((i : ℝ) / d) : ℝ) : UnitAddCircle) = 0 := by
    rw [← QuotientAddGroup.mk_sub, hdiff]
    exact intCast_coe_eq_zero _
  exact sub_eq_zero.mp hsub

/-- The grid `{i/d : i < d}` is a `1/d`-net on the circle. -/
theorem grid_net {d : ℕ} (hd : 0 < d) (y : UnitAddCircle) :
    ∃ i : ℕ, i < d ∧ dist y ((((i : ℝ) / (d : ℝ)) : ℝ) : UnitAddCircle) < 1 / d := by
  obtain ⟨v₀, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [← coe_fract v₀]
  set v : ℝ := Int.fract v₀ with hvdef
  have hv0 : 0 ≤ v := Int.fract_nonneg v₀
  have hv1 : v < 1 := Int.fract_lt_one v₀
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨⌊v * d⌋₊, ?_, ?_⟩
  · rw [Nat.floor_lt (by positivity)]
    calc v * d < 1 * d := by nlinarith
    _ = (d : ℝ) := one_mul _
  · have h1 : (⌊v * d⌋₊ : ℝ) ≤ v * d := Nat.floor_le (by positivity)
    have h2 : v * d < (⌊v * d⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    calc dist ((v : ℝ) : UnitAddCircle) ((((⌊v * d⌋₊ : ℝ) / d) : ℝ) : UnitAddCircle)
        ≤ |v - (⌊v * d⌋₊ : ℝ) / d| := dist_coe_le _ _
      _ < 1 / d := by
          rw [abs_of_nonneg (by rw [sub_nonneg, div_le_iff₀ hd']; linarith)]
          rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hd']
          linarith

/-- The difference set of a closed subset of the circle is closed. -/
theorem isClosed_diff (hYcl : IsClosed Y) :
    IsClosed (image2 (· - ·) Y Y) := by
  have hYcomp : IsCompact Y := hYcl.isCompact
  have himg : image2 (· - ·) Y Y = (fun z : UnitAddCircle × UnitAddCircle => z.1 - z.2) ''
      (Y ×ˢ Y) := (Set.image_prod _).symm
  rw [himg]
  exact ((hYcomp.prod hYcomp).image (continuous_fst.sub continuous_snd)).isClosed

/-! ## §6  The intersection induction and the main theorem -/

/-- **Furstenberg's ×p×q topological rigidity (Furstenberg 1967, Theorem
IV.1).**  A closed subset of the circle invariant under two multiplicatively
independent multiplication maps is finite or the whole circle.  Proof after
Boshernitzan 1994 as presented in Manners arXiv:1305.1514 §4. -/
theorem isClosed_invariant_finite_or_univ (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : MultIndep p q) (hcl : IsClosed Y)
    (hP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) Y Y)
    (hQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) Y Y) :
    Y.Finite ∨ Y = univ := by
  rcases Y.finite_or_infinite with hf | hinf
  · exact Or.inl hf
  right
  set D : Set UnitAddCircle := derivedSet Y with hDdef
  have hDcl : IsClosed D := isClosed_derivedSet Y
  have hDY : D ⊆ Y := (isClosed_iff_derivedSet_subset Y).mp hcl
  have hDP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) D D :=
    fun x hx => accPt_smul (by omega) hP hx
  have hDQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) D D :=
    fun x hx => accPt_smul (by omega) hQ hx
  by_cases htor : ∃ β ∈ D, IsOfFinAddOrder β
  · obtain ⟨β, hβD, hβtor⟩ := htor
    exact eq_univ_of_accPt_torsion hp hq h hcl hP hQ hβD hβtor
  push Not at htor
  rw [← hcl.closure_eq]
  refine Dense.closure_eq ?_
  rw [Metric.dense_iff]
  intro y ε hε
  obtain ⟨d, hd1, hdε, hpd, hqd⟩ := exists_grid hp hq (δ := ε / 2) (by linarith)
  obtain ⟨m, hm0, hpm, hqm⟩ := exists_common_one_mod hd1 hpd hqd
  set P : ℕ := p ^ m with hPdef
  set Q : ℕ := q ^ m with hQdef
  have hP2 : 2 ≤ P := le_trans hp (Nat.le_self_pow (by omega) p)
  have hQ2 : 2 ≤ Q := le_trans hq (Nat.le_self_pow (by omega) q)
  have hPQ : MultIndep P Q := h.pow' hm0 hm0
  have hDP' : MapsTo (P • · : UnitAddCircle → UnitAddCircle) D D := mapsTo_pow_smul hDP m
  have hDQ' : MapsTo (Q • · : UnitAddCircle → UnitAddCircle) D D := mapsTo_pow_smul hDQ m
  set A : ℕ → UnitAddCircle := fun i => ((((i : ℝ) / (d : ℝ)) : ℝ) : UnitAddCircle) with hAdef
  have hAfixP : ∀ i, P • A i = A i := fun i => smul_grid_fix (by omega) hpm
  have hAfixQ : ∀ i, Q • A i = A i := fun i => smul_grid_fix (by omega) hqm
  set X : ℕ → Set UnitAddCircle :=
    fun k => D ∩ ⋂ i ∈ Finset.range k, ((· + A i) ⁻¹' D) with hXdef
  have hXsubD : ∀ k, X k ⊆ D := fun k => inter_subset_left
  have hXcl : ∀ k, IsClosed (X k) := by
    intro k
    apply hDcl.inter
    apply isClosed_biInter
    intro i _
    exact hDcl.preimage (continuous_add_const (A i))
  have hXP : ∀ k, MapsTo (P • · : UnitAddCircle → UnitAddCircle) (X k) (X k) := by
    intro k x hx
    show P • x ∈ X k
    obtain ⟨hxD, hxI⟩ := hx
    refine ⟨hDP' hxD, ?_⟩
    simp only [mem_iInter, mem_preimage] at hxI ⊢
    intro i hi
    have hfix : P • x + A i = P • (x + A i) := by rw [smul_add, hAfixP]
    rw [hfix]
    exact hDP' (hxI i hi)
  have hXQ : ∀ k, MapsTo (Q • · : UnitAddCircle → UnitAddCircle) (X k) (X k) := by
    intro k x hx
    show Q • x ∈ X k
    obtain ⟨hxD, hxI⟩ := hx
    refine ⟨hDQ' hxD, ?_⟩
    simp only [mem_iInter, mem_preimage] at hxI ⊢
    intro i hi
    have hfix : Q • x + A i = Q • (x + A i) := by rw [smul_add, hAfixQ]
    rw [hfix]
    exact hDQ' (hxI i hi)
  have hXne : ∀ k, (X k).Nonempty := by
    intro k
    induction k with
    | zero =>
      obtain ⟨x, hx⟩ := hinf.exists_accPt_principal
      exact ⟨x, hx, by simp⟩
    | succ k ih =>
      obtain ⟨x₀, hx₀⟩ := ih
      have hXinf : (X k).Infinite :=
        infinite_of_mem_not_torsion hP2 (hXP k) hx₀ (htor x₀ (hXsubD k hx₀))
      set Dk : Set UnitAddCircle := image2 (· - ·) (X k) (X k) with hDkdef
      have hDkcl : IsClosed Dk := isClosed_diff (hXcl k)
      have hDkP : MapsTo (P • · : UnitAddCircle → UnitAddCircle) Dk Dk := by
        intro z hz
        show P • z ∈ Dk
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        rw [smul_sub]
        exact mem_image2_of_mem (hXP k hx) (hXP k hy)
      have hDkQ : MapsTo (Q • · : UnitAddCircle → UnitAddCircle) Dk Dk := by
        intro z hz
        show Q • z ∈ Dk
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        rw [smul_sub]
        exact mem_image2_of_mem (hXQ k hx) (hXQ k hy)
      have hDkacc : AccPt 0 (𝓟 Dk) := accPt_zero_diff hXinf
      have hDkuniv : Dk = univ :=
        eq_univ_of_accPt_zero hP2 hQ2 hPQ hDkcl hDkP hDkQ hDkacc
      have hAk : A k ∈ Dk := hDkuniv ▸ mem_univ _
      obtain ⟨x, hx, y, hy, hxy⟩ := hAk
      have hyD : y ∈ D := hXsubD k hy
      have hyI : ∀ i ∈ Finset.range k, y + A i ∈ D := by
        have h2 := hy.2
        simp only [mem_iInter, mem_preimage] at h2
        exact h2
      have hyk : y + A k ∈ D := by
        have hx' : x = y + A k := by
          rw [sub_eq_iff_eq_add] at hxy
          rw [hxy, add_comm]
        rw [← hx']
        exact hXsubD k hx
      refine ⟨y, hyD, ?_⟩
      simp only [mem_iInter, mem_preimage, Finset.mem_range]
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
      · exact hyI i (Finset.mem_range.mpr hik)
      · rw [hik]
        exact hyk
  obtain ⟨xs, hxs⟩ := hXne d
  obtain ⟨i, hid, hidist⟩ := grid_net (d := d) (by omega) (y - xs)
  have hmem : xs + A i ∈ Y := by
    apply hDY
    have h2 := hxs.2
    simp only [mem_iInter, mem_preimage] at h2
    exact h2 i (Finset.mem_range.mpr hid)
  refine ⟨xs + A i, Metric.mem_ball.mpr ?_, hmem⟩
  have h1 : dist (xs + A i) y = dist (A i) (y - xs) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  rw [h1, dist_comm]
  calc dist (y - xs) (A i) < 1 / d := hidist
  _ < ε / 2 := hdε
  _ < ε := by linarith

/-- **Furstenberg's Diophantine corollary**: the ⟨p,q⟩-orbit of a non-torsion
point is dense in the circle. -/
theorem dense_orbit_of_not_isOfFinAddOrder (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : MultIndep p q) {x : UnitAddCircle} (hx : ¬ IsOfFinAddOrder x) :
    Dense {y : UnitAddCircle | ∃ r s : ℕ, (p ^ r * q ^ s) • x = y} := by
  set O : Set UnitAddCircle := {y | ∃ r s : ℕ, (p ^ r * q ^ s) • x = y} with hOdef
  have hOP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) O O := by
    rintro _ ⟨r, s, rfl⟩
    refine ⟨r + 1, s, ?_⟩
    show (p ^ (r + 1) * q ^ s) • x = p • ((p ^ r * q ^ s) • x)
    rw [← mul_nsmul]
    congr 1
    ring
  have hOQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) O O := by
    rintro _ ⟨r, s, rfl⟩
    refine ⟨r, s + 1, ?_⟩
    show (p ^ r * q ^ (s + 1)) • x = q • ((p ^ r * q ^ s) • x)
    rw [← mul_nsmul]
    congr 1
    ring
  have hcP : Continuous (fun z : UnitAddCircle => p • z) := continuous_nsmul p
  have hcQ : Continuous (fun z : UnitAddCircle => q • z) := continuous_nsmul q
  have hBP : MapsTo (p • · : UnitAddCircle → UnitAddCircle) (closure O) (closure O) :=
    hOP.closure hcP
  have hBQ : MapsTo (q • · : UnitAddCircle → UnitAddCircle) (closure O) (closure O) :=
    hOQ.closure hcQ
  have hxO : x ∈ O := ⟨0, 0, by simp⟩
  have hinf : (closure O).Infinite :=
    infinite_of_mem_not_torsion hp hBP (subset_closure hxO) hx
  rcases isClosed_invariant_finite_or_univ hp hq h isClosed_closure hBP hBQ with hfin | huniv
  · exact absurd hfin hinf.not_finite
  · rw [dense_iff_closure_eq]
    exact huniv

end Furstenberg
end NormalNumbers
