/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-MS: `MapState` — the state type the emission step actually needs

S7-NE showed `MobState`'s sign convention (`0 ≤ a`, a nondecreasing numerator) is too narrow: the
emission `readState a ∘ u = t` forces `u.a = t.c − a·t.a`, and a perfectly reduced state can need
`u.a < 0`.  The right invariant is not a sign pattern but the *interval* condition "`mob` maps
`[0,1]` into `[0,1]`", and because numerator and denominator are affine in `z` that condition is
just four inequalities at the two endpoints:

    0 ≤ b ≤ d,   0 ≤ a + b ≤ c + d,   0 < d,   0 < c + d.

`MapState` is that.  Three facts make it the right type:

* `MapState.mapsTo` — `mob` really does map `[0,1]` into `[0,1]` (and `(0,1)` into `[0,1]`);
* `MapState.comp` — it is **closed under composition**, with the same matrix product as `MobState`
  (the proof is the observation that `0 ≤ p ≤ q`, `0 < q` gives `0 ≤ a·p + b·q ≤ c·p + d·q`, i.e.
  affine interpolation between the two endpoint conditions);
* `MapState.exists_emit` — **the emission step is unconditional**: `t` factors as
  `readState a ∘ u` with `u : MapState` *exactly when* `t.mob 0` and `t.mob 1` lie in
  `[1/(a+1), 1/a]`, which is precisely "the image of `t` lies in the cylinder `I_a`".
  Witness `u = [[t.c − a·t.a, t.d − a·t.b], [t.a, t.b]]`, which S7-NE showed is forced.

`MobState.toMapState` embeds the old type, so nothing already proved is lost; what is gained is
that the transducer recursion of S7-PN can now actually be run.
-/
import NormalNumbers.VandeheyS7NoEmit

namespace NormalNumbers.VandeheyS7

/-- A Möbius map of `[0,1]` into `[0,1]`, recorded by its matrix and the four endpoint
inequalities that say so. -/
structure MapState where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  hd : 0 < d
  hcd : 0 < c + d
  hb0 : 0 ≤ b
  hbd : b ≤ d
  hab0 : 0 ≤ a + b
  habcd : a + b ≤ c + d
  hdet : a * d - b * c ≠ 0

namespace MapState

/-- The Möbius action. -/
noncomputable def mob (s : MapState) (z : ℝ) : ℝ := (s.a * z + s.b) / (s.c * z + s.d)

lemma den_pos (s : MapState) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) : 0 < s.c * z + s.d := by
  have h : s.c * z + s.d = (1 - z) * s.d + z * (s.c + s.d) := by ring
  rw [h]
  rcases eq_or_lt_of_le hz.1 with h0 | h0
  · simp [← h0, s.hd]
  · have : 0 ≤ (1 - z) * s.d := mul_nonneg (by linarith [hz.2]) s.hd.le
    nlinarith [s.hcd]

lemma num_nonneg (s : MapState) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) : 0 ≤ s.a * z + s.b := by
  have h : s.a * z + s.b = (1 - z) * s.b + z * (s.a + s.b) := by ring
  rw [h]
  have h1 : 0 ≤ (1 - z) * s.b := mul_nonneg (by linarith [hz.2]) s.hb0
  have h2 : 0 ≤ z * (s.a + s.b) := mul_nonneg hz.1 s.hab0
  linarith

lemma num_le_den (s : MapState) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    s.a * z + s.b ≤ s.c * z + s.d := by
  have h : (s.c * z + s.d) - (s.a * z + s.b)
      = (1 - z) * (s.d - s.b) + z * ((s.c + s.d) - (s.a + s.b)) := by ring
  nlinarith [mul_nonneg (by linarith [hz.2] : (0:ℝ) ≤ 1 - z) (by linarith [s.hbd] : (0:ℝ) ≤ s.d - s.b),
    mul_nonneg hz.1 (by linarith [s.habcd] : (0:ℝ) ≤ (s.c + s.d) - (s.a + s.b))]

/-- **The defining property.**  `mob` maps `[0,1]` into `[0,1]`. -/
theorem mapsTo (s : MapState) : Set.MapsTo s.mob (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
  intro z hz
  have hden := s.den_pos hz
  simp only [mob]
  constructor
  · exact div_nonneg (s.num_nonneg hz) hden.le
  · rw [div_le_one hden]
    exact s.num_le_den hz

/-! ## Composition -/

/-- The key interpolation: an affine functional nonneg at the two endpoints is nonneg on a ray
through a point of the unit "interval of ratios". -/
private lemma aux (s : MapState) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) :
    0 ≤ s.a * p + s.b * q ∧ s.a * p + s.b * q ≤ s.c * p + s.d * q := by
  set z : ℝ := p / q with hzdef
  have hz : z ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg hp hq.le, (div_le_one hq).2 hpq⟩
  have hpz : p = z * q := by rw [hzdef]; field_simp
  constructor
  · have := s.num_nonneg hz
    rw [hpz]
    nlinarith
  · have := s.num_le_den hz
    rw [hpz]
    nlinarith

private lemma aux_pos (s : MapState) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) :
    0 < s.c * p + s.d * q := by
  set z : ℝ := p / q with hzdef
  have hz : z ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg hp hq.le, (div_le_one hq).2 hpq⟩
  have hden := s.den_pos hz
  have hpz : p = z * q := by rw [hzdef]; field_simp
  rw [hpz]
  nlinarith

/-- **Closure under composition**, with the matrix product. -/
noncomputable def comp (s t : MapState) : MapState where
  a := s.a * t.a + s.b * t.c
  b := s.a * t.b + s.b * t.d
  c := s.c * t.a + s.d * t.c
  d := s.c * t.b + s.d * t.d
  hd := s.aux_pos t.hb0 t.hbd t.hd
  hcd := by
    have h := s.aux_pos t.hab0 t.habcd t.hcd
    have he : s.c * (t.a + t.b) + s.d * (t.c + t.d)
        = (s.c * t.a + s.d * t.c) + (s.c * t.b + s.d * t.d) := by ring
    linarith [he ▸ h]
  hb0 := (s.aux t.hb0 t.hbd t.hd).1
  hbd := (s.aux t.hb0 t.hbd t.hd).2
  hab0 := by
    have := (s.aux t.hab0 t.habcd t.hcd).1
    have he : s.a * (t.a + t.b) + s.b * (t.c + t.d)
        = (s.a * t.a + s.b * t.c) + (s.a * t.b + s.b * t.d) := by ring
    linarith [he ▸ this]
  habcd := by
    have := (s.aux t.hab0 t.habcd t.hcd).2
    have he1 : s.a * (t.a + t.b) + s.b * (t.c + t.d)
        = (s.a * t.a + s.b * t.c) + (s.a * t.b + s.b * t.d) := by ring
    have he2 : s.c * (t.a + t.b) + s.d * (t.c + t.d)
        = (s.c * t.a + s.d * t.c) + (s.c * t.b + s.d * t.d) := by ring
    linarith [he1 ▸ he2 ▸ this]
  hdet := by
    have hid : (s.a * t.a + s.b * t.c) * (s.c * t.b + s.d * t.d)
        - (s.a * t.b + s.b * t.d) * (s.c * t.a + s.d * t.c)
        = (s.a * s.d - s.b * s.c) * (t.a * t.d - t.b * t.c) := by ring
    rw [hid]
    exact mul_ne_zero s.hdet t.hdet

@[simp] lemma comp_a (s t : MapState) : (s.comp t).a = s.a * t.a + s.b * t.c := rfl
@[simp] lemma comp_b (s t : MapState) : (s.comp t).b = s.a * t.b + s.b * t.d := rfl
@[simp] lemma comp_c (s t : MapState) : (s.comp t).c = s.c * t.a + s.d * t.c := rfl
@[simp] lemma comp_d (s t : MapState) : (s.comp t).d = s.c * t.b + s.d * t.d := rfl

theorem mob_comp (s t : MapState) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    (s.comp t).mob z = s.mob (t.mob z) := by
  have ht : 0 < t.c * z + t.d := t.den_pos hz
  have hst : 0 < (s.comp t).c * z + (s.comp t).d := (s.comp t).den_pos hz
  have hs : 0 < s.c * ((t.a * z + t.b) / (t.c * z + t.d)) + s.d := by
    have := s.den_pos (t.mapsTo hz)
    simpa [mob] using this
  simp only [mob, comp_a, comp_b, comp_c, comp_d]
  rw [div_eq_div_iff (by simpa [mob, comp_a, comp_b, comp_c, comp_d] using hst.ne') hs.ne']
  field_simp
  ring

theorem ext_entries {s t : MapState} (ha : s.a = t.a) (hb : s.b = t.b) (hc : s.c = t.c)
    (hd : s.d = t.d) : s = t := by
  cases s; cases t; simp_all

/-! ## `MobState` embeds -/

/-- Every `MobState` whose image lies in `[0,1]` is a `MapState`; the hypotheses are the endpoint
conditions, which for a `MobState` reduce to `b ≤ d` and `a + b ≤ c + d`. -/
noncomputable def _root_.NormalNumbers.VandeheyS7.MobState.toMapState (s : MobState)
    (h0 : s.b ≤ s.d) (h1 : s.a + s.b ≤ s.c + s.d) : MapState where
  a := s.a
  b := s.b
  c := s.c
  d := s.d
  hd := s.hd
  hcd := by linarith [s.hc, s.hd]
  hb0 := s.hb
  hbd := h0
  hab0 := by linarith [s.ha, s.hb]
  habcd := h1
  hdet := s.hdet

/-! ## The emission step -/

/-- The digit-reading state, as a `MapState`. -/
noncomputable def readMap (a : ℝ) (ha : 1 ≤ a) : MapState where
  a := 0
  b := 1
  c := 1
  d := a
  hd := lt_of_lt_of_le zero_lt_one ha
  hcd := by linarith
  hb0 := zero_le_one
  hbd := ha
  hab0 := by linarith
  habcd := by linarith
  hdet := by
    show (0:ℝ) * a - 1 * 1 ≠ 0
    norm_num

@[simp] lemma readMap_mob (a : ℝ) (ha : 1 ≤ a) (z : ℝ) :
    (readMap a ha).mob z = 1 / (z + a) := by
  show ((0:ℝ) * z + 1) / (1 * z + a) = 1 / (z + a)
  ring_nf

/-- **S7-MS, the emission step — unconditional.**  `t` factors through reading the digit `a`
exactly when its endpoint values lie in the cylinder `[1/(a+1), 1/a]`.  The witness is the one
S7-NE showed is forced; what changed is that it is now a legitimate state. -/
theorem exists_emit (t : MapState) {a : ℝ} (ha : 1 ≤ a)
    (hlo0 : 1 / (a + 1) ≤ t.mob 0) (hhi0 : t.mob 0 ≤ 1 / a)
    (hlo1 : 1 / (a + 1) ≤ t.mob 1) (hhi1 : t.mob 1 ≤ 1 / a) :
    ∃ u : MapState, (readMap a ha).comp u = t := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have ha1 : (0:ℝ) < a + 1 := by linarith
  -- endpoint values as ratios
  have hd0 : (0:ℝ) < t.d := t.hd
  have hd1 : (0:ℝ) < t.c + t.d := t.hcd
  have he0 : t.mob 0 = t.b / t.d := by simp [mob]
  have he1 : t.mob 1 = (t.a + t.b) / (t.c + t.d) := by
    simp only [mob]; ring_nf
  rw [he0] at hlo0 hhi0
  rw [he1] at hlo1 hhi1
  rw [div_le_div_iff₀ ha1 hd0] at hlo0
  rw [div_le_div_iff₀ hd0 ha0] at hhi0
  rw [div_le_div_iff₀ ha1 hd1] at hlo1
  rw [div_le_div_iff₀ hd1 ha0] at hhi1
  -- `hlo0 : t.d ≤ (a+1) * t.b`,  `hhi0 : a * t.b ≤ t.d`, similarly at 1
  have htb : 0 < t.b := by nlinarith
  have htab : 0 < t.a + t.b := by nlinarith
  refine ⟨⟨t.c - a * t.a, t.d - a * t.b, t.a, t.b, htb, htab, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, ?_⟩, ?_⟩
  · show (t.c - a * t.a) * t.b - (t.d - a * t.b) * t.a ≠ 0
    have hrw : (t.c - a * t.a) * t.b - (t.d - a * t.b) * t.a = -(t.a * t.d - t.b * t.c) := by ring
    rw [hrw]
    intro h
    exact t.hdet (by linarith)
  · refine ext_entries ?_ ?_ ?_ ?_
    · show (0:ℝ) * (t.c - a * t.a) + 1 * t.a = t.a; ring
    · show (0:ℝ) * (t.d - a * t.b) + 1 * t.b = t.b; ring
    · show (1:ℝ) * (t.c - a * t.a) + a * t.a = t.c; ring
    · show (1:ℝ) * (t.d - a * t.b) + a * t.b = t.d; ring

/-- The map S7-NE exhibited as missing IS a `MapState`. -/
noncomputable def noEmitWitness : MapState :=
  ⟨-1, 1, 1, 1, one_pos, by norm_num, zero_le_one, le_refl 1, by norm_num, by norm_num,
    by norm_num⟩

@[simp] lemma noEmitWitness_mob (z : ℝ) : noEmitWitness.mob z = (1 - z) / (z + 1) := by
  show ((-1:ℝ) * z + 1) / (1 * z + 1) = (1 - z) / (z + 1)
  ring_nf

end MapState

section Audit

#print axioms MapState.mapsTo
#print axioms MapState.mob_comp
#print axioms MapState.exists_emit

end Audit

end NormalNumbers.VandeheyS7
