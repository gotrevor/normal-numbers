/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFIntervalGood

/-!
# B6 / L3 — affine transport

Expedition **B6** (`KHINCHIN.md` §B6), lemma **L3**: the affine map
`ψ(x) = q·x + r` (`q ≠ 0`) sends intervals to intervals with constant
distortion `|q|`.  For the affine-image witness route the key direction is the
PREIMAGE: a target CF-cylinder (an interval `(c,d)` in image space) pulls back
to an explicit interval `((c−r)/q, (d−r)/q)` in `x`-space, of length
`(d−c)/q`.  Feeding that interval to L2 (`length_le_two_mul_good_add_err`)
transports the good-block density onto the affine preimage — the density input
the extended schedule (L4) will consume to force `ψ(xstar)` CF-normal.

This module is purely the metric/interval algebra of `ψ` (self-contained real
analysis) plus the L2 corollary on preimages; the DEEP content — arranging
`xstar` so that `ψ(xstar)` is CF-normal — is the L4 schedule surgery
(`CFScheduleA.lean`, next).  `q > 0` is treated here; the general `q ≠ 0` case
follows by the reflection `x ↦ −x` (a `q < 0` map is `(−q) > 0` composed with
negation), deferred to the point of use.

Additive only: no edits to any frozen B5′ module.
-/

namespace NormalNumbers

open MeasureTheory

/-- The affine map `ψ(x) = q·x + r`. -/
def affineMap (q r : ℝ) : ℝ → ℝ := fun x => q * x + r

@[simp] lemma affineMap_apply (q r x : ℝ) : affineMap q r x = q * x + r := rfl

/-- **L3 (preimage form).**  For `q > 0`, the `ψ`-preimage of an open interval
is the open interval of pulled-back endpoints. -/
lemma preimage_affineMap_Ioo {q : ℝ} (hq : 0 < q) (r c d : ℝ) :
    affineMap q r ⁻¹' Set.Ioo c d = Set.Ioo ((c - r) / q) ((d - r) / q) := by
  ext x
  simp only [affineMap, Set.mem_preimage, Set.mem_Ioo]
  rw [div_lt_iff₀ hq, lt_div_iff₀ hq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩

/-- **L3 (image form).**  For `q > 0`, the `ψ`-image of an open interval is the
open interval of pushed-forward endpoints. -/
lemma image_affineMap_Ioo {q : ℝ} (hq : 0 < q) (r a b : ℝ) :
    affineMap q r '' Set.Ioo a b = Set.Ioo (q * a + r) (q * b + r) := by
  ext y
  simp only [affineMap, Set.mem_image, Set.mem_Ioo]
  constructor
  · rintro ⟨x, ⟨hax, hxb⟩, rfl⟩; exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(y - r) / q, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hq]; nlinarith
    · rw [div_lt_iff₀ hq]; nlinarith
    · show q * ((y - r) / q) + r = y
      field_simp [hq.ne']; ring

/-- **L3 (measure form).**  The `ψ`-preimage of `(c,d)` has length `(d−c)/q`
(constant distortion `1/q` under the pullback; `|q|` under the pushforward). -/
lemma volume_preimage_affineMap_Ioo {q : ℝ} (hq : 0 < q) (r c d : ℝ) :
    volume (affineMap q r ⁻¹' Set.Ioo c d) = ENNReal.ofReal ((d - c) / q) := by
  rw [preimage_affineMap_Ioo hq, Real.volume_Ioo]
  congr 1
  field_simp
  ring

/-- **L3 corollary — good density on an affine preimage.**  Transporting L2
(`length_le_two_mul_good_add_err`) through the pullback of a target interval
`(c,d)` whose `ψ`-preimage lands in `(0,1)`: the preimage length `(d−c)/q` is
at most twice the good mass inside the preimage plus the vanishing L1 error.
This is the affine-schedule (L4) density input — good CF-blocks live inside the
pullback of every target cylinder. -/
theorem good_mass_in_affine_preimage {q : ℝ} (hq : 0 < q) (r c d : ℝ)
    (h0 : 0 ≤ (c - r) / q) (hcd : (c - r) / q ≤ (d - r) / q) (h1 : (d - r) / q ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ENNReal.ofReal ((d - c) / q)
      ≤ 2 * volume (goodInInterval ((c - r) / q) ((d - r) / q) n m)
        + ENNReal.ofReal (4 / (Nat.fib (n + 1) : ℝ) ^ 2) := by
  have h := length_le_two_mul_good_add_err ((c - r) / q) ((d - r) / q) h0 hcd h1 hn m
  rwa [show (d - r) / q - (c - r) / q = (d - c) / q by field_simp; ring] at h

end NormalNumbers
