/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TBrickRefine

/-!
# W5 — the limit point of a nested cylinder sequence

The B–Y construction (§2.1) produces a strictly extending sequence of genuine
CF words `w 0 ≺ w 1 ≺ …`; the computed real is the point of
`⋂ s, cfCylinder (w s)`.  This file proves that point exists and is
irrational:

* `rat_dist_ge` — two distinct rationals `p/q`, `P/Q` are at distance
  `≥ 1/(qQ)` (no coprimality needed);
* `exists_irrational_mem_iInter_cfCylinder` — the main result.  Route:
  the closures of the cylinders are nested nonempty compacts, so they
  intersect; a rational point of the intersection would, once `cfK (w s)`
  exceeds its denominator, be forced (by `rat_dist_ge` against the cylinder
  length `1/(K(K+K'))`) to coincide with *both* rational endpoints of the
  enclosing interval — impossible; and an irrational point of the closed
  enclosure is interior, hence in every cylinder (`cfCylinder_endpoints`).
-/

namespace NormalNumbers

open MeasureTheory

/-- Two distinct rationals `p/q` and `P/Q` are at least `1/(qQ)` apart. -/
theorem rat_dist_ge {p : ℤ} {q P Q : ℕ} (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hne : (p : ℝ) / q ≠ (P : ℝ) / Q) :
    1 / ((q : ℝ) * Q) ≤ |(p : ℝ) / q - (P : ℝ) / Q| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  set D : ℤ := p * Q - P * q with hD
  have hD0 : D ≠ 0 := by
    intro h0
    rw [hD, sub_eq_zero] at h0
    apply hne
    have hreal : (p : ℝ) * Q = (P : ℝ) * q := by exact_mod_cast h0
    rw [div_eq_div_iff hqR.ne' hQR.ne']
    linarith
  have habs : |(p : ℝ) / q - (P : ℝ) / Q| = |(D : ℝ)| / ((q : ℝ) * Q) := by
    rw [hD]
    push_cast
    rw [div_sub_div _ _ hqR.ne' hQR.ne', abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * Q)]
    ring_nf
  have hD1 : (1 : ℝ) ≤ |(D : ℝ)| := by
    have h := Int.one_le_abs hD0
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|D| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |(D : ℝ)| := by push_cast; ring
  rw [habs]
  exact div_le_div_of_nonneg_right hD1 (by positivity)

/-- The word lengths of a strictly extending sequence grow at least
linearly. -/
theorem le_length_of_extending (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) :
    ∀ s, (w 0).length + s ≤ (w s).length := by
  intro s
  induction s with
  | zero => omega
  | succ n ih =>
    obtain ⟨u, hu_ne, hu⟩ := hext n
    have : 1 ≤ u.length := List.length_pos_of_ne_nil hu_ne
    rw [hu, List.length_append]
    omega

/-- **The limit point** (B–Y §2.1): a strictly extending sequence of genuine
CF words has an irrational point common to all its cylinders. -/
theorem exists_irrational_mem_iInter_cfCylinder
    (w : ℕ → List ℕ) (hne : ∀ s, w s ≠ [])
    (hpos : ∀ s, ∀ a ∈ w s, 1 ≤ a)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) :
    ∃ x : ℝ, Irrational x ∧ ∀ s, x ∈ cfCylinder (w s) := by
  have hK1 : ∀ s, 1 ≤ cfK (w s) := fun s => one_le_cfK (w s) (hpos s)
  have hK'1 : ∀ s, 1 ≤ cfK (w s).dropLast := fun s =>
    one_le_cfK (w s).dropLast
      (fun a ha => hpos s a (List.dropLast_subset _ ha))
  choose P P' hlen hsubIcc hIoo using fun s =>
    cfCylinder_endpoints (w s) (hne s) (hpos s)
  -- nested nonempty compacts: the closures of the cylinders
  set C : ℕ → Set ℝ := fun s => closure (cfCylinder (w s)) with hC
  have hnest : ∀ s, C (s + 1) ⊆ C s := by
    intro s
    apply closure_mono
    obtain ⟨u, -, hu⟩ := hext s
    rw [hu]
    exact cfCylinder_append_subset _ _
  have hcylne : ∀ s, (cfCylinder (w s)).Nonempty := fun s =>
    nonempty_of_measure_ne_zero
      (volume_cfCylinder_ne_zero (w s) (hne s) (hpos s))
  have hCne : ∀ s, (C s).Nonempty := fun s => (hcylne s).mono subset_closure
  have hCclosed : ∀ s, IsClosed (C s) := fun s => isClosed_closure
  have hCcompact : IsCompact (C 0) := by
    refine IsCompact.of_isClosed_subset
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)) (hCclosed 0) ?_
    refine closure_minimal ?_ isClosed_Icc
    exact fun x hx => Set.mem_Icc.2 ⟨(hx.1.1).le, (hx.1.2).le⟩
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      C hnest hCne hCcompact hCclosed
  simp only [Set.mem_iInter] at hx
  -- `x` lies in every enclosing rational-endpoint interval
  have hxIcc : ∀ s, x ∈ Set.uIcc
      ((P s : ℝ) / (cfK (w s) : ℝ))
      ((P' s : ℝ) / ((cfK (w s) : ℝ) + (cfK (w s).dropLast : ℝ))) := by
    intro s
    refine closure_minimal (hsubIcc s) ?_ (hx s)
    rw [Set.uIcc]
    exact isClosed_Icc
  -- diameter bound for two points of a `uIcc`
  have hdiam : ∀ (a b c e : ℝ), a ∈ Set.uIcc c e → b ∈ Set.uIcc c e →
      |a - b| ≤ |e - c| := by
    intro a b c e ha hb
    rw [Set.mem_uIcc] at ha hb
    rw [abs_sub_le_iff]
    have h1 := le_abs_self (e - c)
    have h2 := neg_abs_le (e - c)
    rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
      rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
      exact ⟨by linarith, by linarith⟩
  -- irrationality: a rational limit is forced onto both endpoints
  have hirr : Irrational x := by
    by_contra hrat
    obtain ⟨r, hr⟩ := not_not.1 hrat
    obtain ⟨q, hq1, hqden⟩ : ∃ q : ℕ, 1 ≤ q ∧ (r : ℝ) = (r.num : ℝ) / q :=
      ⟨r.den, r.den_pos, by rw [Rat.cast_def]⟩
    have hxq : x = (r.num : ℝ) / q := by rw [← hr, hqden]
    -- pick a stage where `cfK` exceeds the denominator
    set s : ℕ := q + 5 with hs
    have hlenw : q + 5 ≤ (w s).length := by
      have h1 := le_length_of_extending w hext s
      have h2 : 1 ≤ (w 0).length := List.length_pos_of_ne_nil (hne 0)
      omega
    have hfib : (w s).length + 1 ≤ Nat.fib ((w s).length + 1) :=
      Nat.le_fib_self (by omega)
    have hKbig : q + 5 ≤ cfK (w s) := by
      have h1 := fib_le_cfK (w s) (hpos s)
      omega
    have hKR : (0 : ℝ) < (cfK (w s) : ℝ) := by exact_mod_cast hK1 s
    have hK'R : (0 : ℝ) < (cfK (w s).dropLast : ℝ) := by
      exact_mod_cast hK'1 s
    have hqK : (q : ℝ) + 5 ≤ (cfK (w s) : ℝ) := by exact_mod_cast hKbig
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
    have hxs := hxIcc s
    have hlens := hlen s
    -- distance from `x` to each endpoint is at most the gap
    have hd0 : |x - (P s : ℝ) / (cfK (w s) : ℝ)|
        ≤ 1 / ((cfK (w s) : ℝ) * ((cfK (w s) : ℝ)
            + (cfK (w s).dropLast : ℝ))) := by
      rw [← hlens]
      exact hdiam _ _ _ _ hxs Set.left_mem_uIcc
    have hd1 : |x - (P' s : ℝ) / ((cfK (w s) : ℝ)
          + (cfK (w s).dropLast : ℝ))|
        ≤ 1 / ((cfK (w s) : ℝ) * ((cfK (w s) : ℝ)
            + (cfK (w s).dropLast : ℝ))) := by
      rw [← hlens]
      exact hdiam _ _ _ _ hxs Set.right_mem_uIcc
    -- x must equal the left endpoint
    have hxE0 : x = (P s : ℝ) / (cfK (w s) : ℝ) := by
      by_contra hne0
      have hne' : (r.num : ℝ) / q ≠ (P s : ℝ) / (cfK (w s) : ℝ) := by
        rw [← hxq]
        exact hne0
      have hge := rat_dist_ge (p := r.num) (P := P s) hq1 (hK1 s) hne'
      rw [← hxq] at hge
      have hlt : 1 / ((cfK (w s) : ℝ) * ((cfK (w s) : ℝ)
            + (cfK (w s).dropLast : ℝ)))
          < 1 / ((q : ℝ) * (cfK (w s) : ℝ)) := by
        apply div_lt_div_of_pos_left one_pos (by positivity)
        have h1 : (q : ℝ) < (cfK (w s) : ℝ) + (cfK (w s).dropLast : ℝ) := by
          linarith
        calc (q : ℝ) * (cfK (w s) : ℝ)
            < ((cfK (w s) : ℝ) + (cfK (w s).dropLast : ℝ))
              * (cfK (w s) : ℝ) := mul_lt_mul_of_pos_right h1 hKR
          _ = (cfK (w s) : ℝ) * ((cfK (w s) : ℝ)
              + (cfK (w s).dropLast : ℝ)) := by ring
      linarith
    -- and the right endpoint
    have hxE1 : x = (P' s : ℝ) / ((cfK (w s) : ℝ)
        + (cfK (w s).dropLast : ℝ)) := by
      by_contra hne1
      have hKK' : 1 ≤ cfK (w s) + cfK (w s).dropLast := by
        have := hK1 s
        omega
      have hcast : ((cfK (w s) + cfK (w s).dropLast : ℕ) : ℝ)
          = (cfK (w s) : ℝ) + (cfK (w s).dropLast : ℝ) := by
        push_cast
        ring
      have hne' : (r.num : ℝ) / q
          ≠ (P' s : ℝ) / ((cfK (w s) + cfK (w s).dropLast : ℕ) : ℝ) := by
        rw [hcast, ← hxq]
        exact hne1
      have hge := rat_dist_ge (p := r.num) (P := P' s) hq1 hKK' hne'
      rw [hcast, ← hxq] at hge
      have hlt : 1 / ((cfK (w s) : ℝ) * ((cfK (w s) : ℝ)
            + (cfK (w s).dropLast : ℝ)))
          < 1 / ((q : ℝ) * ((cfK (w s) : ℝ)
            + (cfK (w s).dropLast : ℝ))) := by
        apply div_lt_div_of_pos_left one_pos (by positivity)
        have h1 : (q : ℝ) < (cfK (w s) : ℝ) := by linarith
        exact mul_lt_mul_of_pos_right h1 (by positivity)
      linarith
    -- but the endpoints are distinct (positive gap)
    rw [hxE0] at hxE1
    have h0 : |((P' s : ℝ) / ((cfK (w s) : ℝ) + (cfK (w s).dropLast : ℝ)))
        - ((P s : ℝ) / (cfK (w s) : ℝ))| = 0 := by
      rw [← hxE1]
      simp
    rw [hlens] at h0
    have hpos0 : (0 : ℝ) < 1 / ((cfK (w s) : ℝ)
        * ((cfK (w s) : ℝ) + (cfK (w s).dropLast : ℝ))) := by
      have := hK1 s
      have := hK'1 s
      positivity
    linarith
  -- irrational + closed enclosure ⇒ strictly interior ⇒ in every cylinder
  refine ⟨x, hirr, fun s => ?_⟩
  apply hIoo s x ?_ hirr
  have hxs := hxIcc s
  have hne0 : x ≠ (P s : ℝ) / (cfK (w s) : ℝ) := by
    intro h
    exact hirr ⟨(P s : ℚ) / (cfK (w s) : ℚ), by rw [h]; push_cast; ring⟩
  have hne1 : x ≠ (P' s : ℝ) / ((cfK (w s) : ℝ)
      + (cfK (w s).dropLast : ℝ)) := by
    intro h
    refine hirr ⟨(P' s : ℚ) / ((cfK (w s) : ℚ) + (cfK (w s).dropLast : ℚ)), ?_⟩
    rw [h]
    push_cast
    ring
  rw [Set.mem_uIcc] at hxs
  rcases hxs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Set.mem_uIoo_of_lt (lt_of_le_of_ne h1 (fun h => hne0 h.symm))
      (lt_of_le_of_ne h2 hne1)
  · exact Set.mem_uIoo_of_gt (lt_of_le_of_ne h1 (fun h => hne1 h.symm))
      (lt_of_le_of_ne h2 hne0)

end NormalNumbers
