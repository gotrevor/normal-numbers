/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.Disjunctive
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Second-round proposals: exact spigot, oscillator certificates, radical norms

Read `../../../MAZE.md` before reopening or retiring these proposals.
These are unproved research nodes, not three established proof mechanisms.
See `docs/pi-routes/round-two.md` for the mechanism tests and stop conditions.
The transfers below are conditional; no new digit assertion about pi is proved.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.RoundTwo

def BinaryWord (w : List ℕ) : Prop := ∀ d ∈ w, d < 2

def AvoidsWord (w : List ℕ) (x : ℝ) : Prop :=
  ∀ n, ¬ OccursAt 2 x w n

/-! ## 4. The exact hypergeometric spigot -/

/-- The affine enclosure is `(p*z+r)/q`, with the unread tail in `[2,4]`.
The initial enclosure represents pi minus its integer part. -/
structure SpigotState where
  n : ℕ
  p : ℤ
  r : ℤ
  q : ℤ
  output : List ℕ
  deriving DecidableEq, Repr

def spigotInitial : SpigotState := ⟨0, 1, -3, 1, []⟩

/-- Substitute the exact tail map `z -> 2 + (n+1)*z/(2*n+3)`.
No approximate forcing or adjustable residual is permitted. -/
def refine (s : SpigotState) : SpigotState :=
  { s with
    n := s.n + 1
    p := (s.n + 1) * s.p
    r := (2 * s.p + s.r) * (2 * s.n + 3)
    q := (2 * s.n + 3) * s.q }

def CanEmit (s : SpigotState) (d : ℕ) : Prop :=
  0 < s.q ∧ d < 2 ∧ (d : ℤ) * s.q ≤ 2 * (2 * s.p + s.r) ∧
    2 * (4 * s.p + s.r) < (d + 1 : ℤ) * s.q

instance (s : SpigotState) (d : ℕ) : Decidable (CanEmit s d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def emit (s : SpigotState) (d : ℕ) : SpigotState :=
  { s with p := 2 * s.p, r := 2 * s.r - d * s.q, output := s.output ++ [d] }

def spigotStep (s : SpigotState) : SpigotState :=
  if CanEmit s 0 then emit s 0 else if CanEmit s 1 then emit s 1 else refine s

def spigotRun : ℕ → SpigotState
  | 0 => spigotInitial
  | n + 1 => spigotStep (spigotRun n)

/-- Classical identity behind the machine, recorded as an input rather than
silently counted as a proved theorem in this module. -/
def HypergeometricPiIdentity : Prop :=
  HasSum (fun n : ℕ => (2 : ℝ) ^ (n + 1) * (Nat.factorial n : ℝ) ^ 2 /
    (Nat.factorial (2 * n + 1) : ℝ)) Real.pi

/-- Ordinary enclosure correctness, distinct from word production.  It should
follow from the hypergeometric identity and the uniform unread-tail bound. -/
def SpigotSound : Prop :=
  ∀ t a w b, (spigotRun t).output = a ++ w ++ b →
    OccursAt 2 Real.pi w a.length

/-- Open quantitative test node, NOT an advance by itself.  The proposed
research is to find uniform arithmetic invariants proving it.  Merely computing
its witnesses is not that mechanism.  C absorbs read/emit costs and small words.
Truth confidence: 85%, heuristic only; no uniform empirical evidence. -/
@[blueprint (title := "Exact pi spigot: exponential word-escape budget")]
def SpigotEscapeBudget : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ w : List ℕ, BinaryWord w →
    ∃ t ≤ C * (w.length + 1) * 2 ^ w.length,
      ∃ a b, (spigotRun t).output = a ++ w ++ b

/-- Finite calibration statement, supported by the exact Python probe.  This
definition does not certify the probe or prove its universal counterpart. -/
def SpigotCalibrationC4 : Prop :=
  ∀ w : List ℕ, BinaryWord w → w.length ≤ 8 →
    ∃ t ≤ 4 * (w.length + 1) * 2 ^ w.length,
      ∃ a b, (spigotRun t).output = a ++ w ++ b

#guard (spigotRun 40).output.take 8 == [0, 0, 1, 0, 0, 1, 0, 0]

theorem pi_disjunctive_of_spigotEscape
    (hs : SpigotSound) (he : SpigotEscapeBudget) : IsDisjunctive 2 Real.pi := by
  rw [isDisjunctive_iff_forall_occursAt 2 (by omega)]
  intro w hw
  obtain ⟨C, _, hC⟩ := he
  obtain ⟨t, _, a, b, hab⟩ := hC w hw
  exact ⟨a.length, hs t a w b hab⟩

/-! ## 5. Polynomial certificates from the oscillator equation -/

noncomputable def realPoly (P : Polynomial ℚ) : Polynomial ℝ :=
  P.map (algebraMap ℚ ℝ)

def PositiveOscillator (P : Polynomial ℚ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 4,
    0 < ((realPoly P).derivative.derivative + realPoly P).eval t

def OscillatorIntegralIdentity : Prop :=
  ∀ P : Polynomial ℚ,
    (realPoly P).eval 0 + (realPoly P).eval Real.pi =
      ∫ t in (0 : ℝ)..Real.pi,
        ((realPoly P).derivative.derivative + realPoly P).eval t * Real.sin t

/-- Elementary analytic bridge, not discharged here.  Integration by parts gives
`P(0)+P(pi) = integral_0^pi (P''+P)(t)*sin(t) dt > 0`.
This is not the research crux; the certificate supply below is. -/
def OscillatorPositivityBridge : Prop :=
  ∀ P : Polynomial ℚ, PositiveOscillator P →
    0 < (realPoly P).eval 0 + (realPoly P).eval Real.pi

/-- Open certificate-supply node.  Seek certificates using the forbidden-word
automaton, not by first locating the word in computed pi digits.
No claim of logical weakness relative to disjunctivity is made.
Truth confidence: 80%, conditional on the expected digit behavior; finding
a useful uniform certificate construction is substantially less certain. -/
@[blueprint (title := "Word-specific oscillator certificates excluding pi avoidance")]
def OscillatorCertificateSupply : Prop :=
  ∀ w : List ℕ, BinaryWord w → w ≠ [] →
    ∃ P : Polynomial ℚ, PositiveOscillator P ∧
      ∀ x ∈ Set.Icc (3 : ℝ) 4, AvoidsWord w x →
        (realPoly P).eval 0 + (realPoly P).eval x ≤ 0

theorem pi_disjunctive_of_oscillatorCertificates
    (hb : OscillatorPositivityBridge) (hc : OscillatorCertificateSupply) :
    IsDisjunctive 2 Real.pi := by
  rw [isDisjunctive_iff_forall_occursAt 2 (by omega)]
  intro w hw
  by_cases he : w = []
  · subst w
    exact ⟨0, by simp [OccursAt]⟩
  by_contra hn
  obtain ⟨P, hP, hsep⟩ := hc w hw he
  have ha : AvoidsWord w Real.pi := by
    intro n h
    exact hn ⟨n, h⟩
  have hle := hsep Real.pi ⟨Real.pi_gt_three.le, Real.pi_lt_four.le⟩ ha
  exact (not_lt_of_ge hle) (hb P hP)

/-! ## 6. Relative norms in the polygon-halving tower -/

/-- The largest real root is `2*cos(pi/2^(n+1))`.  Its special role must
survive the norm argument; a norm alone forgets the chosen embedding. -/
noncomputable def radicalPolynomial : ℕ → Polynomial ℤ
  | 0 => Polynomial.X
  | n + 1 => (radicalPolynomial n).comp (Polynomial.X ^ 2 - Polynomial.C 2)

theorem radicalPolynomial_eval_two (n : ℕ) :
    (radicalPolynomial n).eval 2 = 2 := by
  induction n with
  | zero => simp [radicalPolynomial]
  | succ n ih => simpa [radicalPolynomial, Polynomial.eval_comp] using ih

/-- Ordinary algebraic bridge, explicitly open here.  It links the integer
polynomial tower to the distinguished real root rather than an arbitrary root. -/
def RadicalRootIdentity : Prop :=
  ∀ n : ℕ, (radicalPolynomial n).eval₂ (algebraMap ℤ ℝ)
    (2 * Real.cos (Real.pi / 2 ^ (n + 1))) = 0

def RadicalPerimeterLimit : Prop :=
  Filter.Tendsto
    (fun n : ℕ => (2 : ℝ) ^ (n + 1) *
      Real.sqrt (2 - 2 * Real.cos (Real.pi / 2 ^ (n + 1))))
    Filter.atTop (nhds Real.pi)

/-- The broader research conjecture suggested by relative norms: real angular
logarithms of algebraic points have every binary word.  The proposed proof would
need a word-dependent norm loss retaining the distinguished embedding.
This is stronger than the pi instance; it is not claimed proved or novel in print.
Truth confidence: 85%, heuristic only. -/
@[blueprint (title := "Algebraic angle seeds give binary disjunctive limits")]
def AlgebraicAngleDisjunctivity : Prop :=
  ∀ a : ℝ, IsAlgebraic ℚ a → -2 < a → a < 2 →
    IsDisjunctive 2 (2 * Real.arccos (a / 2))

theorem pi_disjunctive_of_algebraicAngles
    (h : AlgebraicAngleDisjunctivity) : IsDisjunctive 2 Real.pi := by
  have h0 := h 0 (isAlgebraic_zero) (by norm_num) (by norm_num)
  convert h0 using 1 <;> simp [Real.arccos_zero] <;> ring

end NormalNumbers.PiDisjunctiveRoutes.RoundTwo
