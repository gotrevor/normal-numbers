/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.RoundTwo

/-!
# Frozen targets for the bounded second-round mechanism pilots

Read `../../../MAZE.md` and `docs/pi-routes/pilots/README.md`.
These are open propositions until the corresponding pilot supplies proofs.
They test specific certificate families, not the truth of pi disjunctivity.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots

/-- Expected true (99%, direct cubic identity).  A cubic oscillator cannot even
exclude x=3: its value there equals the sum of two positive residual values. -/
@[blueprint (title := "Cubic oscillator certificates are blind at three")]
def CubicBlindAtThree : Prop :=
  ∀ P : Polynomial ℚ, P.natDegree ≤ 3 → PositiveOscillator P →
    0 < (realPoly P).eval 0 + (realPoly P).eval 3

/-- Positive control: residual is `x*(4-x)*(x-2)^2 + 1/4`.
This excludes the single point 3, not an entire forbidden-word set. -/
noncomputable def quarticControl : Polynomial ℚ :=
  -Polynomial.X ^ 4 + 8 * Polynomial.X ^ 3 - 8 * Polynomial.X ^ 2 -
    32 * Polynomial.X + Polynomial.C (65 / 4)

/-- Expected true (99%, exact algebra). -/
def QuarticRejectsThree : Prop :=
  PositiveOscillator quarticControl ∧
    (realPoly quarticControl).eval 0 + (realPoly quarticControl).eval 3 < 0

/-- Expected true (99%, independently checked exact rational quadrature).
All weights are positive and all nodes lie in [0,4]. -/
def QuarticQuadratureIdentity : Prop :=
  ∀ P : Polynomial ℚ, P.natDegree ≤ 4 →
    let R := (realPoly P).derivative.derivative + realPoly P
    10 * ((realPoly P).eval 0 + (realPoly P).eval 3) +
        ((realPoly P).eval 0 + (realPoly P).eval 4) =
      (7 / 12 : ℝ) * R.eval 0 + (8 / 3 : ℝ) * R.eval (1 / 2) +
      (184 / 15 : ℝ) * R.eval (3 / 2) + (35 / 6 : ℝ) * R.eval 2 +
      (13 / 20 : ℝ) * R.eval 4

/-- Expected true (99%, consequence of the positive quadrature).  A quartic
cannot reject both 3 and 4, hence cannot certify the forbidden word [1]. -/
@[blueprint (title := "Quartic oscillator certificates cannot reject both integer endpoints")]
def QuarticEndpointObstruction : Prop :=
  ∀ P : Polynomial ℚ, P.natDegree ≤ 4 → PositiveOscillator P →
    0 < 10 * ((realPoly P).eval 0 + (realPoly P).eval 3) +
      ((realPoly P).eval 0 + (realPoly P).eval 4)

/-- Candidate sharp positive control: residual `x*(x-2)^4 + 1/4`. -/
noncomputable def quinticControl : Polynomial ℚ :=
  Polynomial.X ^ 5 - 8 * Polynomial.X ^ 4 + 4 * Polynomial.X ^ 3 +
    64 * Polynomial.X ^ 2 - 8 * Polynomial.X - Polynomial.C (511 / 4)

/-- Expected true (99%, exact coefficient calculation).  The endpoint values
are -1/2 and -63/2.  Together with classification of [1]-avoiders in [3,4],
this should give a degree-five certificate and make the quartic barrier sharp. -/
def QuinticEndpointControl : Prop :=
  PositiveOscillator quinticControl ∧
    (realPoly quinticControl).eval 0 + (realPoly quinticControl).eval 3 < 0 ∧
    (realPoly quinticControl).eval 0 + (realPoly quinticControl).eval 4 < 0

/-- Generalization suggested by finite-dimensional positivity; open (95%).
Normalize the residual Q=P''+P.  Compactness of the fixed-degree positive cone
gives a positive lower bound for its sine integral, while the inverse oscillator
operator bounds P'.  This would produce a coefficient-independent blind interval.
No quantitative radius or Lean proof is claimed here. -/
@[blueprint (title := "Fixed polynomial degree has a uniform blind interval around pi")]
def FixedDegreeBlindInterval : Prop :=
  ∀ D : ℕ, ∃ ε : ℝ, 0 < ε ∧
    ∀ P : Polynomial ℚ, P.natDegree ≤ D → PositiveOscillator P →
      ∀ x : ℝ, |x - Real.pi| < ε →
        0 < (realPoly P).eval 0 + (realPoly P).eval x

/-- Expected true (99%, difference of squares).  The sibling restores exactly
the previous factor, regardless of the distinguished branch's size. -/
@[blueprint (title := "Relative radical factors exactly compensate")]
def RelativeNormCancellation : Prop :=
  ∀ a : ℝ, -2 ≤ a →
    (2 - Real.sqrt (2 + a)) * (2 + Real.sqrt (2 + a)) = 2 - a

/-- A deliberately narrow proposed gain, expected false.  A refutation does not
rule out inequalities using extra word-dependent information or the exact seed. -/
def UniformSiblingLoss : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ a ∈ Set.Ico (-2 : ℝ) 2,
    (2 - Real.sqrt (2 + a)) * (2 + Real.sqrt (2 + a)) ≤ c * (2 - a)

def iterateSpigot : ℕ → SpigotState → SpigotState
  | 0, s => s
  | n + 1, s => spigotStep (iterateSpigot n s)

/-- Exact positive-width control; its index is zero but it is not the pi initial
state and is not claimed reachable from it. -/
def alternatingSeed (L : ℕ) : SpigotState :=
  ⟨0, 1, (4 : ℤ) ^ (L + 1), 3 * (4 : ℤ) ^ (L + 1), []⟩

/-- Expected true (99%, two-step affine calculation).  Arbitrarily long alternating
prefixes can be emitted without reading an input coefficient, even with p>0.
Thus a bound depending only on the input index, uniform over these states, fails.
This does not refute SpigotEscapeBudget for the particular pi initial state. -/
@[blueprint (title := "Positive-width spigot states can postpone words arbitrarily")]
def PositiveWidthAlternatingPrefix : Prop :=
  ∀ L : ℕ,
    0 < (alternatingSeed L).p ∧ 0 < (alternatingSeed L).q ∧
    (iterateSpigot (2 * L) (alternatingSeed L)).n = 0 ∧
    (iterateSpigot (2 * L) (alternatingSeed L)).output =
      (List.replicate L [0, 1]).flatten

end NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots
