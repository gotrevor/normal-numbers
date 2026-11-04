# Invention pass: no candidate admitted

Outcome: **zero viable new mechanisms** from this pass.  No proof treadmills or
digit sweeps were launched.  This does not establish that no mechanism exists.
The six retired routes remain retired.  The three entries added to the Maze are
screening failures, not a third campaign advertised as three new routes.

The controls are in
`src/NormalNumbers/PiDisjunctiveRoutes/InventionScreen.lean`.  They are elementary
checks of proposed proof steps, not advances on pi's digit distribution and not
claims of mathematical novelty.  The search was local: the Maze, prior pi notes,
`BBPSpan`, `MasterConjectures`, and the disjunctivity definitions.  No internet
search was used or needed.

## 1. Borrow distribution from rational approximants

**Attempt.** Use rational approximants p/q to pi whose denominators have a long
multiplicative orbit under 2.  If 2 is primitive modulo q, a full orbit visits all
nonzero residues.  Could that arithmetic supply the missing word visits, without
assuming random digits of pi?

**The budget.** The ordinary absolute-error transport through T shifts needs
`2^T |pi-p/q|` small, with an additional margin for the desired word cylinder.
Even the weaker threshold `<1` is incompatible with a lower bound
`|pi-p/q| >= c/q^mu` once `q^mu <= c*2^T`.
`not_absoluteShadowBudget_of_lower_bound` proves precisely this implication.
The approximation lower bound is a hypothesis; no numerical irrationality measure
for pi is silently imported.

**Control.** `not_quadraticAccuracyFullPeriodTransfer` uses q=11, p=1 and
x=1/11+1/121.  Quadratic accuracy holds, but the ten-shift error exceeds one.
`denominator_eleven_full_period` checks that 2 really has order 10 modulo 11.
`shadow_scale_controls` checks opposite sides of the budget at q=101 and
illustrative exponent 8.  These are exact rational controls, not pi experiments.

**What would rescue it.** Find the required word early in an approximant's orbit,
inside its actual accuracy horizon, using arithmetic of the specific numerators.
Complete-period cancellation gives no such location.  I did not find a mechanism
for that short-window estimate.  A new approximation formula alone would repeat
the old pattern.  This screen does not rule out proximity modulo one when the
absolute-error certificate fails, or prove that the actual digits disagree.

## 2. Turn a forbidden-word automaton into a functional equation

**Attempt.** Suppose pi avoids a word.  Its digits then follow a finite directed
graph.  Could the graph supply a finite functional system for the digit generating
series, which could then be compared with the analytic identity defining pi?
The attraction is that the proposed input would be finite algebraic data rather
than a table of pi's digits.

**Failure at the first step.** A graph recognizing allowed words leaves the choice
of an infinite path unspecified.  Insert an arbitrary binary sequence in the even
positions and zeros in the odd positions: every resulting stream avoids 11.
`not_countableAvoiderCatalogue` diagonalizes against **any** countable catalogue
of streams.  In particular, restricting to an enumerated collection of finite
descriptions cannot account for all such paths.

A transition matrix can describe the language or sums over paths.  It does not
give the chosen path a finite generator.  I found no extra arithmetic rigidity
that pi would supply here.  Such a rigidity statement would be the real new
input; the forbidden-word hypothesis alone cannot supply it.  The theorem is
about streams and makes no assertion that pi itself is or is not automatic.
In particular, pi's computability is an additional restriction that this
cardinality argument does not exploit.  The rejection is of the unrestricted
recognizer-to-generator step, not of every arithmetic selection argument.

## 3. Deform the constant, prove an average, specialize back to pi

**Attempt.** Embed a pi-producing series or integral in an analytic parameter
family.  Average word-hit statistics over the parameter, then use the family's
analytic structure to control its distinguished pi-producing value.  This seeks
an analytic source of cancellation rather than a new exact digit recurrence.

**Failure of the proposed specialization.** Small average and analytic form do
not provide the needed pointwise estimate.  `polynomial_spike_control` gives
height one and integral 1/(n+1); `not_uniformPolynomialEndpointBound` refutes a
uniform endpoint-by-mass constant for nonnegative polynomials.
`gaussian_spike_control` gives a two-sided control: for every epsilon>0 a positive
Gaussian has total integral epsilon but value one at zero.  Its distinguished
point is interior, so moving away from an endpoint does not remove the issue.

To proceed one would need a quantitative extraction estimate controlling the
increasing concentration of digit observables, with its derivative or localization
cost included.  I found no estimate at the pi-producing parameter that beats
that cost.  The controls do not refute all parameter-family arguments or estimates
with stronger hypotheses.  Generic behavior alone does not finish the argument.

## Decision

None passes the admission test: an explicit new estimate, a reason it holds for
pi, and a discriminating control that the proposed mechanism survives.  All
three attempts stalled before a pi-specific estimate.  The formal controls make
the missing steps visible; they are not a reason to spend another proof lap.

Reopening requires the respective short-window arithmetic estimate, path-selection
rigidity, or quantitative specialization argument.  Merely restating the desired
digit property in one of those forms does not qualify.  We have not assigned
numerical success probabilities or claimed an exhaustive search of possible ideas.
