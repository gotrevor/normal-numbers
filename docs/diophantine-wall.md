# The Diophantine wall: one wall, two doors 🧱

2026-08-29.  Companion to `src/NormalNumbers/DiophantineWall.lean` and, across the street,
`collatz-moonshot`'s `FrontA/PowSeparation.lean`.  Both repos' deepest open inputs are effective
lower bounds on linear forms in `{log 2, log 3, 1}` - but they knock at the wall in **different
coefficient regimes**, and the regime determines which classical tools bite.  This map is the
architecture; the interface theorems make each door consumable with zero repo context.

## The two doors

| | normal-numbers (`LnTwoDyadicSep`) | collatz-moonshot (`sep_two_three`) |
|---|---|---|
| object | `\|ln 2 · 2ⁿ − p\|`, `p ∈ ℤ` | `\|m·log 2 − k·log 3\|`, near-critical |
| coefficients | **exponential** (`2ⁿ`) | **polynomial** (`m, k ~ k`) |
| needs | Tier 1: `≥ 2^(−βn)`; Tier 2: `≥ n^(−C)` | `≥ 2^(−k/3)` (subexponential suffices) |
| classical status | Tier 1 = irrationality measure (Marcovecchio μ ≤ 3.5746, citable); Tier 2 = **Mahler-class open** | Gelfond 1935 / Rhin 1987 (citable); any finite measure suffices |
| interface | `lnTwoDyadicSep_iff_int` (pure: no orbit language) | `sep_of_linear_form` / `sep_of_uniform_measure` (pure ℕ) |
| consumer | run bounds for binary ln 2 (`dyadicSep_run_bound`) | two-block exclusion → `NoDivergentOrbit` front |

## Regime facts worth carrying

- **In the exponential-coefficient regime, the irrationality measure beats Baker.**  Baker-type
  two-log bounds give `exp(−C·log b₁·log b₂) ≈ exp(−C n²)` for coefficients `(2ⁿ, p)` - *worse*
  than the trivial-looking measure route `|ln 2 − p/2ⁿ| ≥ c/2^(μn)` ⇒ `≥ 2^(−(μ−1)n)`.  The
  measure is the right tool for Tier 1; Baker is the right tool for the moonshot door.
- **Neither door's needed strength is the classical theorem's full strength.**  Moonshot needs
  only subexponential (any finite measure); NN Tier 1 needs only *some* finite `β`.  Both are
  strictly-weaker-than-frontier asks - the wall doc's standing question is how weak an input
  each front can survive on.
- **NN Tier 2 (`LnTwoPolySep`) is the one genuinely open door**: polynomial floors at
  exponential coefficients, the `‖(3/2)ⁿ‖` family.  No known technique; the graph treats it as
  a sink-adjacent open node, not a target.

## Shared discharge routes

1. **Shifted-Legendre / Alladi-Robinson** (single kernel, `a = −1`): gives `μ(ln 2) ≤ 4.622` ⇒
   Tier 1 at `β ≈ 3.63`.  The integer linear form, non-vanishing, and `(1/5)ⁿ` remainder are
   already formalized in collatz-moonshot `FrontA/Legendre.lean` (which proved single-kernel
   caps at `log 2` - exactly this door's constant).  One construction, both repos benefit:
   moonshot gets its warm-up leg, NN gets Tier 1.  *Lane-2 work when scheduled; discharges the
   node `LnTwoExpSep`.*
2. **Two-kernel Rhin** (moonshot leg 3): simultaneous `{1, log 2, log 3}` measure - discharges
   the moonshot door AND (a fortiori, restricted) Tier 1.
3. **Citation axioms** (BASELINE per moonshot doctrine): Marcovecchio for NN, Rhin for
   moonshot - honest, disclosed, does not clear GO gates.

## Graph bookkeeping

Nodes: `LnTwoExpSep` 🟡 (citable), `LnTwoPolySep` 🔴 (open), `SliverEscape` 🔵 (new family,
`KickDynamics.lean` - probe-supported; ⚠️ its former "no Diophantine input" tag is retired:
the 2026-08-29 lattice dig showed the run-window content of the kick family is Diophantine),
`LnTwoLatticeAvoid` ⚪ (`LnTwoLattice.lean` - **costume-refuted as a new rung the day it was
frozen**: `latticeAvoid_of_dyadicSep` / `dyadicSep_of_latticeAvoid` prove it ⟺ dyadic
separation at rate `2^(−g n)`, so at `g = 2n+2` it is `μ(ln 2) ≤ 3` territory; kept for its
certificate form `zeroRun_res_eq_ceil` - the run event as one integer identity per `n` - and
the congruence attack surface on the explicit numerator `lnTwoNum`, e.g. the Fermat-quotient
bridge `A_{p−1} ≡ unit·q_p(2) (mod p)` at `n = p−1`, `docs/lit-sweep-2026-08-29.md`).  **Costume check (2026-08-29,
analytic): `SliverEscape` is NOT `LnTwoPolySep` in disguise.**  A sliver ride certifies only
`‖2^(n+j)·ln 2‖ ≤ 1/(n+j+1)` at each ride step - log-precision closeness, far above PolySep's
`n^(−C)` floor - so PolySep does not forbid long rides (no PolySep ⇒ SliverEscape), and a ride
does not produce PolySep-scale smallness (no SliverEscape-failure ⇒ PolySep-failure).  The two
constrain different scales: PolySep bounds the *depth* of a single approach, SliverEscape the
*duration* of coarse closeness.  Both directions genuinely open; the node stands on its own.  Edges proved 2026-08-29: `lnTwoDyadicSep_iff_int` (the wall
door), `dyadicSep_run_bound` / `run_le_of_expSep` / `run_le_of_polySep` (tiers → runs),
`zeroRun_le_of_sliverEscape` (sliver node → runs), gates `kick_floor` / `top_gate`
(unconditional phase-space structure).
