# Vandehey §7 Problem 1 — the false starts, and where the wall actually is

*Written 2026-09-29 at the close of the §7 campaign (laps 27–91), for the next reader.*
*Companion to `papers/vandehey-2017-open-problem-attack-map.md` (the structural diagnosis) and to
`src/NormalNumbers/Maze.lean` (the machine-checked register — every "kernel witness" named below is
an `alias` there, so it cannot rot silently).*

**The question.** `x` CF-normal, `q, r` quadratic irrationals, `q ≠ 0`: is `qx + r` CF-normal?
Simplest instances `x ↦ φx`, `x ↦ x + φ`.  Open since Vandehey, Compositio 2017, §7 Problem 1.
Frozen in this repo as `vandeheyS7_mul_phi` / `vandeheyS7_add_phi` (`VandeheyS7.lean`).

**The one-line diagnosis.**  Vandehey's Theorem 1.1 (rational Möbius images) rides on a FINITE
transducer state set, which exists because `ℤˣ = {±1}`.  Over `ℤ[φ]` Dirichlet gives infinite units,
the state set is infinite (dense in a compact box), and every route below is an attempt to replace
that finiteness.  None has succeeded; this document says exactly how each failed, so the next
reader does not re-walk them.

---

## 1. The false starts, with their kernel witnesses

| # | The idea (one sentence) | Why it looks promising | The witness that kills it | Maze row |
|---|---|---|---|---|
| 1 | **Serret / commensurator**: make `φ`'s action a tail surgery on CF expansions. | Works for `GL₂(ℤ)` (Serret's theorem), and `det(φ-matrix)` is a unit. | `GL₂(ℤ[φ])` projects DENSELY into `PGL₂(ℝ)` (irreducible lattice in a product), so there is no fundamental domain to push the tail into. | attack-map §1 |
| 2 | **Soft rigidity**: read the problem as a self-joining of the geodesic flow and quote measure rigidity. | The two orbits are genuinely related by a Möbius map. | The joinings in question are NOT of the rigid type: the relevant statements are about pathwise identity, which S7-CN shows is inert here. | attack-map §2 |
| 3 | **Emitted digit as a window function** of a bounded input window. | The transducer's output locally depends on few input digits. | `spread_runWord_le` bounds the image's DIAMETER uniformly in the state, never its LOCATION: two distortion-1 states emit `2` and `4` after reading ANY word. | `hall_emit_digit_window_function` |
| 4 | **Bounded-error decomposition**: image count = finite input-family count `+ O(1)`. | The window function is right off a small exceptional set. | That set has POSITIVE Gauss mass, and a CF-normal input meets it with positive frequency, so the error is `Θ(p)`, never `O(1)`.  The ε-scheme replaces it. | bounded-error row |
| 5 | **Hecke/Fibonacci approximation**: approximate `φ` by `F_{k+1}/F_k` and use the proved rational theorem. | Rational multiples ARE covered by Thm 1.1. | `φ` is the worst-approximable real: matching CF depth `N` costs determinant `e^{Ω(N)}`, so Thm 1.1's automaton has exponentially many states while reading `N` digits. | `hall_hecke_approximation` |
| 6 | **Synchronizing word** for the det-`D` transducer (pathwise state merging). | Standard automata trick; would replace finiteness. | The states fibre over `P¹(ℤ/D)` and every letter acts bijectively on that quotient: no word merges two classes, so the hypothesis is unsatisfiable. | `hall_vandehey_synchronizing_transducer` |
| 7 | **Predictable-hit principle**: perfect marginals forbid landing in your own predicted interval. | Feels like a large-deviation truism. | `u n = n/k` is exactly uniform on `k` cells yet hits `(u_{n−1}, u_{n−1}+δ)` at frequency `(k−1)/k`. | `hall_predictable_from_marginals` |
| 8 | **`TransducerData` bundle** as the front. | Packages the transducer's block structure. | Nothing ties the sets to the state: `S = univ/∅` satisfies it whenever the conclusion holds. | `hall_transducerdata_vacuous` |
| 9 | **`StateData` repair** (pin the sets to a `MobState` family). | "Pin the witnesses" was the right lesson. | Pinning to a TYPE pins nothing: `lowState (Gⁿy/Gⁿx)` interpolates any single pair of points. | `hall_statedata_restatement` |
| 10 | **`StateClock`** at a threshold below the width scale. | Looks like a genuine counting hypothesis. | At `T < 1/η` the whole image sits below `1/T` and the inequality is free. | `hall_stateclock_below_width` |
| 11 | **Diophantine good-denominator detour** for the tail cell `w = []`. | The conversion is unconditional and exact. | The counting input needed is Zaremba-strength FOR ONE REAL `y`, not on average — nobody has it.  (A wall, not an error.) | Diophantine row |
| 12 | **Route B's unweighted cover** of the state-dependent target. | A fixed finite cover would restore finiteness. | State-blind covers have mass `1`; net-indexed covers have mass `γ(I_w)^{-3}`.  The `ℤ[φ]`-separation says this is not a net artefact. | cover row |
| 13 | **`BlockForget`, uniform in the input point.** | The state law is KS-indistinguishable across initial states in probes. | `√2−1` is a Gauss fixed point and the width-`1/3` state `t ↦ 2/(t+2)` runs on it as a 2-cycle emitting `1,4`: a gap `≥ 1/2` for every `T`. | `hall_blockforget_uniform_z` |
| 14 | **`BlockForget` repaired to CF-normal inputs.** | A quadratic irrational is never CF-normal. | The quantifier order is `∃T ∀z`: CF-normality is a tail property, so feed it a CF-normal `z` opening with `T` copies of `2`. | `hall_blockforget_cfnormal` |
| 15 | **The crux as a REDUCTION** (`BlockForgetRun`/`BlockForgetAll`). | It is `x`-free in its first form and probe-green. | The reference run IS the Gauss shift, so the SIGNED crux is the goal, both directions; and `abs_gap_witness` shows the absolute values are not free.  The crux = goal + locality. | `hall_blockforget_is_restatement` |
| 16 | **The §7 scalar debts** (`WidthAfford`, `MeanSlack`, `ClockLinear`). | They look like routine bookkeeping. | They were stated for a transducer THROTTLED to one digit per read; the throttle creates a queue whose `√n` walk makes the wide times have density zero, so `WidthAfford` is false and the width-filtered crux is vacuous on the same run. | `hall_one_digit_throttle` |

---

## 2. What WAS proved, and is reusable

All axiom-clean, all in `src/NormalNumbers/`:

* **The transducer, twice.**  `runState`/`runClock` (S7-RN, throttled) and the **greedy** transducer
  `flushState`/`flushWord`/`grunState` (S7-GR), whose termination comes from the width
  (`width_le_of_emitAcc`) and whose state is REDUCED at every time.
* **Transducer correctness** (S7-GC, `cfDigit_image_eq_gOut`): the greedy output word is a prefix of
  the image's continued fraction — the link the chain had never claimed.
* **The reference run is the Gauss shift** (S7-RR): `pairStep (refState, z) = (refState, gaussMap z)`.
* **The compact box** (S7-BX/S7-PB, fact (δ)): the width-`≥η` states form a compact box, with
  `denRatio` trapped by the read/emit recursion.
* **Distortion ≤ 2** along a run (`distortion_runWord_le_two`), and **loss of memory**
  (`spread_runWord_le`).
* **Relative equidistribution** (S7-RQ): for order-connected `A`, the orbit frequency of
  `I_v ∩ G^{-|v|}A` is `relMass v A`, with no distortion constant.
* **Window frequencies** (S7-WN): CF-normality computes the frequency of every finite-window event
  exactly.
* **Image irrationality** (S7-IN, S7-GD): `Φ.mob x` is irrational, so the frozen targets are not
  vacuous.
* **The architecture** (S7-BF → S7-RV → S7-CO → S7-IM → S7-AW): the crux for every word, and
  nothing else, gives `IsCFNormal (Φ.mob x)` — no `RefCesaro`, no clock hypothesis, no width
  hypothesis.
* **The ledger** (S7-GW, S7-LD2): an emission pays `b²`, a read costs `a(a+1)(r+2+1/r)`, and the
  output stream cannot outgrow the input stream.
* **Pair correlations** (S7-PC): `|γ(I_w ∩ G^{-(|w|+h)}I_w) − γ(I_w)²| ≤ 4(9/10)^h`, plus the thin
  digit tail along a CF-normal orbit.
* **Near-boundary digits** (S7-NB): a point within `w` of `1/(k+1)` has a digit `≥ 1/(4(k+1)²w)`
  within two steps.

## 3. Where the wall actually is

Two equivalent formulations, both reached in lap 91:

1. **Locality.**  The headline is exactly the SIGNED crux (S7-NR).  What the crux adds is that the
   run's window statistics track the input's WINDOW BY WINDOW — local clock regularity plus window
   concentration.  Nothing about global frequencies delivers that.
2. **Joint equidistribution.**  For the greedy run, `width < η` implies the IMAGE's orbit point sits
   within `2η` of a cylinder boundary (S7-GS).  The boundary neighbourhood has measure `≍ √η`
   (S7-SM), and the probe measures the narrow-time frequency at exactly `√η` over five decades.  So
   the remaining scalar obligation is a NO-CONCENTRATION statement about the image orbit — strictly
   weaker than the headline, and the sharpest form the problem has taken here.

The honest summary: the campaign replaced "the state set is infinite" with a precise, quantitative
obstruction — the pair `(state, input point)` must equidistribute, and every attempt to avoid
measuring that pair has either been refuted or shown to be the theorem itself.

## 4. Probes worth re-reading before any new attempt

* `experiments/PROBE-2026-09-29-lap91-stall-and-width-walk.md` — exact `ℤ[φ]` simulation, output
  verified against the true CF of `x/φ`; the throttle/queue diagnosis and the `√η` law.
* `experiments/PROBE-ROUTE-A.md`, `archive/probe/PROBE-2026-08-25-1235-route-a-transducer.md` — the
  state-law measurements that motivated route A.
* `archive/probe/PROBE-2026-09-27-transducer-not-synchronizing.md` — the fibration that kills
  synchronization.
