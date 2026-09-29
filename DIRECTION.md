# DIRECTION — normal-numbers 🧭

## CURRENT DIRECTIVE (altitude laps only write here; it OUTRANKS the HANDOFF) 🧭

**Set 2026-09-29 (review lap 30).**  Supersedes lap 27's directive; the route is UNCHANGED, the
crux has moved one step in and leg 1 is now a theorem.

* **Objective.**  Vandehey §7 Problem 1, at the crux: **`OrbitCellBound q r₀ C`**
  (`VandeheyS7Cell`).  Nothing else on this front counts as progress.
* **State of the chain (lap 30).**  `vandeheyS7_mul_phi_of_orbitCellBound` /
  `vandeheyS7_add_phi_of_orbitCellBound` (`VandeheyS7Golden`, axiom-clean) prove the frozen
  targets from exactly TWO hypotheses: the cited `GaussACRigidity (C/log 2)` and the crux.
  Leg 1 (`AffineImageIrrational`) is DISCHARGED for both instances.  `CellCover (1/log 2)` is
  proved.  So every remaining line of the route runs through `OrbitCellBound`.
* **Mandated next move.**  Attack `OrbitCellBound` **only**, and prefer moves that either
  (a) prove an unconditional statement about the image expansion of a CF-normal `x`, or
  (b) kill a candidate sub-route with a theorem (a refutation with a Lean witness is an advance).
  `GaussACRigidity` **stays a cited hypothesis** — do not resume `GaussKB.lean` (lap 28 spent a
  lap there against lap 27's directive; that must not recur).
* **What the crux IS, established lap 30 (use this, do not re-derive it).**  Writing the state at
  input time `n` as the Möbius map `s_n = O_n⁻¹ Φ P_n` (`O_n` = emitted convergent matrix, `P_n` =
  input convergent matrix, `Φ` = the affine map), the crux is
  `limsup (1/N) #{n<N : Gⁿx ∈ s_n⁻¹(E)} ≤ C γ(E)` for every cell `E`.  Three facts pin it down:
  1. `s_n⁻¹(E)` is **predictable** — determined by `x₁…x_n` — and CF-normality of `x` is a
     statement about the tail marginal alone.  So no argument that uses only "predictable +
     bounded distortion" can work.
  2. The per-state distortion bound **fails**: a post-emission state whose image `J` straddles
     `1/k` at a scale far below `|E|` has `γ(s⁻¹E) ≈ 1/2` with `γ(E)` arbitrarily small.  The cell
     threshold `T` is what such states produce (a huge output digit), so the crux's own `w = []`
     tail-cell case is the tightness statement that must control them — a bootstrap, not a
     bypass.
  3. `Γ ∩ Φ⁻¹ΓΦ = {±I}` for `Φ = diag(φ,1)` (φ irrational), so the state set is *literally*
     `PSL₂(ℤ)` and the state is the point `ΓΦP_n ∈ Γ\SL₂(ℝ)`.  This is the structural reason
     behind `no_window_function` and `infinite_zPhi_abs_le_one`, and it identifies the crux with
     "the ray `Γ g_x(t)` equidistributes ⟹ so does `Γ Φ g_x(t)`" — the self-joining wall.  Do not
     re-attack the wall softly; attack the ARITHMETIC of `Φ`.
* **Forbidden drift.**  (i) The window-function frame — `no_window_function` refutes it in the
  kernel; `spread_runWord_le`/`hdist_runWord_le` bound the image DIAMETER, never its LOCATION.
  (ii) Bounded-error decompositions (`cfCount_tendsto_of_decomposition`): the exceptional set has
  positive Gauss mass, so the error is `Θ(p)`.  (iii) Serret/commensurator and soft self-joining
  rigidity.  (iv) Finishing `GaussACRigidity`.
* **Why.**  Leg 1 and the geometry are done; the chain is two hypotheses wide and one of them is
  cited by standing rule 3.  Every further lap that does not touch `OrbitCellBound` is leaf work.

Directive history:
- 2026-09-29 (lap 27, review): window-function frame REFUTED; ε-scheme replaces the bounded-error
  engine; the ERGODIC route (`OrbitACBound` + `GaussACRigidity`) becomes primary, the
  state-indexed decomposition the fallback.
- 2026-09-29 (lap 30, review): leg 1 DISCHARGED (`VandeheyS7Golden`), so the crux is the whole
  chain; crux pinned as the predictable-set/`Γ\SL₂(ℝ)`-translate problem, with the three facts
  above written into the directive so grind laps stop re-deriving them.


## OPERATOR OBJECTIVE 2026-09-29: Vandehey §7 Problem 1 🌙

**Target (open, Vandehey Compositio 2017 §7 Problem 1):** if `x` is CF-normal, is `φx` CF-normal?
Is `x + φ`?  Moonshot lane: the objective is a conjecture graph, not "prove X".  There is no
stop condition beyond the lap cap; a refutation of a route is an advance, and a lap succeeds by
advancing the crux, not by sorry count.

**Read first:** `papers/vandehey-2017-open-problem-attack-map.md` (§1 diagnosis, §2 dead ends,
§3 Route A with the three 2026-08-24 corrections), `experiments/PROBE-ROUTE-A.md`,
`archive/probe/PROBE-2026-08-25-1235-route-a-transducer.md`, and the Maze.  Serret/commensurator
and soft rigidity (self-joinings of geodesic flow) are dead; do not relitigate them.

**Graph to build:**
1. **Frozen targets.**  A new module `VandeheyS7.lean` (in the root import) stating
   `vandeheyS7_mul_phi : ∀ x, IsCFNormal (Int.fract x) → IsCFNormal (Int.fract (goldenRatio * x))`
   and `vandeheyS7_add_phi` (for `x + φ`), plus the general quadratic-irrational form as a Prop.
   These are open statements: `sorry`-free is not expected, and they are never weakened.
   Record the frozen names and commit in `HANDOFF.md`.
2. **The obstruction, as Lean.**  The Thm 1.1 pipeline (Raney normal form → transducer → class
   equidistribution → run clock, `VandeheyCapstone.lean`) needs a finite state set.  State as
   Props, with probes, where it breaks over `ℤ[φ]`: unit drift makes the reachable state set
   infinite; pathwise merging is impossible (`M⁻¹VM` integral forces `V` diagonal for
   `M = diag(φ,1)`); Lemma 2.2's bounded burst fails (`burst ≤ C + log(1+a)/Lévy` instead).
   Prove what is provable (infinitude of the state set, the non-merging fact) and add Maze rows.
3. **Route A: replace finiteness.**  The dynamics read only the real place.  Candidate nodes:
   a bounded-distortion window lemma for reduced post-emission states (the compact analogue of
   `entries ≤ D`; the integer descent does NOT port), a distributional merging statement
   (Birkhoff–Hopf cone contraction, not coupling), trigger windows with `ρ(∂U) = 0` in place of
   trigger strings, and the endgame either-or trick (verbatim for any `M`, so the problem reduces
   to "every string has a limiting frequency in `φx`, independent of the CF-normal `x`").  Wire
   each node to the frozen target by a theorem, even a conditional one.
4. **Reuse before rebuild.**  Factor the Thm 1.1 pipeline so its finite-state step is a named
   hypothesis; the new work supplies a compact-fiber substitute for that hypothesis.

Guard rule applies to every new Prop (content locator + degenerate cases).  A Prop that turns
out false goes in the Maze with its refutation, never silently weakened.

**Lap 1 side items (cheap, do first):** SwingC2 triage and the OVERVIEW refresh (Vandehey 1.1
proved, joint Lambert rests on AGP alone) from `PENDING_WORK.md`; prune them from the queue when
done.

---

Open fronts: `STATUS.md`.  Queue: `PENDING_WORK.md`.

Completed runs (the directive text is in git history, the outcome in `STATUS.md`):
- 2026-09-28 (a): Moshchevitin–Shkredov refuted; C3 headline without `hURM`; Vandehey automaton
  hypothesis refuted.
- 2026-09-28 (b)+(c): **Vandehey 2017 Thm 1.1 proved** (`vandehey_matrix_action_holds`, `6d7a8ad`).
- 2026-09-28 (joint Lambert inputs): `PrimeIntervalSupply` proved (`3ddc0b6`); AGP gap mapped
  (`docs/JOINT-LAMBERT-AGP-GAP.md`).

The pre-merge directive history is in `archive/DIRECTION-to-2026-09-27.md`.

## Standing rules (bind every lap)

1. **Guard rule.**  A lap may not hand the chain a new `Prop` unless the same lap also lands, in
   the kernel:
   - a *content locator*: the trivial or extremal instance, which shows where the content is not;
   - a *degenerate-case verdict* for the empty, singleton, truncated/boundary and
     constant-function configurations.
   A reduction without both is not an advance.  This rule was installed at C3/MRT lap 115, after
   laps 112-114 "reduced" the debt to statements that were false: a stronger statement looks
   cleaner and dies on a singleton block.
2. **Refutations are progress, and are recorded as Lean data.**  Every walked dead end gets a row
   in `src/NormalNumbers/Maze.lean`, aliased onto the refuting theorem.  Read the Maze before
   proposing a route.
3. **Literature inputs are named hypothesis `Prop`s**: cited, faithful or weaker, never `axiom`.
   **New math comes first.**  A literature input stays assumed until a new result needs it
   discharged; then proving it is a side quest (Philipp and Wall were proved this way).
4. **Frozen statements stay byte-identical.**  A campaign's ratified headline and its frozen
   modules are pinned by commit in that campaign's kickoff.  Statement freezing is JUDGE-owned
   (`JUDGE.md`).
5. **A false contract is recorded as an obstruction, never silently weakened.**
6. **Every new module goes in the root import** (`src/NormalNumbers.lean`), so `lake build`
   covers it.

## Standing charter (destination)

The project harvests the digit-reading dynamics of real numbers: normality, disjunctivity,
continued-fraction normality, and the richness of arithmetic constants such as `∑ ω(n)/bⁿ`.
Moonshot lane: aim at the open conjectures (C1-C3 of the casting-out programme, Vandehey's
open problem), and treat a conditional theorem on an honestly labelled literature input as a
real advance.
