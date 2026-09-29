# DIRECTION — normal-numbers 🧭

## CURRENT DIRECTIVE (altitude laps only write here; it OUTRANKS the HANDOFF) 🧭

**Set 2026-09-29 (review lap 77).**  Supersedes lap 74's directive.  Same destination, same crux;
what changes is the INSTRUMENT, because fact (α)'s one escape hatch is now concretely in reach.

* **Objective.**  Vandehey §7 Problem 1, at the crux: **`OrbitWordBound q r₀ C`**, now in the
  explicit shape `BlockAverageBound` for the sets `mapBlockSet (runState Φ x n) w j`
  (`MapState.orbitWordBound_of_runBlockAverage`, `VandeheyS7RunPin`).  Nothing else counts.

* **NEW — fact (δ), the reason this directive changed.**  Directive fact (α) says only *finiteness
  of the predictor's range* or genuine arithmetic of `Φ` can beat predictability.  The range is
  **precompact**, and both halves are elementary:
  1. **The box lemma.**  `width s = |det s| / (s.d·(s.c+s.d))` exactly.  So `|det| ≤ D`,
     `width ≥ η` and `denRatio := (c+d)/d ∈ [1/K, K]` force `d ≤ √(KD/η)` and `c+d ≤ √(KD/η)`,
     and then `0 ≤ b ≤ d`, `0 ≤ a+b ≤ c+d` put **all four entries in `[−M, M]`,
     `M = √(KD/η)`**.  Compactness needs bounded DISTORTION, not a width floor — lap 74 was
     looking for the floor alone and that is why the search stalled.
  2. **The distortion IS bounded along the run**, by a one-line recursion on `r = denRatio`:
     a read is `r ↦ (r+a)/(r+a−1) = 1 + 1/(r+a−1)`, so after any read `r ∈ (1, 1+1/(r₀+a−1)]`;
     an emission is `r ↦ (mob 1 / mob 0)·r` with `mob 1/mob 0 ∈ [b/(b+1), (b+1)/b] ⊆ [1/2,2]`
     because the image lies in `I_b`.  Reads contract `r` towards `1` *uniformly in the digit*,
     emissions move it by a factor ≤ 2.  So `r` is trapped in an absolute band from step 1 on —
     no hypothesis, no width floor, no normality.
  So: **the reduced states of width ≥ η lie in a fixed compact box of `ℝ⁴`**, hence — up to a
  precision `ρ` costing an additive `O(ρ/η²)` in measure — the predictor `n ↦ s_n⁻¹(I_w)` takes
  **finitely many values**, i.e. `A_n ⊆ E_i^{+ρ'}` for one of `M(η,ρ)` FIXED sets `E_i`.

* **What fact (δ) turns the crux into.**  Not "empirical vs expected for an arbitrary predictable
  family" (hopeless, fact (α)) but: for the finite cell decomposition `{B_i}` of the state box,
  **the joint frequency `freq{n : s_n ∈ B_i ∧ Gⁿx ∈ E_i}` must not exceed `freq{s_n ∈ B_i}·γ(E_i)`
  by more than a constant.**  That is Vandehey's *class equidistribution* with a COMPACT class
  space in place of a finite one — a different and much better-posed wall than the self-joining
  one.  (Dropping the state constraint and summing is NOT allowed: it costs the factor `M`.)

* **Mandated next move**, in this order:
  (a) the **box lemma** and `denRatio`, for `MapState`, unconditional;
  (b) **`denRatio` bounds along `runState`** — the read step, the emit step, the trapped band;
  (c) the **finite-cell approximation**: name `ClassFreqBound` (joint state-cell/cylinder
      frequency) and prove `BlockAverageBound ⟸ ClassFreqBound + width-frequency`;
  (d) only then attack `ClassFreqBound` itself.
  Along the way, the two cheap corrections found this lap: `hΦ` is **trivially** instantiable
  (`MapState` admits `z ↦ v + ε(z−u)`, det `ε ≠ 0`), so lap 76's "next action #1" is a triviality
  and NOT a case analysis on `⌊φ·fract x⌋`; and the `∀ Φ` form of `hBA` should be weakened to the
  `∃ Φ` form before anyone tries to discharge it.

* **Operator check 2026-09-29 12:15 — test `CellMemory` against the Maze BEFORE building on it.**
  `CellMemory` (S7-CM) says the ρ-net cell of the state is decided by the last `L` input digits.
  That is close kin to the refuted window-function frame: `no_window_function` exhibits two states
  of minimal distortion that stay apart after EVERY word, so the far past (the initial state)
  fixes something the recent digits cannot.  Next lap, first move: either prove `CellMemory` is
  not refuted by those witnesses (say exactly why the net cell differs from the emitted digit),
  or refute it in the kernel and add a Maze row.  Guard rule applies.

* **Forbidden drift.**  (i) The window-function frame (`no_window_function`).  (ii) Bounded-error
  decompositions (`cfCount_tendsto_of_decomposition`).  (iii) Serret/commensurator and soft
  self-joining rigidity.  (iv) Finishing `GaussACRigidity` — it stays cited (standing rule 3).
  (v) `StateClock` in the uniform-`η` form.  (vi) **Re-auditing the older `∃`-bundles by hand**;
  the sharper rule (type-pinning is not pinning) is recorded, the front is `runState`-explicit now.

* **What the crux IS, established lap 30 (use this, do not re-derive it).**  Writing the state at
  input time `n` as the Möbius map `s_n = O_n⁻¹ Φ P_n` (`O_n` = emitted convergent matrix, `P_n` =
  input convergent matrix, `Φ` = the affine map), the crux is
  `limsup (1/N) #{n<N : Gⁿx ∈ s_n⁻¹(E)} ≤ C γ(E)` for every cell `E`.  Three facts pin it down:
  1. **(α)** `s_n⁻¹(E)` is **predictable** — determined by `x₁…x_n` — and CF-normality of `x` is a
     statement about the tail marginal alone.  So no argument that uses only "predictable +
     bounded distortion" can work (`exists_predictor_all_hit`).  Only *finiteness of the
     predictor's range* — see fact (δ), which now supplies it — or genuine arithmetic of `Φ`.
  2. **(β)** The per-state distortion bound **fails** at small width: a post-emission state whose
     image `J` straddles `1/k` at a scale far below `|E|` has `γ(s⁻¹E) ≈ 1/2` with `γ(E)`
     arbitrarily small.  This is why no uniform width floor exists; it does NOT obstruct (δ),
     which only needs the width floor on a set of times of frequency `1 − δ`.
  3. **(γ)** `Γ ∩ Φ⁻¹ΓΦ = {±I}` for `Φ = diag(φ,1)` (φ irrational), so the state set is *literally*
     `PSL₂(ℤ)` and the state is the point `ΓΦP_n ∈ Γ\SL₂(ℝ)`.  Fact (δ) is the compatible reading:
     the *matrix* remembers everything (γ), but the *reduced state of width ≥ η* lives in a
     compact box (δ), and only the latter is what the predictor sees.

* **Why.**  Three hypotheses became one (`BlockAverageBound`), and that one is now stated about
  explicitly defined sets.  Fact (α) named the only two ways past it; (δ) delivers the first one
  cheaply, and it is unconditional.  A lap that does not either build (δ)'s machinery or attack
  `ClassFreqBound` is off-directive.

Directive history:
- 2026-09-29 (lap 27, review): window-function frame REFUTED; ε-scheme replaces the bounded-error
  engine; the ERGODIC route (`OrbitACBound` + `GaussACRigidity`) becomes primary, the
  state-indexed decomposition the fallback.
- 2026-09-29 (lap 30, review): leg 1 DISCHARGED (`VandeheyS7Golden`), so the crux is the whole
  chain; crux pinned as the predictable-set/`Γ\SL₂(ℝ)`-translate problem, with facts (α)(β)(γ).
- 2026-09-29 (lap 74, review): crux-neglect corrected; `StateClock`'s uniform width floor
  identified as the wrong shape by fact (β); the MEASURE side of the crux closed by S7-PB.
- 2026-09-29 (lap 77, review): fact (δ) — the reduced state set of width `≥ η` is a COMPACT BOX
  (box lemma + `denRatio` trapped by the read/emit recursion), so fact (α)'s "finiteness of the
  predictor's range" is available; the crux becomes `ClassFreqBound`, class equidistribution over
  a compact class space.

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
