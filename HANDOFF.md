# Handoff: the period-2 wall is BROKEN — equidistribution for a periodic automaton

**Date**: 2026-09-28 (lap 5) · **Branch**: `wip/g5-prime-subset` · **HEAD**: `20daa82` ·
`lake build` 🟢 10327 jobs · working tree clean · nothing pushed.

Scope: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`vandeheyUniformFreq_holds`.  **`DIRECTION.md`'s CURRENT DIRECTIVE outranks this file**, but its
lap-4 steps 1–3 are now either DONE or re-aimed by the lap-5 route finding — the full record is
the new top section of `PENDING_WORK.md`.  Read that before touching the supply side.

## 🎯 Where the proof stands

    vandehey_matrix_action_holds                      ← Vandehey 2017 Thm 1.1
      ← vandeheyUniformFreq_of_scaleUniformFreq       ✅ VandeheyLeafReduction
      ← mobiusUniformFreq_of_transducer               ✅ shape now CORRECT (de-factorized, lap 5)
            hkK, hK, hout ✅      hρ : SubWindow ρ ✅ (free)
            hjs  🟡 **the analytic crux is PROVED** (`classEquidistribution_prodStep_of_common_reach`);
                    what remains is the TRANSPORT to `lrDelta` (see NEXT 1) — bookkeeping, not analysis
            hlen 🟡 corollary of `hjs` (lap-4 finding; do NOT use the cone route)
            hgen, htail ⬜

## ✅ This lap (5 green commits, all `#print axioms`-clean)

`39b452f` **De-factorized the whole §4–§6 engine.**  `JointStateFreq δ s₀ ρ` now asks only for an
`x`-independent `ρ q t` (Vandehey's own Remark 3.6 shape).  The product form `ν t · γ(I_q)` that
lap 4 refuted is gone; everything the engine used it for comes from the single new inequality
`SubWindow ρ : 0 ≤ ρ w t ≤ γ(I_w)`, which is FREE for a joint law
(`jointCount_le_winCard` + `tendsto_windowFreq` ⇒ `jointStateFreq_le_gauss`).  `tailMass` lost its
`ν` factor entirely; `wLimit_set_bddAbove` bounds by `C`; guard-rule locator/verdict restated;
`mobiusUniformFreq_of_transducer` restated against `ρ` + `hρ`.

`bb3f047` **Route finding** (`probes/raney_parity_split.py`, 3.5M CF digits, `D = 3`):
* the SIGNED density `(1/n)Σ(−1)^i 1[w_i=q]1[P⁺_i=t]` is **0** (≤0.003 vs a 0.25 signal), so
  `lrDelta`'s joint law is exactly **half** the phase-corrected one;
* the PHASE-CORRECTED law itself does NOT factorize — two `D=3` states split a mass of exactly
  `γ(I_q)/4` `q`-dependently.  So lap 4's F2 is real but is **not** a parity artifact;
* that is consistent with the kernel: `ClassEquidistribution δ t q` binds `L` INSIDE the per-`q`
  statement, so `classEquidistribution_rplusDelta` never claimed a `q`-independent `ν`.
* Hence `hjs` reduces to `ClassEquidistribution` for the **product automaton**
  `prodStep δ := δ × (ε ↦ ε+1)` at `(ι^p t, p)`.  Both obvious routes to that are DEAD: its
  `n`-step kernel is `1[η+n=p]·(c+O(θⁿ))γ`, which oscillates, so there is no pin; and summing the
  signed identity over states gives `0 = o(n)`.

`d7370c4` **Refactor isolating the one analytic input.**  The four two-point masses are named
lemmas (`abs_measure_joint_inter_joint_sub_le` + 3 siblings) instead of `have`s inside
`abs_integral_devFun_mul_le`; `sum_gaussMeasure_windowBound_le_of_variance` and
`classEquidistribution_of_variance` take `∫ devAvg² ≤ V/K` directly (pin versions are wrappers).

`0bd3b6d` + `20daa82` **`VandeheyParity.lean` (~730 lines, sorry-free) — the wall.**
* `jointEvent_prodStep` / `devFun_prodStep`: the product automaton's deviation function is
  `sel η p k · 1[J_k] − L · 1[W_k]` in the ORIGINAL automaton's events.
* **`abs_integral_devFun_prodStep_mul_sub_le`** — with `L := c/2` (half the pin's constant) the
  constant part of the two-point integral cancels EXACTLY; the residue is
  `selSign(k') · altResidue(k)`, a ±1 alternation in the larger index times a function of the
  smaller one, up to `2(C+1)ρⁿ`.
* `abs_sum_selSign_le`: the ±1 sign sums to `O(1)` over ANY contiguous range.
* **`integral_devAvg_prodStep_sq_le`** — `∫ devAvg² ≤ (2+B₀)/K` for the PERIODIC automaton: in the
  double sum the mean part is `Σ_k R k · Σ_{k'∈Ico (k+|q|) K} selSign k'` (plus its `sum_comm`
  mirror), so it contributes `O(K)`, not `O(K²)`.  **The alternation performs the cancellation the
  pin would have performed termwise.**  The error part reuses `sum_gap_majorant_le` unchanged.
* **`classEquidistribution_prodStep_of_common_reach`** — for any automaton with a uniform common
  reach (e.g. `rplusDelta`, `VandeheyLR.rplus_common_reach`), the window frequency of a genuine `q`
  restricted to ONE PARITY CLASS of positions, jointly with the state, equidistributes along EVERY
  CF-normal orbit, with reference weight `c/2`.

## 🎬 Next actions, in order

1. **Transport to `lrDelta`** (new file importing `VandeheyParity` + `VandeheyRaneyReach`).  With
   `s₀ := diag(D,1) ∈ RPlus D` and `stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)`:
   `1[stateAt lrDelta … i = t] = 1[P⁺_i = ι^i t]`, and `det` forces the parity, so
   > `jointCount lrDelta s₀ t q x n = jointCount (prodStep rplusDelta) (s₀,0) (t⁺,p) q x n`,
   > `(t⁺,p) = (t,0)` if `det t = +D`, `(ι t, 1)` if `det t = −D`.
   Then `tendsto_jointCount_of_classEquidistribution` on `prodStep rplusDelta` gives
   `JointStateFreq lrDelta s₀ ρ` with `ρ q t := L(q,t)·γ(I_q)`, and `hρ : SubWindow ρ` from
   `jointStateFreq_le_gauss` (plus `ρ [] t ≤ 1`, i.e. `γ(cfCylinder []) = 1`).
   Subtype gymnastics (`RState D` vs `RPlus D`) is the only real work.
2. `hlen` as a corollary of `hjs` (augment the state with the last emitted letter → `numAlt` is a
   Birkhoff sum of a bounded window/state function; `wCount`/`wLimit` evaluates it).
3. `hgen` (near-free, `patWord_alternation`), `htail` (a cylinder estimate).
4. Only then the `PrimeIntervalSupply` side item of the operator objective.

## ⚠ Gotchas found this lap

- `set x := e with h` gives `h : x = e`; a metavariable target (`classEquidistribution_of_variance`'s
  implicit `c`) makes side-goal `by linarith` fail — pass `(c := …) (V := …)` explicitly.
- `div_le_div_of_nonneg_right` in this mathlib pin wants `0 ≤ denom`, not `0 <`.
- `omit [DecidableEq S] in` must precede the docstring, not sit between it and the `lemma`.
- A lemma with `[DecidableEq S]` cannot be used inside a lemma that `omit`s it.
- `integral_add` needs explicit `(f := …) (g := …)` or it unifies against `+` of functions.
- `nlinarith` in a context with a dozen `set`s times out: use `mul_le_one₀` and explicit `calc`.
- `Finset.sum_comm` alpha-renames for free; `rw [Finset.sum_mul, ← Finset.sum_filter]` turns an
  `if`-sum into `(filtered sum) * const`.

## 📁 Files

New: `src/NormalNumbers/VandeheyParity.lean`, `probes/raney_parity_split.py`.
Changed: `VandeheyOutputFreq.lean`, `VandeheyAssembly.lean`, `VandeheyTwoPoint.lean`,
`VandeheyClassEquidist.lean`, `src/NormalNumbers.lean`, `PENDING_WORK.md`.

---
**→ Next session: NEXT action 1 (transport the parity joint count to `lrDelta`).  Tree clean at
`20daa82`.**
