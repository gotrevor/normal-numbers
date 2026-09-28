# Handoff: the crux input is PROVED — and the capstone's hypothesis shape is refuted

**Date**: 2026-09-28 (lap 4, review) · **Branch**: `wip/g5-prime-subset` · **HEAD**: `6ab5066` ·
`lake build` 🟢 10326 jobs · working tree clean · nothing pushed.

Scope: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`vandeheyUniformFreq_holds`.  **Read `DIRECTION.md` CURRENT DIRECTIVE first — it outranks this
file**, and it was rewritten this lap.  `PENDING_WORK.md` carries both findings in full.

## 🎯 Where the proof stands

    vandehey_matrix_action_holds                      ← Vandehey 2017 Thm 1.1
      ← vandeheyUniformFreq_of_scaleUniformFreq       ✅ VandeheyLeafReduction
      ← ScaleUniformFreq  (x ↦ p·x, prime p)
      ← mobiusUniformFreq_of_transducer               ⚠ VandeheyAssembly — hypothesis shape WRONG
          for the concrete L/R transducer:
            hkK, hK ✅ (lap 3)   hout ✅ (laps 2–3, incl. the run↔CF-digit bijection)
            hjs     🟡 **the crux input is now PROVED for the phase-corrected automaton**
                       (`classEquidistribution_rplusDelta`); what remains is the parity split
                       back to `lrDelta`, and the de-factorization below
            hlen    🟡 no longer an analytic leaf — a corollary of `hjs` (see below)
            hgen, htail ⬜

## ✅ This lap (2 green commits, all `#print axioms`-clean)

`3147723` **`VandeheyRaneyReach.lean` — uniqueness, the involution, the arithmetic core.**
* `Mat2.balanced_decomp_unique` — the Raney (L/R word, balanced matrix) factorization of a
  nonnegative matrix of nonzero determinant is **unique**.  This **pins the
  `Classical.choose`-defined `lrDelta`/`lrOut` for the first time** (`VandeheyLR.lrStep_pin`):
  exhibit any factorization and you have identified the transducer step.  Everything else in
  the file rests on it.
* `det_lrDelta` : `det (lrDelta M j) = − det M`.  **The period-2 obstruction** (below).
* `Mat2.swapRows` (`ι M = J·M`): an involution of the state set with `lrDelta ∘ ι = ι ∘ lrDelta`
  (`lrDelta_swapState`) and `lrOut (ι M) j = (lrOut M j).map not` (`lrOut_swapState`).
* The arithmetic core: `lrDelta M j = [[0,D],[1,0]] ↔ D ∣ a + b·j ∧ D ∣ c + d·j`
  (`lrDelta_eq_zMinus` / `dvd_of_lrDelta_eq_zMinus`); `exists_digit_zMinus` solves the pair over
  `ZMod D` (`D ∣ det M` makes the two congruences equivalent); `eq_zPlus_of_dvd` classifies the
  one exceptional state as `diag(1,D)`; `lrDelta_zPlus`, `lrDelta_zDiag` are its two steps.

`6ab5066` **The reach, and the crux input.**
* `RPlus D` (a `Fintype`), `rplusDelta hD P a := ι (lrDelta hD P a)` — the phase-corrected
  automaton, with `stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)`.
* **`rplus_common_reach`** — every `P ∈ RPlus D` reaches `diag(1,D)` in **exactly 2** genuine
  digits, for every prime `D`.
* **`classEquidistribution_rplusDelta`** — `VandeheyCocycle.ClassEquidistribution (rplusDelta hD) t q`,
  for every prime `D` and every genuine `q`.  **This is the crux input of Theorem 1.1**, for the
  machine that actually computes `x ↦ D·x`.  `tendsto_jointCount_rplusDelta` turns it into the
  `x`-independent joint (window, state) frequency.

## ⚠ The two findings that reshaped the route

**F1 — the Raney automaton is PERIODIC.**  `det (M · B j) = − det M`, so the determinant's sign
is a deterministic period-2 phase; states of opposite phase are never simultaneously occupied,
so NO target is reachable from every state at ONE fixed length.  That is exactly the hypothesis
of `classEquidistribution_of_common_reach`, so the published supply route could never have been
applied to `lrDelta`.  Equivalently `stateHorizonIntegral_pin_of_reach` is FALSE for a periodic
chain.  Probe: `probes/raney_reach.py`.  **Repaired** by the phase quotient above.

**F2 — the capstone's factorized hypothesis is FALSE.**  `mobiusUniformFreq_of_transducer`
assumes `JointStateFreq`: `jointCount/n → ν t · γ(I_q)` with ONE `ν`.
`probes/raney_joint_product.py` (2.1M Gauss-distributed CF digits) shows that at `D = 3` four of
the fourteen Raney states have `ρ(q,t)/γ(I_q)` moving by up to **20 %** across
`q ∈ {[1],[2],[3],[4],[1,1],[1,2],[2,1]}` — ≈15σ, while the other ten are flat to 0.3 %.  At
`D = 2` it DOES factorize, and the reason is visible: there the stationary law is uniform, and a
uniform law is invariant under every individual digit's action.  The Raney digit steps are not
injective, so the state stays correlated with the digits abutting the window.

**The fix is cheap, not fatal.**  Carry Vandehey's un-factorized `ρ : List ℕ → S → ℝ`.  The
escape mass that the factorization was adopted for is recovered for free from

> `ρ(w,t) ≤ γ(I_w)`  (because `jointCount ≤ winCard` at every `n`),

so `Σ_{w ∉ F} ρ(w,t) ≤ 1 − Σ_{w ∈ F} γ(I_w)`, and `exists_boundedWords_sum_gt` (already proved)
supplies `F` with `Σ_F γ(I_w) > 1 − ε`.

## 🎬 Next actions, in order (= `DIRECTION.md` CURRENT DIRECTIVE steps 2–4)

1. **De-factorize the output side.**  In `VandeheyOutputFreq.lean`, replace
   `JointStateFreq δ s₀ ν` by `ρ : List ℕ → S → ℝ` with limit `ρ q t`.  Only ~25 lines mention
   `ν`; the substitution is `ν t * (gaussMeasure (cfCylinder w)).toReal ↦ ρ w t`.  Three places
   need real thought, all easy: `wLimit_set_bddAbove` (the bound becomes `C`, via
   `ρ w t ≤ γ w` and `Σ_Q γ w ≤ 1`), `wLimit_trigInd_le` and `tailMass` (drop the `ν` factor:
   `tailMass k m := Σ_t γ(familySetC (trigPrefix k t m))`).  Add once, up front:
   `jointCount ≤ winCard` and hence `0 ≤ ρ q t ≤ γ(I_q)` from `hjs` + `tendsto_windowFreq`.
   Then restate `mobiusUniformFreq_of_transducer` (`VandeheyAssembly.lean`) and fix
   `VandeheyTrigger.lean`.  Re-do the guard-rule lemmas at the end of `VandeheyOutputFreq.lean`.
2. **`hjs` for `lrDelta` itself, by the parity split.**  `jointCount lrDelta s₀ t q x n` lives on
   ONE parity of `i` (the phase of `t` relative to `s₀`), so it equals
   `½(jointCount rplusDelta … ± Σ_{i<n} (−1)^i 1[window=q] 1[P_i = t])`.  The unsigned half is
   `tendsto_jointCount_rplusDelta` (proved).  **The signed half is FREE from the existing
   two-point machinery**: `VandeheyTwoPoint.abs_integral_devFun_mul_le` bounds an ABSOLUTE
   value, so inserting `(−1)^k` into `devAvg` changes nothing in `integral_devAvg_sq_le`; only
   the final `windowBound`/`localAvg` plumbing has to be re-run with the sign.
3. **`hlen` is then a corollary, not an analytic leaf.**  Vandehey's own §6 proof writes `ℓ(n)`
   as a Birkhoff sum of a BOUNDED window/state function: augment the state with the last emitted
   letter (a finite augmentation), so `numAlt` is additive over blocks with a purely local seam
   term, and `wCount`/`wLimit` evaluates the average.  The lap-3 handoff's cone-perturbation
   route is superseded — it would only give a bounded factor, never convergence.
4. `hgen` (near-free, `patWord_alternation`), `htail` (a cylinder estimate).

## ⚠ Gotchas found this lap

- `Mat2` structure equality: use a local `mat2_ext`; `omega` on component goals needs the `one_a
  … one_d` simp lemmas first, or it leaves `M.a = (1 : Mat2).a` unreduced.
- `linear_combination` is the right tool for the `Mat2` entry identities; `ring` errors with
  "made no progress" on the components that `push_cast` already closed.
- `field_simp` in `ZMod D` leaves `x * (1 + -1) = 0`; follow it with `ring`.
- A `def` whose body goes through `lrDelta` must be `noncomputable`.
- `VandeheyCocycle.ClassEquidistribution` needs `[Nonempty X]` **in the statement**, so a
  `haveI` inside the proof is too late — supply a real instance
  (`instance [Fact (Nat.Prime D)] : Nonempty (RPlus D)`).
- `simpa` will not unfold a subtype projection of a `def`; state the `have` with the unfolded
  type and let defeq do the work.

## 📁 New files this lap

`src/NormalNumbers/VandeheyRaneyReach.lean` (~700 lines, sorry-free) ·
`probes/raney_reach.py`, `probes/raney_quot.py`, `probes/raney_plus.py`,
`probes/raney_joint_product.py`.

---
**→ Next session: NEXT action 1 (de-factorize `JointStateFreq` to `ρ`).  Tree clean at `6ab5066`.**
