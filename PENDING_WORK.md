# PENDING WORK — the queue

Concrete next moves, cheapest and most clear-cut first.  Front context is in `STATUS.md`.  The
lap-by-lap log from before the 2026-09-27 merge is `archive/PENDING_WORK-to-2026-09-27.md`.
Treadmill laps append dated notes **below the queue**, and a review lap folds them back into it.

## Queue

0. **THE CRUX (binding, see `DIRECTION.md` CURRENT DIRECTIVE) — Vandehey §5–§6, the OUTPUT
   side, in `VandeheyOutputFreq.lean`.**  Decomposition, as fixed by lap 1 of 2026-09-28:
   - ✅ `gaussMeasure_allWordsEvent`, `exists_boundedWords_sum_gt` (the finite digit-truncated
     escape from the infinite CF alphabet — the elementary stand-in for Airey–Mance tightness).
   - ✅ `wCount_le_of_finset` (pointwise split), `eventually_wCount_le` (the upper-bound engine:
     `wCount ≤ (Sb + ε)·n` eventually, for any bound `Sb` on finite length-`m` subfamily mass).
   - ✅ `eventually_le_wCount` (truncation LOWER bound) and **`tendsto_wCount_div`**: for a
     bounded nonnegative weight on the countably infinite length-`m` genuine words, the
     state-restricted count has Cesàro limit `wLimit ν t a m` — defined as a supremum over
     finite subfamilies, so it mentions NO `x`.  That is the published Lemma 4.3's infinite
     case, with no ergodic theory, no Ryll-Nardzewski, no Vitali-Hahn-Saks.
   - ✅ Trigger layer: `fireAt` / `fireTotal` (the untruncated per-position multiplicity, a
     supremum that is ATTAINED because `K` bounds it — `exists_fireAt_eq_fireTotal`),
     `trigCount` (bucketed by length × state) with `trigCount_eq` identifying it with
     `Σ_i fireAt i J`, `trigLimit`, and `tendsto_trigCount_div` (the truncated count converges
     `x`-independently).  Tail layer: `trigPrefix` / `trigInd` / `tailMass`,
     `fireTotal_sub_fireAt_le` (pointwise: a missed trigger forces the window into
     `trigPrefix`), `trigTotal_le_trigCount_add` (aggregate), `wLimit_trigInd_le`.
   - ⬜ **NEXT: close the assembly** (`tendsto_triggerCount`): a trigger family
     `A ⊆ List ℕ × S` with multiplicity `k`, uniform bound `F ≤ K`, bucketed by word length.
     `F − F_{≤m} ≤ K·1_{U_m}`, `U_m ⊆ ⋃_t {i : tᵢ = t, window_m(i) ∈ P_{t,m}}` where `P_{t,m}`
     is the set of length-`m` words agreeing with a trigger of length `> m`.  The ONE honest
     hypothesis is `τ_m := Σ_t ν t·γ(familySetC P_{t,m}) → 0`, i.e.
     `γ(⋂_m familySetC P_{t,m}) = 0`: the triggers decide a.e.  Note `familySetC P_{t,m}` is
     decreasing in `m`, so `τ_m` converges automatically — the hypothesis is only that the
     limit is `0`, which is Vandehey's Lemma 4.3 condition (2) in honest form.
     Conclusion: `(1/n)Σ_{i<n} F(x,i) → Σ_{(q,t)∈A} k(q,t)·ν t·γ(I_q)`, `x`-independent.
   - ⬜ **Then `MobiusCFNScale` needs a per-matrix `vandehey_matrix_action_of_uniformFreq`.**
     The existing one is global (`∀` matrices); the leaf route needs the single-matrix form so
     the either-or endgame can pin `L = γ(I_v)` from a per-matrix uniform-frequency statement.
     Cheap refactor, do it when the assembly lands.
   - ⬜ Only THEN the supply side: `raneyNorm` as a total function, `RaneyState D` as a
     `Fintype`, and the common-target reach (old HANDOFF NEXT 1–3).

1. **Vandehey crux — the single leaf `MobiusCFNScale`** (`VandeheySmith.lean`):
   `x ↦ p·x` preserves CF-normality for prime `p`.  The Smith shortcut WORKED and is formalized
   (`mobiusCFN_of_leaves`), and the Serret leaf is PROVED (`mobiusCFNGL2_holds`), so
   `vandeheyUniformFreq_of_scale` reduces all of Theorem 1.1 to this one statement.
   - **Now under way: Vandehey §2.**  `VandeheyMat2.lean` (the matrix layer, `act_cfMat`) and
     `VandeheyNormalForm.lean` (`M_D`, `isMD_entry_bounds`, `finite_isMD`) are in.  The next
     item is **Lemma 2.1**, `M·J A_j = A_{d₀} J A_{d₁} ⋯ J A_{d_m}·M'` with `M' ∈ M_D` — a
     Euclidean descent, elementary, spelled out in `HANDOFF.md`.
   - The structural insight of 2026-09-28: **the fibre merges by Serret** (`serret_cfEquiv`),
     so class-relative synchronization is a corollary, not a probe observation.
   - After §2: the abstract **output-frequency transfer principle** (Vandehey §5–§6 in
     transducer-free form) — if a finite-state transducer reads the input digits and the joint
     (state, input window) frequencies converge to `x`-independent limits, then every output
     word frequency converges.  That is pure combinatorics; it needs no CF theory and no
     analysis, and it is what turns `tendsto_jointCount_classStep` into digit frequencies of
     `p·x`.  Then §2 (Raney normal forms, finiteness of the det-`±p` state set) and the fibre
     step (state = class × mergeable fibre) remain.
2. **Joint Lambert, unconditional.**  Discharge `AGP` and `PrimeIntervalSupply` from PNT+
   (`WeakPNT_AP`, PNT).  After that, the quantitative §6 count is a separate target.
3. **C3/MRT `CharTailCancellation`.**  This is the only C3 input with a standard-literature proof:
   Euler product, then `L(1,χ) ≫ q^{-1/2}`, then arg-L winding.
4. **Elliott margin check.**  A Littlewood-strength `ζ'/ζ ≪ log t / log log t` would suffice if
   every consumer in `ElliottZetaTheta.lean` tolerates a `log log log` margin.  Check that.  If
   one doesn't, record "Vinogradov or nothing" in the Maze.
5. **SwingC2 triage.**  Delete or restate `tauMomentPrimesShiftStruct_of_primeDensity`, which
   takes the vacuous `PrimeDensityAP`, and `survivorLeaf_of_struct`.

## Lap notes (newest first)

### 2026-09-28 — OPERATOR OBJECTIVE items 1-3, all three landed

1. **`moshchevitinShkredov_cf_false` PROVED** (`MoshchevitinShkredovRefuted.lean`, wired into
   the root import).  Witness `x = [0;1,2,3,…]` from `exists_irrational_mem_iInter_cfCylinder`
   on the nested words `[1,…,s+1]`; `exists_irrational_cfDigit_succ` is the reusable form.
   Strictly increasing digits ⇒ the first letter of a genuine block pins its unique start
   position ⇒ every block occurs at most once ⇒ every frequency is `O(1/p)`, so the criterion's
   hypothesis is vacuous at `σ = 0` while `γ(I_1) = log₂(4/3) > 0`.  Maze:
   `hall_moshchevitin_shkredov_cf_false`.
2. **`conjC3_of_geom_input_band'`** (`C3MrtBlockDefect.lean`) is the C3 headline with `hURM`
   discharged by `uniformResonantMass_holds`.  `C3MrtURMLowHigh.lean` retired as the redundant
   second route: its sorried narrow high range `|t| < 2δ` had no consumer and is removed; its
   sorry-free lemmas stay.  Maze: `hall_urm_low_high_split`.
3. **`exists_jointFreq_limit` retired.**  Its `Synchronizing` hypothesis is unsatisfiable, and
   that is now a THEOREM, not just a probe: `not_synchronizing_of_injective_quotient` — an
   automaton with a quotient on which every letter acts injectively has no synchronizing word.
   For the det-`±D` transducer the quotient is the row-lattice class in `ℙ¹(ℤ/D)` and each
   `B_a ∈ GL₂(ℤ/D)`.  Axiom-free.  Maze: `hall_vandehey_synchronizing_transducer`.  The live
   transfer principle is `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`, whose
   hypothesis `ClassEquidistribution` is now the single crux of the Vandehey front.

### 2026-09-28 lap 1 (review) — the output side opened; crux re-aimed

Reviewed the last three laps: all three had gone into the transducer's *input* side (Raney §2,
the pin, Doeblin) while §4.3/§5/§6 — the piece that decides whether the input side is worth
anything — had never been touched.  Course-corrected in `DIRECTION.md` CURRENT DIRECTIVE.

The structural find that makes §5–§6 elementary: our own
`tendsto_jointCount_of_classEquidistribution` returns the joint (window, state) limit in
**factorized** form `ν t · γ(I_q)`.  Vandehey only has `ρ ≪≫ μ̃` (Remark 3.6) and therefore
needs a genuine measure to get countable additivity; with the product form, countable
additivity reduces to countable additivity of `γ` alone, and the infinite CF alphabet is
escaped by a finite digit-truncated family of mass `> 1 − ε`.  That is also exactly the
tightness patch the published §3 owes and never pays.

Landed in the kernel (`VandeheyOutputFreq.lean`, all `#print axioms`-clean):
`gaussMeasure_allWordsEvent`, `exists_boundedWords_sum_gt`, `wCount_le_of_finset`,
`eventually_wCount_le`, plus the guard-rule quartet for the new `Prop` `JointStateFreq`.

