# HANDOFF 2026-09-16 — deep reflection lap: §4C for the `a`-side is PROVED

Branch `wip/g5-prime-subset`, `lake build` 🟢 **9086 jobs**, tree clean.
`src/` = the two pre-expedition forbidden-drift `sorry`s; **zero `axiom`s**.

**Read `DIRECTION.md` → CURRENT DIRECTIVE first** — it was re-set this lap and it OUTRANKS this
handoff.  The reasoning is in `REFLECTION-2026-09-16-campaignB.md`.

## The governance change (do not lose this)

Campaign B's `c` axis and subset axis are closed.  The `a`-side is now the campaign's
**TERMINAL** objective and there is a **pre-registered FINISH LINE**: when `isDisjunctive_weightA`
and its audit theorem are proved, the campaign is COMPLETE — do **not** open a successor by
re-parametrizing again.  One permitted stretch only (the general additive function).  The
diagnosed risk on this project is *scope creep*, not a false summit: a machine that works always
has one more parameter to widen, and B4/B5-shaped laps (growth-class bookkeeping) are now
explicitly forbidden drift.

## Proved this lap — `src/NormalNumbers/G4PhaseA.lean` (new)

All `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

| declaration | content |
|---|---|
| `omegaOnA a sm m` | the `a`-weighted small-prime count `∑_{p∈sm, p∣m} a_p`; `omegaOnA_one` = `omegaOn`, `omegaOnA_indicator` = `omegaOn (sm.filter S)` |
| `totalPhaseA`, **`phaseA_eq_sum_local`** | `Φ_a(n) = ∑_{p∈sm} localPhase p ρ (a_p·x) n` — the local phase at `p` is the **ordinary** one at *scaled* coefficients |
| `shiftPhaseA`, **`shiftPhaseA_roots`** | the per-prime `LocalPhase`; its roots are `image (root p ρ)`, so **the four §4C error terms are identical to the unweighted ones** |
| **`norm_sampleAvg_ee_phaseA_le`** | §4C for the `a`-weighted phase sum, via `norm_sampleAvg_prod_ee_le` with the per-prime seed `if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0` |
| `vecMul_const_mul`, `coeffAL_const_mul` | `coeffAL` is **linear in the frequency** |
| **`sum_sq_distZ_coeffA_ge_gen`** | the decisive one: `freqSeed bb K ≤ ∑_i distZ(a_p·coeffAL bb q i)²` for `1 ≤ a_p ≤ Ca`, given `N ≥ 1 + ⌈log_bb(2^K·Ca·D)⌉`.  **The seed is unchanged.** |
| `SvalA`(+`_one`), `sum_mul_SvalA`, `torusChar_SvalA`, `sum_sq_distZ_coeffA_ge_of_bound` | the concrete grid vector and its character identity |
| **`norm_sampleAvg_torusChar_SvalA_le`** | §4C for the grid's `a`-weighted vector — same shape, same error terms, as `norm_sampleAvg_torusChar_Sval_le` |

### Why it was cheap (the structural reason, worth keeping)

A priori the rescaling could have destroyed the good-prime gain outright: `dist(k·x, ℤ)` can
vanish while `dist(x, ℤ) > 0`.  It does not, because

* `coeffAL` is linear in `q`, so scaling the *coefficients* by `a_p` = scaling the *frequency*
  by `a_p`; and
* `sum_sq_distZ_freqDepthB_ge` has **no hypothesis on the Fourier box at all** — it holds for an
  arbitrary nonzero integer frequency.  The box `D` enters the separation argument only through
  `freqDepthB_le`, i.e. only through the *admissibility* of the selected depth inside the layer
  budget `N`.

So the entire cost of a general bounded `a` is one **additive** `⌈log_bb Ca⌉` on a layer budget
already of size `Θ(K)`.

## Next, in order (steps 3–4 of the directive's ladder)

3. **The schedule's layer budget**: `N ≥ 1 + clog bb (2^K * (Ca * D))`.  `Ca` is a fixed constant
   and `k₄`/`N` are chosen after it, exactly as `C` was in B2e.
   🚦 **Trigger**: if some schedule quantity is capped *from above* by `N` in a way that
   `⌈log_bb Ca⌉` breaks — the moment cap `Mc ≤ 2^{m₂}` of
   `DESIGN-2026-09-16-prime-subset.md` §3 is the one to watch — that is a **proved obstruction**:
   write it into the DESIGN file and the headline stays what is already proved.
4. **§4D + assembly** at the active set `S = {p : 1 ≤ a_p}`.  **Architecture (binding)**:
   `omegaOnA 1_S sm m = omegaOn (sm.filter S) m`, so the prime-subset campaign *is* the `a`-side
   at `a = 1_S` — generalize `G4SubsetC*` **in place**.  Do **not** build a fifth parallel §4D
   stack; four already exist (`G4Remainder*`, `G4SubsetJunk`, `G4Unbounded*`, `G4SubsetC*`).
   Then the audit theorem in `G4WeightStatement`.

`PENDING_WORK.md` §B6 carries the same in table form.
