# HANDOFF 2026-09-16 — deep reflection lap: §4C for the `a`-side is PROVED, through the frame

Branch `wip/g5-prime-subset`, HEAD `e26ade6`, tree **clean**, `lake build` 🟢 **9087 jobs**.
`src/` = the two pre-expedition forbidden-drift `sorry`s; **zero `axiom`s**.

> **Read `DIRECTION.md` → CURRENT DIRECTIVE first.**  It was re-set by this (altitude) lap and it
> OUTRANKS this handoff.  Full reasoning: `REFLECTION-2026-09-16-campaignB.md`.
> Supersedes `HANDOFF-2026-09-16-aside-4C.md` (same lap, earlier checkpoint).

## The governance change — do not lose this

Campaign B's `c` axis and subset axis are **closed**.  The `a`-side is now the campaign's
**TERMINAL** objective and there is a **pre-registered FINISH LINE**: once `isDisjunctive_weightA`
and its audit theorem are proved and trust-triple clean, the campaign is COMPLETE.  Do **not**
open a successor campaign by re-parametrizing again.  One permitted stretch only (the general
additive function, see the directive).

Diagnosed risk on this project: **scope creep, not a false summit**.  Two campaigns closed in a
day; B0–B3 attacked the machine but B4/B5 were growth-class bookkeeping plus an audit surface.
B4-shaped laps — widening an exponent against an unchanged budget — are now forbidden drift.

ROUTE VERDICT: **CONTINUE**.  No registered trigger fired.

## Proved this lap — all `#print axioms` = `[propext, Classical.choice, Quot.sound]`

### `src/NormalNumbers/G4PhaseA.lean` (new) — §4C for the `a`-weighted vector

| declaration | content |
|---|---|
| `omegaOnA a sm m` | `∑_{p∈sm, p∣m} a_p`; `omegaOnA_one` = `omegaOn sm`, `omegaOnA_indicator` = `omegaOn (sm.filter S)` |
| `totalPhaseA`, **`phaseA_eq_sum_local`** | `Φ_a(n) = ∑_{p∈sm} localPhase p ρ (a_p·x) n` — the local phase at `p` is the **ordinary** one at *scaled* coefficients |
| `shiftPhaseA`, **`shiftPhaseA_roots`** | the roots are `image (root p ρ)`, so **the four §4C error terms never see `a`** |
| **`norm_sampleAvg_ee_phaseA_le`** | §4C for the `a`-weighted phase sum, via `norm_sampleAvg_prod_ee_le` with the per-prime seed `if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0` |
| `vecMul_const_mul`, `coeffAL_const_mul` | `coeffAL` is **linear in the frequency** |
| **`sum_sq_distZ_coeffA_ge_gen`** | `freqSeed bb K ≤ ∑_i distZ(a_p·coeffAL bb q i)²` for `1 ≤ a_p ≤ Ca`, given `N ≥ 1 + ⌈log_bb(2^K·Ca·D)⌉`.  **The seed is unchanged.** |
| `SvalA`(+`_one`), `sum_mul_SvalA`, `torusChar_SvalA`, `sum_sq_distZ_coeffA_ge_of_bound`, **`norm_sampleAvg_torusChar_SvalA_le`** | the concrete grid vector, its character identity, and §4C for it |

### `src/NormalNumbers/G4FrameA.lean` (new) — the frame layer

| declaration | content |
|---|---|
| `gridFrameWA W a bb hbb G X hne sm γ hη hε D` | `gridFrameW` with **only** the `S` field replaced by `SvalA` (structure-update syntax), so every other field is *definitionally* unchanged |
| `gridFrameWA_one` | at `a = 1` it **is** `gridFrameW` |
| `gridFrameWA_propA` | `exact gridFrameW_propA` — `PropA` never reads `S` (same for `PropB`) |
| `torusChar_gridFrameWA_S` | the frame character, reindexed by `G.rowEquiv` |
| **`gridFrameWA_propC`** | bound is *literally* `smallPrimeBound` — take `sm` pre-filtered to the **active** primes `{p : 1 ≤ a_p}` (free: an inactive prime contributes `0` to `omegaOnA`), and the per-prime seed collapses to the constant `θ₀` |
| **`gridFrameWA_propC_gen`** | seed discharged at `freqSeed bb G.K`, under `1 + clog bb (2^K*(Ca*D)) ≤ G.N` |

### Why the whole thing was cheap (the structural reason — keep it)

A priori the rescaling could have destroyed the good-prime gain outright: `dist(k·x, ℤ)` can
vanish while `dist(x, ℤ) > 0`.  It does not, because

* `coeffAL` is linear in `q`, so scaling the *coefficients* by `a_p` = scaling the *frequency*
  by `a_p`; and
* `sum_sq_distZ_freqDepthB_ge` carries **no hypothesis on the Fourier box at all** — the box `D`
  enters the separation argument only through `freqDepthB_le`, i.e. only through the
  *admissibility* of the selected depth inside the layer budget `N`.

So the entire quantitative cost of a general bounded `a`, anywhere in §4C, is one **additive**
`⌈log_bb Ca⌉` on a layer budget already of size `Θ(K)`.

## Next, in order (step 4 onward of the directive's ladder)

4. **§4D — `PropD` for `gridFrameWA` at `w_{a,c}`.**  Port `G4SubsetCFrame`'s chain with
   `omegaOn (·.filter S) ↦ omegaOnA a ·` and `Sval ↦ SvalA`:
   `weightSC_split` → `frozenWeightSC` / `frozenTranslateSC` / `frozenGammaSC` /
   `blockSum_frozenSC_eq` → `blockSum_weightSC_split` → `gridFrameW_weightSC_Ffull_decomp` →
   `gridFrameW_weightSC_propD` (→ `gridFrameW_weightSU_propD_of_bounds` at `effC`).
   The big-prime estimate scales by `Ca`: `omegaOnA a T m ≤ Ca · omegaOn T m`.
   The arithmetic layer is already in kernel (`G4WeightA`: `weightAW`, `weightAW_eq_cast`,
   `weightAW_mul`, `TWeight.weightA`, `weightAW_one`, `weightAW_indicator`).
5. **Schedule**: the layer budget `N ≥ 1 + clog bb (2^K * (Ca * D))`.  `Ca` is a fixed constant
   and `k₄`/`N` are chosen after it, exactly as `C` was in B2e.
   🚦 **Registered trigger**: if some schedule quantity is capped *from above* by `N` in a way
   that `⌈log_bb Ca⌉` breaks — the moment cap `Mc ≤ 2^{m₂}` of
   `DESIGN-2026-09-16-prime-subset.md` §3 is the one to watch — that is a **proved obstruction**:
   write it into the DESIGN file, and the campaign's headline stays what is already proved.
6. **Assembly** at `S = {p : 1 ≤ a_p}`, then the audit theorem in `G4WeightStatement`, then
   🏁 **STOP**.

**Architecture (binding).**  `omegaOnA 1_S sm m = omegaOn (sm.filter S) m` — the prime-subset
campaign **is** the `a`-side at `a = 1_S`.  Generalize `G4SubsetC*` **in place**; do **not**
build a fifth parallel §4D stack (four already exist: `G4Remainder*`, `G4SubsetJunk`,
`G4Unbounded*`, `G4SubsetC*`).

`PENDING_WORK.md` §B6 carries the same in table form.
