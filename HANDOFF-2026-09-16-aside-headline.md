# HANDOFF 2026-09-16 — the `a`-side headline is PROVED; only the audit theorem remains

Branch `wip/g5-prime-subset`, HEAD `3a64f4a`, tree **clean**, `lake build` 🟢 **9090 jobs**.
`src/` = the two pre-expedition forbidden-drift `sorry`s; **zero `axiom`s**.

> `DIRECTION.md` → CURRENT DIRECTIVE (the `a`-side, TERMINAL, with a pre-registered FINISH LINE)
> outranks this file.  Supersedes `HANDOFF-2026-09-16-aside-4C-frame.md`.

## 🏁 The finish line is (all but) reached

`SchedB.isDisjunctive_weightA_logLog` — **unconditional**, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`:

> for `a` bounded (`a_p ≤ Ca`, `1 ≤ Ca`) whose **active** primes `{p : 1 ≤ a_p}` carry a Mertens
> rate, and any `c_p ≤ ⌊log₂log₂ p⌋`, the constant `∑_n w_{a,c}(n)/bⁿ` with
> `w_{a,c}(n) = ∑_{p∣n}(a_p + c_p(v_p(n)−1))` is disjunctive in every base `b ≥ 3`.

The directive's remaining item is **step 6's audit theorem** in `G4WeightStatement` (mirror
`audit_isDisjunctive_subsetWeight_logLogPow`), plus the `a = 1_S` sanity instance recovering
`isDisjunctive_subsetWeight_logLog`.  Then 🏁 STOP (do **not** open a successor campaign).

## Proved this session (commits `14e9e2b`, `862ce2b`, `621f953`, `126d9c6`, `3a64f4a`)

| file | content |
|---|---|
| `G4WeightAFrame.lean` (new) | §4D for `w_{a,c}` on `gridFrameWA`: `omegaBigA`, `omegaW_split`, `weightAC_split`, `frozenGammaAC`, `SvalA_filter_active` (inactive primes drop for free — this is what lets the frame carry the ACTIVE small primes `PropC` demands), `gridFrameWA_weightAC_Ffull_decomp`, `gridFrameWA_weightAC_propD`, **`omegaBigA_layer_cake`** (`a_p = #{k∈[1,Ca] : k ≤ a_p}` ⇒ `Ca` copies of the subset large-prime average, reusing `bigAvgS_le'`, which is uniform in `S`), `bigAvgA_le'`, `weightAW_le_smul`, `farAvgW_le_effC_smul`, `gridFrameWA_weightA_propD_of_bounds` |
| `G4UnboundedAvg` / `G4UnboundedFrame` | `sum_abs_farPartW_le_of_layer` / `farAvgW_le_of_layer` generalized **in place**: the dominating weight is now any `g : ℕ → ℝ`.  Needed because `w_{a,c} ≤ Ca·w_c` is *not* dominated by any `weightW c'` — on squarefree `m` the `ω` coefficient of `weightW` is exactly 1.  (Recorded obstruction; the scaling is unavoidable.) |
| `G4WeightAWitness.lean` (new) | `ScheduleWitnessAU` (only `hN`, `hbig`, `hfar`, `hbudget` move), `gridFrameWA_propB_of_bound`, `separatingFrameExistsW_weightA_of_witness`, `isDisjunctive_weightA_of_witness`, **`hN_holdsA`** |
| `G4SchedBEAssembly` | `hbig_holdsE` split into `hbig_two_termsE` (`≤ 2K·a⁴ + 51·a²`) + its numeric closing; statement unchanged |
| `G4WeightASched.lean` (new) | `hbigA_holdsE`, `scheduleWitnessAUE`, `exists_scheduleWitnessAU`, **`isDisjunctive_weightA_logLog`** |

### 🚦 The registered trigger does NOT fire — this is the lap's decisive finding

The enlargement `D → Ca·D` **is** absorbable.  `hN_holdsA`: the schedule's `N = 100K²` against
`2^K·Dj K k₄ ≤ 2^{3K}` leaves room for any `Ca ≤ 2^K`.  And the `Ca`-scaled large-prime average
fits the **unchanged** budget (`δbig = 1/8`) because the estimate is `Θ(a²)` (`a = 2^{−k₄}`) while
the target is `(1/K)·a` — a factor `2^{k₄}/K` of slack (`hbigA_holdsE`, needs `10⁵Ca k₄³ ≤ 2^{k₄}`).
Net: **the entire cost of a general bounded `a` is one enlargement of `k₄`**, `k₄ ≥ Ca·max ⌈A⌉₊ Dc`,
supplied by `exists_good_k₄_polyGen` at degree 4.  No new analytic content anywhere.

## Next lap, in order

1. `G4WeightStatement`: `audit_isDisjunctive_weightA_logLog` (the audit surface re-states the
   headline from first principles: `weightALambert` unfolded, `IsDisjunctive` unfolded), plus the
   `a = 1_S` instance recovering the subset headline, and a `STATUS.md` row.
2. Re-run the trust triple (`#print axioms` on every headline) and update `PENDING_WORK.md`.
3. 🏁 Then the campaign is COMPLETE — `box done --green`.  The one permitted stretch (general
   additive `f(p^v) ≤ a_p + c_p(v−1)` riding `sum_abs_farPartW_le_of_layer`, now generic in `g`,
   which makes it *easier* than when the directive was written) is optional and only after.

## Build hygiene (cost me ~20 min this session)

The box's "Too many open files" failure is real here: run **one** `lake build` at a time, under
`taskset -c 0-5`, and kill stray background `lake`/`lean` processes first.  Concurrent background
builds are what triggered it, not the code.
