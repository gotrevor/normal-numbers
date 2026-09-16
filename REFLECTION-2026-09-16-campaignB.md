# REFLECTION — 2026-09-16 (deep reflection lap, campaign B closed, `a`-side opened)

*Altitude lap.  Everything below was re-derived from the source tree, the compiler and the
git/handoff history this lap; nothing is inherited from a previous lap's verdict.*

Build 🟢 **9085 jobs**, verified this lap.  `src/` = exactly two `sorry`s
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`), both
pre-expedition and both on the forbidden-drift list; **zero `axiom`s** anywhere in `src/`.

---

## 0.  What the axiom ledger actually says (re-run, not inherited)

| theorem | `#print axioms` |
|---|---|
| `G4.audit_isDisjunctive_weight_logLogPow` | `[propext, Classical.choice, Quot.sound]` |
| `G4.audit_isDisjunctive_subsetWeight_logLogPow` | trust triple |
| `G4.audit_isDisjunctive_residueClass_weight_logLogPow` | trust triple |
| `G4.SchedB.isDisjunctive_weight_logLogPow` | trust triple |
| `G4.SchedB.isDisjunctive_subsetWeight_logLogPow` | trust triple |
| `G4.isDisjunctive_base`, `isDisjunctive_four`, `isDisjunctive_two` | trust triple |
| `G4.Sched.isNormal_fullRealW` | trust triple |
| `G4.SchedB.isDisjunctive_Omega`, `isDisjunctive_weight` | trust triple |

**Math-axiom count (🟢+🟡+🟠): 0.**  There is no axiom ledger to chip on this project: the
debt-discharge doctrine is vacuous here, and the reflection's real job is therefore *route*,
not *debt*.  STATUS.md's ledger namespaces were checked against the tree and are correct as
written (`G4.isDisjunctive_residueClass{,_weight_logLogPow}`, `G4.irrational_primeSum`); all four
also re-printed trust-triple clean this lap.

**Statement faithfulness, re-read against the definitions.**  `IsDisjunctive b x` unfolds to
`∀ a c, 0 ≤ a → a < c → c ≤ 1 → ∃ n, Int.fract (x·bⁿ) ∈ Ico a c` — the standard dense-orbit
form, no weakening.  `G4WeightStatement`'s three audit theorems restate the headlines with
`weightLambert` / `subsetWeightLambert` / `TWeight` fully unwound, so an auditor reads
`∑' n, (#{p ∣ n} + ∑_{p∣n} c_p(v_p(n)−1))/bⁿ` and nothing else.  **No transcription drift found.**

---

## 1.  Is the DESTINATION still right?

**Yes, with one honest recalibration that must be written down rather than assumed.**

The programme's live centrepiece is the **G4 disjunctivity machine**: the §4A–§4E stack that
proves `∑_n w(n)/bⁿ` is disjunctive in base `b ≥ 3` for arithmetic weights `w`.  Its destination
is the *maximal weight class the machine supports*:

> `w(n) = ∑_{p ∣ n} (a_p + c_p·(v_p(n) − 1))`, `a` bounded, `c` in the polylog growth class,
> the whole thing optionally restricted to a prime set with a Mertens rate.

Reached so far: **every axis except general `a`**.  `a ∈ {1, 1_S}` and `c_p ≤ A₀(1+log₂log₂p)^s`
on any `S` with a Mertens rate, all unconditional and trust-triple clean.

**What the destination is NOT, and why that is not a surrender.**  Two natural upgrades are
*machine-checked dead ends of this mechanism*, not open problems this lap should reopen:

* **Base 2.**  `G4RowMassOptimal.two_pow_le_sum_abs` — every nonzero integer array on the tensor
  grid with vanishing line sums in all `K` directions has `∑|μ| ≥ 2^K`, attained by `D_s^{⊗K}` —
  gives `rowL1_le_rowMass` and hence `one_le_rowMass_two`: **every** design in the family has
  row mass `≥ 1` at `b = 2`, while the §4D budget needs `< 1`.  This is a theorem about the
  whole family, not about our parameters.  The single named escape (signed cancellation in the
  `p > Y` range) is a two-point-correlation input the programme deliberately excludes.
* **Normality rather than disjunctivity.**  `qForces_normal_iff_density_one` +
  `not_qForces_normal_at_pow`: a quantized digit-local sampler forces normality iff it reads a
  density-one position set, and this schedule's sampled density is `≤ ½(3/K⁴)^K`.  Closed
  quantitatively, on this mechanism.

Both walls are *proved*, and the repo has been scrupulous about never claiming past them.  That
scrupulousness is the healthiest structural fact about this project and must be preserved.

One consequence worth recording plainly: **`phaseOscillation` is the same wall.**
`primeLambert = ∑ ω(n)/2ⁿ` is the **base-two** constant, so the sorry-gated
`irrational_primeLambert` is exactly the case the design family kills; and it is additionally
*superseded in the literature* (Tao–Teräväinen arXiv 2512.01739 Thm 1.3 proves it).  The `b ≥ 3`
half is ours and unconditional (`G4.irrational_primeSum`).  So neither open `sorry` in `src/` is
a target: one is a proved-dead route to a published theorem, the other is Linnik-strength and
reaches no unconditional statement.  Keeping both parked is correct, and this is the reasoning,
not an assertion.

---

## 2.  ROUTE VERDICT: **CONTINUE** — but with a FINISH LINE, which is a real course change

### The registered triggers, checked against git + the handoffs

| trigger (CURRENT DIRECTIVE, 2026-09-16 B-review-1) | fired? |
|---|---|
| 🚦 "if step 1's error term cannot be made `o(X)` for any growth class strictly larger than bounded, that is a proved obstruction → fall back to `w_{c,S}`" | **NO.**  `Tame c A` was found and `isDisjunctive_weight_logLogPow` covers the whole class `c_p ≤ A₀(1+log₂log₂p)^s`.  The step-1 crux `sum_junk_le'` closed (`G4UnboundedJunk`). |
| ⛔ forbidden drift (pre-expedition `sorry`s, Comparator, base 2, `native_decide`, `docs/` essays) | **honoured**; nothing in the last 40 commits touches any of them. |

### The two "am I rationalizing past a trigger" tells

* **(a) recurring "the crux is almost cracked" with nothing closing?**  **No.**  In the last
  ~24 h two whole campaigns *closed* with unconditional, trust-triple-clean headlines
  (`isDisjunctive_residueClass`, `isDisjunctive_Omega`, `isDisjunctive_weight`, then
  `isDisjunctive_weight_logLogPow` and the merge).  These are whole-lemma targets, not
  narrowings.
* **(b) declining finishability across reflections?**  **No — rising.**  The 2026-09-16
  B-review-1 directive named "`c` unbounded" as *the* route-decisive uncertainty; it closed the
  same day.

**So no trigger has fired, and the route continues.**

### The real risk here is NOT a false summit — it is unbounded scope

This is the finding this lap exists to produce, and it argues for a course change.

Look at what the last laps actually did.  B0–B3 attacked the machine (a `C`-free junk estimate,
a new hypothesis class `Tame`, a per-`d` overlap bound).  **B4 and B5 did not**: widening
`c_p ≤ ⌊log₂ p⌋` to `c_p ≤ A₀(1+log₂log₂p)^s` is growth-class bookkeeping against an unchanged
budget, and B5 is an audit surface.  Valuable, cheap — and *not* mathematics on the crux.

The structural hazard of a machine that works is that there is always one more parameter to
generalize.  Left open-ended, this campaign can emit "new headlines" indefinitely while the
marginal content per lap goes to zero.  A treadmill cannot notice that from inside; this lap
can.  **The fix is a pre-registered finish line, not a redirection.**

**The `a`-side is the right terminal target, for a reason that is structural rather than
aesthetic:** it is the *only* remaining axis that touches **§4C, the near-field Fourier core**.
Every campaign since A kept the retained small-prime vector equal to the *indicator* vector
`omegaOn sm`, so §4C was untouched and the work was §4D budget plumbing.  A general `a` changes
`Sval` itself.  It is therefore the last piece whose feasibility was in genuine doubt — and the
last one that is real mathematics rather than re-parametrization.

---

## 3.  The decisive probe, run this lap: **the `a`-side crux is FEASIBLE and CHEAP**

Hardest-first means risk-first.  The decisive case is: *does the good-prime contraction survive
when the local phase at `p` runs at the scaled frequency `a_p·q`?*  It can fail catastrophically
in principle — `distZ(a·x)` can be `0` while `distZ(x) > 0`.  So this was the right thing to
test, and it is the smallest compiler-grounded probe of it.  Both halves now **compile**
(`scratch/ProbeA.lean`, against the real tree):

```lean
-- 1.  the phase decomposition survives: the local phase at p is the ORDINARY one at a_p·x
lemma phaseA_eq_sum_local (a : ℕ → ℕ) (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) :
    totalPhaseA a s ρ x n = ∑ p ∈ s, localPhase p ρ (fun i => (a p : ℝ) * x i) n

-- 2.  the frequency-separation SEED is unchanged; the only cost is the box D → Ca·D
theorem sum_sq_distZ_coeffA_ge_gen {bb : ℕ} (hbb : 2 ≤ bb) {N D Ca : ℕ}
    (hN : 1 + Nat.clog bb (2 ^ K * (Ca * D)) ≤ N)
    {ap : ℕ} (hap : 1 ≤ ap) (hapC : ap ≤ Ca)
    {q : (Fin K → Fin s) → ℤ} (hq : q ≠ 0) (hqD : ∀ a, |q a| ≤ (D : ℤ)) :
    freqSeed bb K ≤ ∑ i : AtomLayer K s N, distZ ((ap : ℝ) * coeffAL bb q i) ^ 2
```

**Why (2) is the whole ball game.**  `coeffAL` is *linear in the frequency* — `a_p·(q ᵥ* A) =
(a_p·q) ᵥ* A` — so scaling the coefficients is the same as scaling `q`.  And
`sum_sq_distZ_freqDepthB_ge` is stated for an **arbitrary nonzero** `q`, with no box hypothesis
at all: the box `D` enters only through `freqDepthB_le`, the *admissibility* statement that the
chosen depth `j_α` fits inside the layer budget `N`.  Hence the seed `freqSeed bb K = b^{−4}(2/b²)^K`
is **untouched** by `a`, and the entire cost of a general bounded `a` is one enlargement,

> `N ≥ 1 + ⌈log_bb(2^K · D)⌉`  ⟶  `N ≥ 1 + ⌈log_bb(2^K · Ca · D)⌉`,

an *additive* `⌈log_bb Ca⌉` on a layer budget that is already `Θ(K)` — absorbable exactly the
way `C` was in campaign B.  Nothing else in §4C moves: the roots of `LocalPhase.ofShifts` are
`image (root p ρ)` and depend only on `ρ`, so the four §4C error terms in
`norm_sampleAvg_torusChar_Sval_le` are **literally identical**.

**And the downstream is already generic.**  `norm_sampleAvg_prod_ee_le` — which
`norm_sampleAvg_ee_phase_le` is a thin instantiation of — already takes a *per-prime*
`LocalPhase p` family and a *per-prime* seed `fun p => if GoodPrime ρ p then θ₀ else 0`.  So the
`a`-version needs no new probabilistic layer at all: feed it `shiftPhase ρ (a_p • x)` and the
seed `if GoodPrime ρ p ∧ 1 ≤ a_p then θ₀ else 0`.

**Verdict: the `a`-side is not a wall.  It is a two-module port.**

---

## 4.  What a sharp outsider would say we're missing

### (i) One stack, not two — the `a`-side IS the subset side

`omegaOnA 1_S s m = omegaOn (s.filter S) m`.  The prime-subset campaign is *literally* the
`a`-side at `a = 1_S`.  So the temptation to build a fifth parallel stack
(`G4WeightA*` beside `G4SubsetC*`) is the wrong architecture: it duplicates §4D for a fourth
time.  **Generalize `G4SubsetC*` in place** — replace the `S`-filter by the `a`-weight, recover
the subset results as `a = 1_S` and the plain results as `a = 1`.  This collapses two open
obligations (the `a`-side, and the `a`-side × subset merge) into one.

### (ii) The statement should be the general ADDITIVE FUNCTION

`w_{a,c}(n) = ∑_{p^v ‖ n} (a_p + c_p(v−1))` is precisely the additive functions whose `p`-local
value is **affine in `v`**.  That is an odd class to headline.  The natural statement is:

> for every additive `f : ℕ → ℕ` with `f(p^v) ≤ a_p + c_p(v−1)` (`a` bounded, `c` polylog) and
> `f(p) = a_p`, `∑_n f(n)/bⁿ` is disjunctive in base `b ≥ 3`.

Why this is nearly free, given campaign B's own structural move: **the far-field `hW` is a
domination, not an equality** (`sum_abs_farPartW_le_of_layer` only ever bounds a sample sum from
above).  §4C sees only `f(p)` — it is blind to `f(p^v)` for `v ≥ 2`, because the retained vector
is a function of `p ∣ n` alone.  §4D's junk/frozen estimates are all *upper* bounds on the
excess.  So general `f` should ride the `a`-side plus the existing domination.  One thing to
check before claiming it: `TWeight` wants ℕ-valued, so `f` must be non-decreasing in `v` at each
`p`.  Record as the campaign's **stretch statement**, attempted only after the `a`-side lands.

### (iii) Nothing else is worth opening

The `c_p ≍ log p` boundary is a *proved* obstruction (`cMax ≈ 2^{21K²}` against an exponential
junk budget, `DESIGN-2026-09-16-prime-subset.md`).  Mere divergence `∑_{p∈S}1/p = ∞` without a
rate is likewise a *proved* limitation of the route, not a defect.  Base 2 and normality are
proved dead.  There is no untried high-value axis being neglected.

---

## 5.  KEEP / STOP / NEXT

**KEEP**
* Proving walls instead of asserting them.  `two_pow_le_sum_abs`, `not_T_E`,
  `qForces_normal_iff_density_one`, the `cMax` boundary — a campaign that machine-checks its own
  negative results is worth far more than one that only accumulates positives.
* The audit-surface discipline (`G4WeightStatement`): headline statements restated with every
  abbreviation unwound.  This is the real faithfulness defense and it is working.
* Compiling skeleton + named `sorry` leaves before each hard step.

**STOP**
* **Opening a new campaign the moment one closes.**  Two campaigns closed in a day; the reflex
  to immediately widen the parameter again is what turns a finished machine into a treadmill.
* **Growth-class bookkeeping laps** (B4-shaped work: widening an exponent against an unchanged
  budget).  If a target does not touch §4C, §4B or the schedule's *structure*, it is not worth a
  lap of its own — fold it in or skip it.
* **Building a parallel stack per parameter.**  Four §4D stacks already exist
  (`G4Remainder*`, `G4SubsetJunk`, `G4Unbounded*`, `G4SubsetC*`).  Generalize in place.

**THE single highest-value next target**

> **`isDisjunctive_weightA` — the master additive weight at a general bounded `a`** — reached by
> generalizing the `S`-filter to the `a`-weight *in place*, with the §4C port already probed:
> `phaseA_eq_sum_local` + `sum_sq_distZ_coeffA_ge_gen` (both compile), then `SvalA` /
> `torusChar_SvalA` / `norm_sampleAvg_torusChar_SvalA_le`, then the schedule's layer budget
> `N ≥ 1 + clog_bb(2^K·Ca·D)`, then assembly at `S = {p : 1 ≤ a_p}`.

**Reasoning.**  It is the only remaining obligation that touches the near-field Fourier core;
its feasibility was the last genuine uncertainty in the campaign and this lap's probe resolved it
*positively*, which converts it from a risk into a finite port; and it subsumes the subset axis,
so it closes two obligations at once.  After it (and optionally the additive-function stretch),
**the campaign is saturated and the run should end** — not be extended by another
re-parametrization.
