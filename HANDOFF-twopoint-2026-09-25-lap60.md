# HANDOFF twopoint — lap 60, 2026-09-25: **the 🟡 `DelangeMean` is DISCHARGED IN FULL**

Branch `wip/twopoint-avg`.  Working tree clean; five green commits this lap (pre-commit `lake build`,
9298 jobs).  Every new declaration `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
**No `sorry` introduced.**

## CORRECTION, found at the end of the lap — read this first

`DelangeSlot.charSum_tendsto_zero` (`DelangeSlotMaster.lean`, proved and axiom-clean, written in an
earlier campaign) specialises at `M = 1`, `κ ≡ 1`, `P = 0` to exactly `∑_{n≤N} z^{ω(n)} = o(N)`,
because `omegaLarge 0 = ω`.  **The 🟡 was therefore already discharged in this tree; the connection
had never been made.**  `TwoPointDelangeAll.delangeMean_via_delangeSlot` now records that
derivation in kernel.  So the honest accounting of this lap is:

* the *ledger* advance (ConjC1 free of all cited-but-unproved theorems) is real, and was blocked
  only by missing wiring, not by missing mathematics;
* `TwoPointDelangeLevin.lean` is an **independent second proof**, by a genuinely different route:
  `charSum_tendsto_zero` goes through Dirichlet `L`-functions, `ψ(x,χ) = o(x)` and Wiener–Ikehara;
  the new file uses only the hyperbola-averaged quantitative PNT and elementary summation — no
  `L`-function, no character, no contour, and it is quantitative (`≪ (log N)^{θ−1}`, any
  `θ > max(Re z, 0)`).  Two independent kernel proofs of the same statement is worth having.
* The lap-59 handoff's claim that `b ≥ 3`, `‖t‖ ≥ 1/6` "needs `ζ(s)^z` — Selberg–Delange or
  Halász" is **refuted twice over**: by the elementary route below, and by the tree's own
  `DelangeSlot`.  Do not repeat that claim.

## The headline

    delangeMean_of_phase_ne_one :  phase t ≠ 1  →  DelangeMean t          -- unconditional
    omegaPow_mean_tendsto_zero  :  ‖z‖ = 1 → z ≠ 1 → ‖∑_{n≤N} z^{ω(n)}‖/N → 0

for **every** `t ∉ ℤ` — no regime restriction.  Delange's 1969 theorem, carried as a cited
hypothesis since this swing began, is now a theorem of this repo on its whole range.  The wiring
(`TwoPointDelangeAll.lean`) gives `delangeMean_all`, `conjC1_of_multiElliott`,
`conjC1_of_pairDecorr` — hypothesis-free apart from the arithmetic leaf.

**Ledger update.**  `TwoPointKataiFree.lean`'s table said `ConjC1` rests on two inputs, `DelangeMean`
(🟡 PROVEN, "project-scale to formalise") and `MultiElliott` (🔴 OPEN).  As of this lap **it rests
on ONE**: the 🔴.  No cited-but-unproved theorem remains anywhere under `ConjC1`.

## Why the wall fell (the reason to read this)

Laps 28–56 ran Levin–Fainleib on the **kernel** `h_z = (z−1)^ω μ²`, whose `ℓ¹` mass
`A(N) ≍ (log N)^{‖z−1‖}` is the error term of the scale equation.  That, and only that, is what
capped the route at `‖z−1‖ < 1` (`‖t‖ < 1/6`).  Lap 59 then reached `t = 1/2` by finite convolution
to `μ`, and proved finite convolution reaches nothing else.  Both analyses were correct; the
conclusion drawn from them ("`b ≥ 3` needs `ζ(s)^z`") was not.

Run Levin–Fainleib on `f = z^ω` **itself**.  `‖f‖ ≡ 1`, so every error term is `O(N)` with no
`(log N)^{‖z−1‖}` anywhere.  It works because `ω` sees a prime power only through its prime,
uniformly in the exponent:

    ω(p^k · m) = ω(m) + [p ∤ m]        (`omegaNat_primePow_mul`)

so `f(d·m) = z·f(m)` off the multiples of `minFac d`, for every prime power `d` at once.

## The chain (`src/NormalNumbers/TwoPointDelangeLevin.lean`)

| step | declaration | content |
|---|---|---|
| identity | `sum_conv_gen`, **`sum_fOm_log_eq`** | `∑_{n≤N} f(n)log n = ∑_{d≤N} Λ(d)(z·M(N/d) − (z−1)·G(minFac d, N/d))`, EXACT |
| defect | `norm_gOm_le`, `ppPair`/`ppTerm`, **`sum_vonMangoldt_div_mul_minFac_le`** | `∑_{d≤N} Λ(d)/(d·minFac d) ≤ 16`, by prime-power regrouping onto `sum_log_div_sq_prime_le`.  **No Mertens' 2nd.** |
| swap | `sum_hyperbola_swap` | `∑_d k(d)∑_{e≤N/d}T(e) = ∑_e T(e)∑_{d≤N/e}k(d)` |
| (A)(B)(C) | `norm_defect_le`, `exists_norm_psi_replace_le`, `norm_log_shift_le` | `32N`; `ψ→N/m` on `DelangeSlot.exists_sum_abs_deltaN_le`; `log N` vs `log n` on `sum_log_div_le` |
| **scale eq** | **`exists_levin_scale_bound`** | `‖M(N)·log N − z·N·T(N)‖ ≤ C·N`, **C absolute** |
| Abel | `tOm_eq_of_pos`, `exists_mOm_scale` | `T = M/N + Ũ`; `‖m(N)log N − z·Ũ(N)‖ ≤ C` |
| recursion | `invStep`, `invStep_le_logRatioStep`, `exists_uOm_step` | `Ũ(N+1) = Ũ(N)(1+z·s_N) + s_N·E_N`, `s_N = 1/((N+1)log N)`, `‖E_N‖ ≤ C` |
| closure | `levin_step_scalar`, **`exists_norm_uOm_le_rpow`** | `‖Ũ(N)‖ ≤ K(log N)^θ` for ANY `θ ∈ (max(Re z,0),1)` |
| payoff | `omegaPow_mean_tendsto_zero`, `delangeMean_of_phase_ne_one` | `M(N)/N ≪ (log N)^{θ−1} → 0` |

The decisive difference from brick 3 of the old route: the additive error is a **constant**, not
`A(N)`, so the induction needs only `θ > 0` — and `Re z < 1` is automatic for `‖z‖ = 1`, `z ≠ 1`.
Reused verbatim from `TwoPointDelangeScale.lean`: `logRatioStep`, `one_le_log_cast`,
`log_succ_eq_mul`, `logRatioStep_le_inv`, `norm_one_add_mul_ofReal_le`, `one_add_rpow_ge`,
`rpow_sub_one_mul`.  From `TwoPointMoebiusPNT.lean`: `sum_log_div_le`.

## Refuted en route, recorded so no lap retries it

**The pretentious ladder.**  `z^ω = w^ω * G`, `G(p) = z−w`, `∑_{n≤N}‖G(n)‖/n ≍ (log N)^{c}`,
`c = |z−w|`.  With a base rate `M_w(x) ≪ x(log x)^{β−1}` the convolution gives
`M_z(N) ≪ N(log N)^{c+β−1}`, so one can step from `w` to `z` whenever `c + β < 1` — and iterate
along the circle from the proved regime.  It **fails**: the exponent accumulates the *arc length*,
`dβ/dt = 2π`, while the budget `1 − Re z = 2sin²(πt)` only grows like `2π²t²`.  The ladder stalls
before it leaves `‖t‖ < 1/6`.  (Lap 59's "anchor bootstrapping fails on the tail" was the right
verdict for the wrong reason: the quantitative rate does make the convolution converge; it is the
exponent arithmetic that kills it.)

## Where the swing stands

`ConjC1` ⟸ one input, the 🔴 arithmetic leaf (`MultiElliott` / `PairDecorr` / `TwoPointWeightedAvg`
/ `TwoPointPairSumSmall`), pinned at SESSION WRAP 4 as an *equivalence* with a named open problem
and stated conditionally by the paper itself.  `DIRECTION.md`'s CURRENT DIRECTIVE forbids
re-opening it.  `twoPointWeightedAvg_all` untouched, as ratified.

## Confidence at wrap
- `DelangeMean t` for all `t ∉ ℤ`: **DONE** (was 25% at lap 59).
- `ConjC1` free of all cited-but-unproved theorems: **DONE**.
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%** (unchanged;
  untouched this lap, per the directive).

## NEXT SESSION
The 🟡 ledger of this swing is empty.  Remaining `sorry`s in `src/` outside the forbidden set:
`SwingC2.lean` (×4), `SwingC3Leaf.lean`, `SwingC3Rotation.lean`, `PrimeLambertOscillation.lean`,
`MahlerDriftOne.lean` (Linnik-strength, disclosed).  `SwingC1*.lean` and the ratified leaf are
frozen by the directive.

---

## Checkpoint (end of lap 60)

Branch `wip/twopoint-avg`, HEAD `e71155e`.  Working tree **clean**.  Eight green commits this lap,
every one gated by the pre-commit `lake build` (9298 jobs).  No `sorry` introduced; every new
declaration `#print axioms`-clean.

New files: `src/NormalNumbers/TwoPointDelangeLevin.lean`, `src/NormalNumbers/TwoPointDelangeAll.lean`
(both imported from `src/NormalNumbers.lean`).  No frozen file touched
(`PairDecouple*`, `SwingC1*`, `CastingOut*`, `Maze.lean`, `papers/`, `agent-mail/`, KICKOFFs,
`DIRECTION.md` all untouched); `twoPointWeightedAvg_all` untouched, as ratified.

## NEXT SESSION — start here

1. **`DelangeSlot.charSum_tendsto_zero` is an unexploited asset.**  It is proved and axiom-clean
   and gives far more than `DelangeMean`: for any character-like `κ` mod `M` and any `P`,
   `(1/N)∑_{n≤N} κ(n)·z^{ω_{>P}(n)} → 0`.  Nothing outside the `DelangeSlot` namespace consumes it.
   That is exactly **Delange in arithmetic progressions, for the large-prime `ω`** — the engine the
   C3 crux needs for its digit peel.  First move of the next lap: inventory what else in the tree
   becomes unconditional once it is wired in (the same way `DelangeMean` did this lap).

2. **The C3 crux, `SwingC3Leaf.weylLambertTwist_holds`** — the biggest open obligation now visible
   outside the frozen C1 leaf.  It asks
   `(1/N)∑_{n<N} e(jn/Q)·e(h·tailLarge P b n) → 0`, and `tailLarge P b n = ∑_{i≥1} ω_{>P}(n+i)b^{−i}`.
   Peeling one digit gives `e(h·tail_n) = e((h/b)·ω_{>P}(n+1))·e((h/b)·tail_{n+1})`, and the first
   factor times the periodic twist `e(jn/Q)` is **exactly an instance of item 1**.  So the natural
   next lap is the structural reduction: `WeylLambertTwist` from `charSum_tendsto_zero` plus a
   ShiftIndep-type decorrelation, putting C3 on the same footing as C1 and pinning its depth.
   Caveat to test, not assume: the peel must grow (`K ≈ log_b log N`, since `tail_n = O(log n)`),
   which is what makes C1's analogue a 🔴; check whether C3's twist changes that.

3. **Alternative C3 route, possibly cheaper**: `SwingC3Rotation.tailLargeDecouple_holds` (disclosed
   `sorry`, leaf B).  Leaf A is proved.  Leaf B says the distribution of `tailLarge P b n` does not
   depend on `n mod Q` when every prime factor of `Q` is `≤ P`.  At finite level this is EXACT by
   CRT (moduli `p > P` are coprime to `Q`); the whole content is the truncation, i.e. a Brun
   fundamental-lemma / level-of-distribution argument.  The repo already has Brun material
   (`KICKOFF-brun-lower-core.md`, `PrimeModelRadical*`).  Formalising the exact finite-level CRT
   independence is a self-contained prerequisite worth one lap on its own.

4. **Do NOT retry**: the pretentious ladder along the unit circle (refuted above); the claim that
   `‖t‖ ≥ 1/6` needs Selberg–Delange/Halász (refuted twice over); anything on the frozen C1
   arithmetic leaf, which `DIRECTION.md` forbids.

## Confidence at checkpoint
- `DelangeMean t` for all `t ∉ ℤ`: **DONE**, now by two independent kernel proofs.
- `ConjC1` free of all cited-but-unproved theorems: **DONE**.
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%** (untouched).
- C3 (`weylLambertTwist_holds`) provable with known techniques: **15%** — raised from "unmeasured"
  because item 1 supplies its first peel outright.
