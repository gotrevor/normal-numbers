# STATUS — normal-numbers 📊

## Attended update, 2026-09-13: Stoneham base-6 disjunctivity proved

Every finite base-6 word occurs arbitrarily late in `stoneham23`:
`stoneham_base6_interval_recurrence` and `isDisjunctive_six_stoneham23`, in
`StonehamBoundary.lean`.  The fixed-boundary congruence route is complete at
`f1f9749`; frozen statements unchanged, host build and transitive dependency
checks passed.  Fable/low finished in lap 1; the bounded campaign is stopped.
No literature novelty claim, no normality claim in base 6, and no ln-2 result.

The parallel theta investigation produced an exact low-precision seed
permutation and a counterexample to inferring short-block cancellation from
such information; `experiments/theta_seed_precision.py` is its exact probe.
ROADMAP also corrects the old open label for `sum 1/(9^k 2^(2^k))` using
Vandehey's later normality theorem.  No second normality campaign was launched.

The September 8 and 13 snapshots below are historical; the live campaign is G4.

**A machine-checked conjecture graph around normality/disjunctivity, plus a
sorry-free proof wing (Becher–Yuhjtman, image-Khinchin, the adder tower, the
Mahler multiplier chapter) — and the G4 disjunctivity theorem, proved and
kernel-verified 2026-09-14; the live campaign is now its base-`b` generalization.**
· **Build**: 🟢 green (8948 jobs) ·
**Updated**: entropy review lap 8 · 2026-09-14 · `wip/g4-entropy` @ `79f2470`

## 🔬 2026-09-14 (entropy expedition, laps 1–7): the SAMPLE-ENTROPY theorems E0 and E1

The live campaign is the attended **entropy expedition** (`BRIEF-entropy-expedition-2026-09-14.md`,
`DIRECTION.md` override + entropy CURRENT DIRECTIVE), branch `wip/g4-entropy`.  Fix `x = G₄` and
read its *binary* digits through the implemented base-four schedule.  Ten new `G4Entropy*`
modules, all `sorry`-free, no new axioms, no pre-expedition file edited:

```
Sched.entropy_E0 : K = 4k₄ → 33856 ≤ K → (1/5)·k₄·(K²+1)^K < (jointLaw …).H₂
Sched.entropy_E1 : K = 4k₄ → 160000 ≤ K → k₄·(K²+1)^K − 50·√K·(K²+1)^K < (jointLaw …).H₂
```

`jointLaw` is the law of the **whole vector** `Z^x_K = (⌊2^{m_K}{4^{k_{K,α}(n)}x}⌋)_{α}` under
*one* uniform `n ∈ P_K`; `m_K = K/4`, `H_K = (K²+1)^K`.  E1 is the brief's quantitative target
with `C = 50`, and dividing by `m_K H_K` gives `H₂/(m_K H_K) ≥ 1 − 200/√K → 1`, the qualitative
E0.  Both print the trust triple.  The mechanism: an *entropy* deficit replaces the covering
deficit of an omitted word (E0 has no omitted word), and the four schedule allowances were
re-closed exponentially small (`hbig_small`, `hfar_small`, `jackson_term_small`,
`smallPrime_term_tiny`, new Jackson degree `DjE = (16K²2^{m_K})²`).

**This is not normality and does not claim it.**  It is an unconditional statement about the
quantized arithmetic sample.  The bridge to ordinary digit frequencies is brief §6's transfer
`T_E`, and settling it is the whole objective of the next laps — see the entropy CURRENT
DIRECTIVE.  Review lap 8's finding: the sample is **digit-local** (`ZSample_eq_blockVal`), so
`T_E` forces the sampled position set `S = ⋃_K S_K` to have lower density ≥ 1/2, while
`kIdx_spec`'s `d_α ∣ kIdx` confines `S_K` to multiples of `2d_α` with `d_α ≥ 1 + Q_K·D₀_K`
and `Q_K = (U+K+N+2)!`.  That points hard at `T_E` being **false**, with an explicit witness.

## 2026-09-14 (review lap 16): the headline's corollaries — IRRATIONALITY — and base two RETIRED

`IsDisjunctive.irrational` (`DisjunctiveCorollaries.lean`): a rational `a/q` has
`q·orbit b x n ∈ ℤ`, so its orbit misses `[1/(2|q|), 1/|q|)`.  Hence, axiom-clean and
unconditional, **`G4.irrational_primeSum : 3 ≤ b → Irrational (∑' p : Nat.Primes, 1/(bᵖ−1))`**
— an independent, machine-checked proof of the `b ≥ 3` half of the prime-Lambert
irrationality family (Tao–Teräväinen arXiv 2512.01739 Thm 1.3 is the base-two case), by a
different route, and strictly stronger for those bases.  Also `IsDisjunctive.exists_ge` (every
interval is hit *arbitrarily late* — cut it into `N+1` pieces, the hitting times are distinct)
and hence `every_word_occurs_base_late`: every finite base-`b` word occurs infinitely often.

**Base two is RETIRED, not deferred.**  Lap 13 refuted the parameter choice (`rowL1 2 K = 1`);
this lap refutes the design family: killing a layer costs one tensor coordinate, and any
nonzero integer array with vanishing line sums in `K` directions has `L¹ ≥ 2^K`, so
`rowL1 ≥ 2^K b^{−K}/(b−1) ≥ 1` at `b = 2` for *every* such design — the cost of killing a
layer exactly cancels its gain.  And no re-tuning of `Y` escapes: the medium range needs
`Y ≲ √X` while a non-cancelling far range needs `Y ≥ X^{1−o(1)}`.  The only repair is signed
cancellation for `p > Y` — the deep two-point correlation input the brief forbids inheriting.
New campaign (G5): make the arithmetic input an interface, instances `ω` and `Ω`.

## 🏁 2026-09-14 (lap 14): G4B PROVED — `IsDisjunctive b (primeLambertAtBase b)` for every `b ≥ 3`

`NormalNumbers.G4.isDisjunctive_base` (`G4SchedBAssembly.lean`): for every integer `b ≥ 3`,
`∑_n ω(n)/bⁿ = ∑_p 1/(bᵖ−1)` (`isDisjunctive_primeSum`) is disjunctive in base `b`; every
finite base-`b` word occurs (`every_word_occurs_base`); and `∑ ω(n)/(cᵏ)ⁿ` is disjunctive in
base `c` for `cᵏ ≥ 3` (`isDisjunctive_root`).  `#print axioms = [propext, Classical.choice,
Quot.sound]`, no `sorry`, no `native_decide`.  The base-four theorem is re-derived as the
instance `isDisjunctive_four'`.  The whole §4 layer is base-general (`gridFrame bb`, the
named masses `rowL1 b K = (2/b)^K/(b−1)`, `rowL2`, `farBound`, the seed
`freqSeed b K = b^{−4}(2/b²)^K`), and the §5 schedule `SchedB` runs in `(b, K)` under
`3 ≤ b`, `2b² ≤ K`, `K ≥ 100`, with `hbig`/`hfar` settled at the worst case `b = 3`.
Base two stays refuted on this route (`rowL1 2 K = 1`).  Handoff:
`HANDOFF-2026-09-14-g4-lap14.md`.

## 2026-09-14 (review lap 13): G4 base-four INDEPENDENTLY VERIFIED; campaign advances to base `b ≥ 3`

Re-ran the whole audit from scratch: `lake build` 8930 jobs green; `isDisjunctive_four`,
`isDisjunctive_two`, `G4DisjunctiveFour_holds`, `G4DisjunctiveTwo_holds`,
`every_binary_word_occurs`, `primeSumAtBase_four`, `summable_omegaR_div_pow` each print
`[propext, Classical.choice, Quot.sound]`; `grep` finds **no `axiom` declaration anywhere in
`src/`**; and the endpoint's *definitions* (`IsDisjunctive`, `orbit`, `omegaR`,
`primeLambertAtBase`, `primeSumAtBase`, `OccursAt`) were re-read line-by-line against the
brief's frozen statement and are faithful.  Since the kernel guarantees the proof given the
definitions, and the definitions match the brief, **the base-four result stands**.

New campaign **G4B** (brief §7.1): `IsDisjunctive b (primeLambertAtBase b)` for every `b ≥ 3`.
Decisive symbolic probe run before any code — the five `ScheduleWitness` inequalities
re-derived in `b`.  `hB` gets easier (deficit `K log2·b^{−ℓ}/(4ℓ log b)`, vs `K·4^{−ℓ}/(8ℓ)`
at `b = 4`); `θ₀(b) = b^{−4}(2/b²)^K` gets larger; but `hbig`'s very-large-prime term is
`(log Mx/log Y)·(2/b)^K/(b−1)`, which at **`b = 2` is identically `1`** — so `hbig` is FALSE
at base two for every `η, ε, K, X`.  That is a genuine refutation of the base-two route (not
a stalled proof) and it explains the brief's own `b ≥ 3`.  Details: `DIRECTION.md` CURRENT
DIRECTIVE, `PENDING_WORK.md` §G4B.

## 🏁 2026-09-14: G4 disjunctivity PROVED (base four and base two), axiom-clean

`NormalNumbers.G4.isDisjunctive_four : IsDisjunctive 4 primeLambertFour` and
`isDisjunctive_two : IsDisjunctive 2 primeLambertFour` (`G4ScheduleAssembly.lean`), for the
constant `primeLambertFour = ∑' n, ω(n)/4ⁿ = ∑_p 1/(4ᵖ−1)` (`primeSumAtBase_four`).
Corollaries `every_binary_word_occurs`, `every_quaternary_word_occurs`.  Every one prints
`[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`, no local axiom in
the dependency cone.  The whole brief §4–§5 candidate argument is machine-checked.  Handoff:
`HANDOFF-2026-09-14-g4-lap12.md`.


## Where it stands

**The attended campaign is CLOSED.**  `G₄ = ∑_p 1/(4ᵖ−1) = ∑_n ω(n)/4ⁿ` is disjunctive in
base four and in base two (`G4.isDisjunctive_four`, `isDisjunctive_two`), and the whole brief
§4–§5 argument generalises: `G4.isDisjunctive_base : 3 ≤ b → IsDisjunctive b
(primeLambertAtBase b)` for every integer `b ≥ 3` (brief §7 follow-on item 1).  Every one of
those prints `[propext, Classical.choice, Quot.sound]`; `src/` contains **no `axiom`
declaration at all**, and no G4/G4B file carries a `sorry`.  As of review lap 16 the digit
theorem also yields its number-theoretic corollaries: `irrational_primeSum` (`∑_p 1/(bᵖ−1)`
is irrational for `b ≥ 3`) and `every_word_occurs_base_late` (every word, arbitrarily late).

**Live campaign: the attended ENTROPY EXPEDITION** (branch `wip/g4-entropy`; it supersedes
G5 for this run).  Brief §2–§4 are closed — `Sched.entropy_E0` / `Sched.entropy_E1` are
unconditional, axiom-clean theorems about the joint quantized sample of G₄ (section above).
The one statement whose truth value is still open is the §6 transfer `T_E`
(*`E0` for `Z^x_K` ⟹ `IsNormal 2 x`, for every `x`*), and review lap 8 identified the attack:
the sample is digit-local, so `T_E` would force the sampled positions to have density ≥ 1/2,
which the `d_α ∣ kIdx` structure appears to forbid.

**Base two (the number `∑_p 1/(2ᵖ−1)` itself) is refuted on this route and retired** — see the
lap-16 entry above and `DIRECTION.md`.  It remains a theorem of Tao–Teräväinen, not of this
repo; `PrimeLambertOscillation.phaseOscillation` is the honestly-disclosed hole of the old
base-two attempt and is not a prerequisite for anything proved here.

**Live campaign G5** (`DIRECTION.md` CURRENT DIRECTIVE, *past* the attended brief's finish
line — first thing to re-authorise when Trevor returns): replace the arithmetic input `ω` by
a named interface and prove the theorem for a class of additive weights, with two instances —
`ω` (re-deriving `isDisjunctive_base`) and `Ω`, giving the new constant
`∑_{q = pᵃ} 1/(b^q − 1)`.  The decisive case is C2 (`G4LocalContraction.norm_localSum_le`),
whose local model is `ω`'s indicator `1_{p∣m}` and must become the valuation `v_p(m)`.

**The Mahler-multiplier chapter** (previous campaign, complete): `M(g,k) < g^(k+1)` answers
Berend–Boshernitzan's stated open question, `sup_g M(g,k)/g^(k+1) = 1` is sharp, and at
`k = 1`, prime base, the sandwich is `p²/12 ≤ M(p,1) ≤ p²/4 + O(p)`.  `src/` carries exactly
TWO `sorry`s, both off every unconditional headline and both deep-analytic:
`exists_prime_nonresidue` (`MahlerDriftOne.lean`; a prime `q ∈ (p/3,p/2)` with `(p|q) = −1` —
a character sum over primes in an interval shorter than the reciprocity modulus, i.e.
Burgess/Karatsuba-strength) and `phaseOscillation` (`PrimeLambertOscillation.lean`).

## What's happened (newest first)

- **2026-09-14 (entropy review lap 8)** — inventory: build 🟢 8948 jobs, `entropy_E0`,
  `entropy_E1`, `isDisjunctive_four/two/base`, `primeSumAtBase_eq_primeLambertAtBase` all on the
  trust triple; `src/` holds exactly two `sorry`s, both off-campaign and disclosed.  No
  repetition across laps 1–7 (each closed a different brief section), but **crux-neglect did
  apply**: §6 `T_E` was untouched while §4 closed.  Direction REVISED — §5 (S) deprioritized,
  `T_E` promoted to THE objective, with a concrete decomposition (digit-locality lemma →
  sampled-position density → masked witness) written into the entropy CURRENT DIRECTIVE.
- **2026-09-14 (DEEP REFLECTION LAP, after G4 lap 9b)** — **ROUTE VERDICT: CONTINUE;
  brief §4 CLOSED; two recorded §5 parameter values REFUTED.**  Inventory: `lake build`
  green (8888 jobs), zero `sorry`s and zero axioms anywhere in the G4 wing, every G4
  headline on the trust triple, and **all five named §4 inputs now proved about the one
  concrete `gridFrame`**.  Trigger check: G-T1 stays retired, G-T2 and G-T4 did not fire,
  **G-T3 is now live and did NOT fire** — this lap re-derived every `ScheduleWitness`
  inequality from the Lean definitions and they close.  Two corrections to lap 9b's recorded
  paper check, each of which would have sent grind laps at a FALSE inequality:
  (a) `lam = 1` makes `smallPrimeBound`'s third error term `exp(+Θ(TL))`, so `hbudget` is
  unsatisfiable — `lam` must exceed `2e`; `lam = 13/2`, `lam' = e`, `Mc = ⌈10⁴·T·L⌉` works
  (`C > e^{lam}/log(lam/2e)`, minimised `≈ 3690` at `lam ≈ 6.4`).  (b) `N ≈ 10K log K` makes
  `hfar` false — `farC = log((X+Dm)/|P|) + log(log(X+Dm)+1)` has a `log log X = L` term that
  lap 9b dropped, so the retained depth must be the brief's `J = ⌈3 log₂ L⌉`.  New structural
  finding: the §5 schedule squeezes `K` from **both** sides —
  `0.58 log log L ≲ K ≲ log L/(2 log log L)` — the lower edge coming from D's medium range
  (`0.52·8^{−K/2}√(log Mc)` vs `εη`, with `log Mc ≥ log L` forced by C's `R = X^{1/(20Mc)}`).
  With `K` frozen that term diverges, which is precisely the mechanism behind the brief's
  "do not freeze `K`" prohibition.  Mandated next move: **`hB`**, the `X`-free witness
  inequality, with the derived sufficient hypothesis `K ≥ 33856·ℓ²·16^ℓ`.  Trigger G-T5
  registered (re-cost `K = ⌊log log L⌋` if a §5 inequality resists 6 laps).  Also corrected a
  stale STATUS claim: `src/` has TWO disclosed `sorry`s, not one (`phaseOscillation` in the
  old irrationality file was uncounted).

- **2026-09-14 (FRESH-MIND REVIEW LAP #2, after G4 lap 5)** — **Direction KEPT,
  mandated move CHANGED: stop producing inputs, close a named `Prop`.**  Inventory:
  zero `sorry`s and zero axioms in the whole G4 wing, every headline on the trust
  triple — and zero of `PropA`…`PropJackson` discharged after five laps.  Trigger
  **G-T1 retired as satisfied** (C3 is proved: `G4CRTInput.crt_input` plus the
  assembly `G4TransferMoment.norm_sampleAvg_prod_ee_le`; lap 3 eliminated the
  Shiu-type exponential moment entirely by a degree-`M` polynomial bound, so the
  route carries no external sieve dependency).  G-T2/G-T3 have not fired.  New
  trigger **G-T4** covers the abstract-frame ↔ concrete-object seam: a bookkeeping
  mismatch is fixed by one deliberate `G4Wiring` commit; a *mathematical* mismatch
  is an escalation, never a `Prop` edit.  Mandated: `G4Frame.lean` with
  `gridFrame` and the theorems `gridFrame_propA`, `gridFrame_propC`; then **D**,
  Jackson, B assembly, §5 schedule, in that order.

- **2026-09-14 (FRESH-MIND REVIEW LAP, G4 lap 3)** — **Course-correction: the crux
  moved from B to C, and C's arithmetic seed is proved.**  Laps 1–2 put all their
  effort into §4B; a crux-neglect check showed §4C — the half the brief itself says
  is unproved ("the growing-array moment and exponential-moment bounds still need
  proofs"; "the transfer from the independent residue model to the actual progression
  is not automatic independence") — had received zero laps.  This lap attacked it.
  Proved, unconditionally and `#print axioms`-clean: `minWeight_kronPow`, the
  **minimum distance of a product code** (`M` of minimum weight `d` ⟹ `M^{⊗K}` of
  minimum weight `d^K`); `minWeight_diff` (`D_s` has minimum weight 2, via telescoping
  row sums plus injectivity from `det T_s = s+1`); hence `minWeight_tensorDiff`
  (`‖supp(Aᵀq)‖₀ ≥ 2^K`); the column-mass bound `‖Aᵀq‖∞ ≤ 2^K‖q‖∞`; the layer choice
  `freqDepth K w = K+1+⌈log₄|w|⌉` with its window
  `4^{−(K+2)} ≤ |w|4^{−j} ≤ 4^{−(K+1)}`, its retention `j > K`, and its uniform
  admissibility `j_α ≤ K+1+⌈log₄(2^K D)⌉` over the whole Fourier box; and the §4C
  seed **`∑_α dist(w_α4^{−j_α},ℤ)² ≥ 4^{−4}8^{−K}`**.  The two powers are structurally
  distinct — `16^{−K}` is the squared window scale, `2^K` the code distance — so
  weakening the support bound to `2` would destroy the `8^{−K}` that §5 needs against
  `rK`.  Also checked on paper (not yet in Lean) that the §5 schedule is self-consistent
  on all four of the brief's essential comparisons, so the parameter budget is not the
  risk; C3 is.  `DIRECTION.md` CURRENT DIRECTIVE rewritten to G4 with triggers G-T1…G-T3.

- **2026-09-08 (DEEP REFLECTION LAP)** — **The certificate space is mapped; the
  run+jump chain is the route.**  Built an exact combinatorial model of the lower
  side (backgrounds `D`, junction `D → D'` costing `D'(p−D)`, vertex condition
  `−D_prev/D_next ∈ ⟨p⟩ (mod D)`; `M(p,1) =` max-bottleneck closed walk) and
  **checked it against the census**: equal at `p = 13,19,23,29,31`, off by one at
  `7,11,17` (`experiments/mahler_bg_cycle_model.py`).  Three refutations, each
  with a proof and a measurement: (i) orbit-free cycles are impossible — at the
  maximum `D_j` the divisibility forces `λ_j = 1`, the monodromy is parabolic, the
  solution space one-dimensional, so consecutive coprimality pins `D_i = O(1)` and
  the cost to `O(p)`; the `E = 0` column is empty for every prime `7 … 89`; the
  previous lap's `5/27` 3-cycle lead is dead (it exceeds the `3−2√2` cap the same
  argument gives, and its vertex condition fails directly).  (ii) The closed-form
  single-background frame `D = (p+j)/c` caps at **`p²/12` exactly** (`j = 1` is
  degenerate for every `c`, so `cj ≥ 6`) — family II is that frame's optimum.
  (iii) The multi-offset frame caps at `1/5` and has **no** uniform floor.
  **The finding**: the `E ≤ 1` optima all have one shape — the run of consecutive
  integers `p−b … b` plus the jump `b → p−b` — every vertex free except the
  bottom, giving `M(p,1) ≥ b(p−b−1)` whenever `−1 ∈ ⟨p⟩ (mod b)`, `3 ≤ b < p/2`.
  **2512 `(p,b)` pairs checked, zero mismatches**; ratio `≥ 0.1983` for every prime
  `11 … 20000`, median `0.2499`.  `b ∣ p+1` makes the condition free, so
  `b = (p+1)/3` gives `2/9` and `b = (p+1)/4` gives `3/16` — unconditional, and
  together they cover every prime `p ≢ 1 (mod 12)`.

- **2026-09-08 (REVIEW LAP)** — **The factor `3` is a drift, and it is not
  intrinsic.**  Derived and machine-checked the closed form of the one-junction
  certificate: `M ≈ min(p(p−D)/b, p(b−1)D/(b|g|))` with drift
  `g = −b·c₂⁻¹ − p (mod bD)`; drift `1` ⟺ `−1 ∈ ⟨p⟩ (mod D)` (family I's
  hypothesis, now *equivalent* to optimality rather than an artifact of
  `D = (p+3)/2`); a junction scaled by `k` divides `M` by `k` and needs
  `−k ∈ ⟨p⟩ (mod D)` (family II, `k = 3`).  **Refuted**: any closed-form
  background `D = (p+j)/2` caps at `1/3`, since `g ≡ −p (mod b)` is odd for
  `b = 2` and `j = 1` is degenerate.  **Measured** (`mahler_onejunction_scan.py`,
  literal `NumCert.Good` check): with a per-prime `D`, `M/⌊p/2⌋² ≥ 0.881` at
  every prime `17 … 127`.  Next: `MahlerBackgroundCert.lean` (family I with free
  `D, c₀, b`), then the arithmetic crux "∃ `D ∈ (p/3,p/2)` with `−1 ∈ ⟨p⟩`".

- **2026-09-08 (grind laps 2–3, post-reflection)** — **THE RUN+JUMP CHAIN THEOREM.**
  `MahlerRunJump.lean` (the certificate: `Θ(p)` backgrounds `b, b+1, …, p−b`, valid
  for every `M < b(p−b−1)`, via one generic two-denominator edge lemma) and
  `MahlerRunJumpWalk.lean` (the data from `p^f ≡ −1 (mod b)` and `T = 2φ((p−b)!)`,
  the two closed walks, the theorem).  **`mahler_lower_bound_runjump`: for every
  prime `p`, every `3 ≤ b < p/2` with `−1 ∈ ⟨p⟩ (mod b)`, `M(p,1) > b(p−b−1) − 1`.**
  Corollaries: `3 ∣ p+1` ⟹ `M(p,1) > 2(p+1)(p−2)/9 − 1`; `4 ∣ p+1` ⟹
  `M(p,1) > (p+1)(3p−5)/16 − 1`; so **`3/16 · p²` for every prime `p ≢ 1 (mod 12)`**
  (`p ≥ 11`).  Against the exact census the bound is EXACT at `(p,b) = (13,5)`,
  `(23,10)`, `(31,14)` (`M = 35, 120, 224`), and never exceeds `M(p,1)` at any
  admissible pair `p ≤ 31`.  All trust triple, no `sorry`.
  **T3 endpoint (stated per the directive)**: the UNCONDITIONAL constant is `3/16`
  for `p ≢ 1 (mod 12)` and `1/12` (family II) for `p ≡ 1 (mod 12)`; the clean
  CONDITIONAL `1/4` is `mahler_lower_bound_runjump_near_half` (`p = 2b + j`,
  `−1 ∈ ⟨p⟩ (mod b)` ⟹ `M(p,1) > (p−j)(p+j−2)/4 − 1`), whose hypothesis is
  measured to hold with `j ≤ 33` at every prime `p < 2000`
  (`experiments/mahler_runjump_admissible.py`).  Removing the hypothesis is an
  Artin-type short-interval statement, not grind work.

- **2026-09-08 (grind lap 2)** — **The uniform prime lower bound.**
  `MahlerNumCert.lean` (generic numerator-certificate layer over
  `AdderEscapeCert`), `MahlerFamilyI.lean` (one junction over `1/D`,
  `D = (p+3)/2`: `M(p,1) > ⌊p/2⌋² − 2` when `p^k ≡ −1 (mod D)`; instances
  `M(41,1) ≥ 399`, `M(199,1) ≥ 9799`), `MahlerFamilyII.lean` (second junction =
  the first scaled by `3`: `M(p,1) > (⌊p/2⌋² − 2)/3` for **every** prime `p ≥ 17`,
  via Euler `e = 3φ(D)`).  All trust triple, no `sorry`.

- **2026-09-08 (REVIEW LAP)** — **The prime lower side reformulated as a long
  addition; the first uniform law proved.**  `MahlerBurstDigit.lean` (new,
  trust triple): the `k = 1` background certificate in **adder form** — carry
  `bgCarry` and emitted digit `bgDigit` for "constant background `b` plus burst
  `N`", with `bgResidue_div_eq_bgDigit` identifying the window digit at distance
  `d = i+1` with the digit emitted at position `i`, and
  `mahler_lower_bound_bg_adder` restating the bound with one condition per digit
  position (and no `hstab` — the carry dies when the burst runs out).  On top of
  it, the **first uniform-in-`p` brick**: `bgDigit_zero_ne`, for odd `g ≥ 5` and
  any burst with `B ≡ −4 (mod g)`, position `0` misses the target `g−1` for
  *every* `m < ⌊g/2⌋²` — because the digit sum is `2(u−r) (mod g)` and
  `2(u−r) ≡ −1` forces `u − r ≡ Q`.  `B ≡ −4 (mod p)` is the law satisfied by
  the extremal burst at every prime `7 … 59` (exact digit-DFS).  Route settled
  by data: the burst family holds `M/⌊p/2⌋² ≥ 0.43` up to `p = 59`, so it *is*
  uniformly quadratic — the gap is a formula, not existence.  Closed-form bursts
  `B = p^K(p−c) − 4` REFUTED (only `Θ(p)`).  Engine validated end-to-end by
  `mahler_lower_bound_base29` (`M(29,1) ≥ 140`, `decide +kernel`).
- **2026-09-08 (autonomous, lap 6)** — **The escape engine is a theorem.**
  `AdderEscapeCert.lean`: a decidable automaton certificate (tail intervals,
  per-channel carries, block-free channel digits) plus a witness pair of closed
  walks gives an irrational `α` with the block never occurring in `m·α`,
  `1 ≤ m ≤ M` (`escape_mahler_lower_bound`, trust triple).  Next brick: the
  `(7,2)` instance `M(7,2) ≥ 176`, and exact `k = 1` values at `11, 17`.
- **2026-09-08 (autonomous, laps 3–5)** — **Prime lower side: five new
  certificates, the burst law, and period-2 backgrounds.**
  `MahlerPrimeLowerBound.lean`: `M(17,1) ≥ 63`, `M(31,1) ≥ 224` (exact),
  `M(59,1) ≥ 840 = ⌊59/2⌋² − 1` (beyond the census).  All census bursts are
  `B = p^j κ − 4S_j` with `κ ≡ −8/3 (mod p)`; the family is NOT uniformly
  quadratic (ratio decays past `p ≈ 60`).  `MahlerLowerBoundPeriod2.lean`:
  the `p = 19` extremal shadows `1/(Q+1)`, a period-2 background; formalized
  as a base-`g²` certificate through the Pillai digit bridge, giving
  `M(19,1) ≥ 80` (exact).  General prime lower bound still open
  (`PENDING_WORK.md` §top).
- **2026-09-08 (autonomous, lap 2)** — **The universal constant is `1`, in Lean.**
  `MahlerLowerBoundSmooth.lean`: `mahler_lower_bound_smooth` (`t ∣ g^j`, `t < g`
  ⟹ `M(g,k) ≥ t(gᵏ−1)`; the divisor bound is `j = 1`), instances
  `M(630,1) ≥ 393125` (`0.9905·630²`) and `M(26250,1) ≥ 688878756`
  (`0.99973·26250²`), and `mahler_constant_one_sharp`: for every `k ≥ 1`,
  `ε > 0`, `L`, some base `g ≥ L` has `M(g,k) ≥ (1−ε)g^(k+1)` (Dirichlet on
  `log 3/log 2`, `g = 2^a3^b L`, `t = min(2^a,3^b)²L`).  With
  `mahler_multiplier_lt` this closes the "sharp universal constant" wing:
  `sup_g M(g,k)/g^(k+1) = 1`, not attained.  Formalizes the host's
  `docs/mahler-universal-constant-is-one-2026-09-07.md` (its lower side).
- **2026-09-08 (autonomous)** — **The `(7,2)` extremal orbit dissected; escape
  engine started.**  The instrument's SCC for block `00` is three cycles
  (`1/4`, `4/5`, and `0.(541251512)₇`); their mixing escapes all `m ≤ 175`
  exactly (numeric, 3000 digits), and the period-9 point IS the exact witness
  (`176` is the first `m` that hits).  Its shadow denominators `5,5,5,28,4,4,35,5,5`
  are the drop mechanism verbatim, with `MahlerFarey`'s jump estimate tight.
  No burst family reaches it (sign structure of carries), so the exact lower
  side at `k ≥ 2` needs the automaton: `AdderEscape.lean` lands the true-carry
  recursion and the digit formula for `m·x` (trust triple).  Plan in
  `PENDING_WORK.md` §top.
- **2026-09-07 (autonomous)** — **`g^(k+1)/4` refuted for `k ≥ 2`; first `k = 2`
  prime lower bounds.**  Exact `M(7,2) = 176 = 0.51·7³` (new; with `M(3,2) = 8`,
  `M(5,2) = 48`: ratios `.30 .38 .51`, climbing) — the `k = 1` constant `1/4` does
  not persist, and the shadow-denominator DROP found in `MahlerQuarter.lean` is
  where the extra multipliers live.  `MahlerPrimeLowerBoundBlock.lean`
  (`mahler_lower_bound_bg_block`, trust triple): `M(5,2) ≥ 44`, `M(7,2) ≥ 103`
  in the kernel.  The background+burst family caps at `102` at `(7,2)`: the
  `k = 2` extremal orbit (run blocks `00`/`66`) is a new shape to find.
- **2026-09-07 (autonomous)** — **`M(g,1) ≤ (g² + 6g + 1)/4` for odd primes: the
  multi-scale bound lands at the census constant `1/4`** (`MahlerQuarter.lean`,
  `Mahler.mahler_multiplier_quarter`, trust triple).  The denominator-jump engine
  of `MahlerFarey.lean` iterated: the canonical shadow's denominator strictly
  increases every stage once `d·μ·g·(Q−d) ≤ (μ−d)(μ−2d)·Q`, which at
  `μ = (g+1)(g+5)/4` has discriminant `−4μ²`.  Retires `g(g+1)/2` for `g ≥ 5`.
  ⚠️ Found while formalizing: for `k ≥ 2` the shadow denominator can drop by a
  factor `g`, so `g^(k+1)/4` at `k ≥ 2` is NOT claimed (`PENDING_WORK.md` top).
- **2026-09-02 (autonomous)** — **`M(g,k) < g^(k+1)`: Berend–Boshernitzan's open
  question (Acta Arith. 66, p. 320) answered YES** (`MahlerMultiplierStrict.lean`,
  `Mahler.mahler_multiplier_lt`, ledger `Literature.berendBoshernitzan_strict_holds`,
  trust triple).  The B–B paper was read in full (host findings, archived): the
  `t(gᵏ − 1)` lower bound and `B = 125` are their Thm 3.1 / Ex 3.1 — re-attributed.
- **2026-09-02 (autonomous)** — **Mahler run branch settled at `gᵏ`; prime-base
  conjecture refuted** (`MahlerRunBranch.lean`).  For prime `g`, if `0ᵏ` or `(g−1)ᵏ`
  occurs i.o. in `α` then some `m ≤ gᵏ` has any `k`-block i.o. in `m·α`
  (`mahler_multiplier_of_zero_runs` / `_pred_runs`, trust triple) — the Liouville
  witnesses' branch is pinned to `[gᵏ − 1, gᵏ]`.  Exact adder-machine computation
  (`experiments/mahler_exact_M.py`) gives `M(g,1)` for `g ≤ 29`: for odd primes it
  tracks `((g−1)/2)²`, so `M(g,k) = Θ(g^(k+1))` for primes too and the room is on the
  LOWER side, in the run-free branch (Farey-hopping orbits).  `PENDING_WORK.md` top.
- **2026-09-02 (review lap)** — **Mahler lower bound sharpened from `gᵏ − 1` to
  `t·(gᵏ − 1)`** (`MahlerLowerBoundGeneral.lean`).  Own construction:
  `α = B·liouvilleNumber g` turns the multiplier problem into a digit problem
  about the multiples of one integer; `B = c` for `g = t·c` stretches the budget
  by `t`.  Even bases: `M(g,k) ≥ (g/2)(gᵏ−1)`.  Numerically sharp for this `α`.
  The chapter's open question moves to **prime bases, upper side**.
- **2026-09-01** — **CFScheduleA schedule route encoded as `Prop` nodes; `src/`
  sorry-free** (section below): `VarianceBlockCountPsiPushed` refuted in-kernel
  (`varianceBlockCountPsiPushed_false`), `SchedABlockLinear` open/choice-opaque,
  every dependent conditional.  Same lap: tower floors (C2 cardinality-optimal,
  `c5_sharp`, B–B `M(3,1)=2` lower half), N3 `e` factorial-kick machine, N2
  Stoneham base-6 readout.  Every pre-existing axiom set unchanged (census).
- **2026-09-01** — Mahler chapter made two-sided: upper bound sharpened
  `(g+3)gᵏ → g^(k+1)` (universal covering lemma + shadow-rational escape, closing
  the `g = 2` gap), lower bound `gᵏ − 1` proved from `liouvilleNumber g`.
  Furstenberg 1967 dense-orbit theorem wired via re-homed ×p×q rigidity.
- **2026-09-01** — C10 tower claim proved via a *reduction finding* (the family
  splits; the dossier's 540 396-state certificate is not needed).  Tower brief
  C1–C10 closed.  `PiSqBBP` Aristotle faithfulness cross-check passed.
- **2026-08-31** — ledger hotspot edges; π²-BBP proved.
- **2026-08-30** — `adder_sixfold_disjunction` proved (novel candidate theorem);
  tower phase A; literature ledger first pass (`Literature.lean`).
- **2026-08-26** — `IsNormal.isDisjunctive` (unconditional API gap) closed; Track
  D3 `quadratic_irrationals_disjunctive_of_hypothesisM`; Comparator harness and
  the Phase-3 publishing-prep pass completed locally.
- **2026-08-25** — image-Khinchin headline complete (`ae_tail_average_tendsto`
  proved via the L²-variance/finite-truncation route); B6 affine family exceeded.

## CFScheduleA schedule route encoded as Prop nodes (2026-09-01)

- **`src/` is sorry-free.**  The two disclosed `sorry`s of the abandoned interleaved-
  schedule route (`CFScheduleA.lean`) are re-encoded as named conjecture-graph nodes
  (`def … : Prop`, statements verbatim), with every dependent taking the node as an
  explicit hypothesis (Trevor's decision, 2026-09-01):
  - `VarianceBlockCountPsiPushed` — **RED / refuted.**  Kernel-checked negation
    `varianceBlockCountPsiPushed_false` (`CFScheduleARefuted.lean`, trust triple): the
    bound fails already for `ψ = id`, `v = [1]`, `wx' = [2,…,2]` — a cylinder-restricted
    second moment centred at the global mean is `Θ(n²)`.  Dependents
    `psi_pushed_chebyshev_brick` → `gaussMeasure_aggregate_psi_pushed_le` →
    `exists_scale_cfCylinder_psi_avoid_zbad_poly` are vacuous and say so.
  - `SchedABlockLinear` — **OPEN.**  Choice-opaque (`schedA` is a `Classical.choose`
    recursion whose spec carries no block upper bound), argued false for this construction
    in `OBSTRUCTION-2026-08-24-block-measure-budget.md`.  Dependents `schedA_block_geom` →
    `schedA_hfreq_x`/`_z` → `exists_interleaved_affine_witness`.
- Every other constant's axiom set is unchanged (before/after `collectAxioms` census over
  all NormalNumbers modules); all headlines below keep exactly the trust triple.
- **Tower deductions kernel-checked** (`AdderTowerDeductions.lean`, same day): the
  single-multiplier floor `exists_irrational_mul_omits_digit` (base `b ≥ 3`, any digit,
  any `m ≠ 0`: some irrational `X` has `m·X` omitting the digit entirely — Cantor-set
  encoding of `Set ℕ` through `realOfDigits`), hence **C2 is cardinality-optimal**
  (`no_single_multiplier_all_digits`), **B–B `M(3,1) = 2` lower half**
  (`Literature.berendBoshernitzan_M31_lower_holds`; with C1 both halves are in-kernel)
  and `M(g,1) ≥ 2` for all `g ≥ 3`; and **C5 sharpened** (`c5_sharp`: the `X + 4Y`
  channel is unnecessary — a two-line corollary of C1).  All trust triple.
- **N3 `e` factorial-kick machine landed** (`EFactorialKick.lean`, same day): in every
  base `b`, a run of `k` zeros / top digits of `e` at position `n` with
  `bᵏ > eSplit b n + 1` pins the rational surrogate `fract (bⁿ·A(M)/M!)` to an explicit
  window of width `< 1/(M+1) + b⁻ᵏ` (`eSurrogate_window_of_zeroRun`/`_of_maxRun`,
  unconditional); the CITED node `EIrrationalityExponentTwo` caps runs at `(1+ε)n`
  (`eRun_le_of_exponentTwo`); numerator rigidity `A(M) ≡ A(M mod p)` (`eNum_zmod`).
  Trust triple throughout.
- **N2 base-6 Stoneham readout PROVED** (`StonehamBase6.lean`, same day):
  `stoneham_base6_readout` — the base-6 orbit of `α₂,₃` at position `n` is
  `(3^a mod 2^c)/2^c` up to a `2^{−Θ(3^{j*+1})}` error (`a = n−(j*+1)`, `c = 3^(j*+1)−n`),
  so the base-6 digits of `α₂,₃` are a transcript of `3^a mod 2^c`.  Trust triple.

## Outstanding

### Short-term (mirrors PENDING_WORK top)
Campaign **entropy expedition** (ACTIVE), in order:
1. **`G4EntropyLocality.lean`** — digits agreeing on the window `[2k, 2k+m)` give the same
   `blockVal`, hence the same `ZVec`/`jointLaw`/`H₂`.  Mechanical, load-bearing.
2. **`G4EntropyPositions.lean`** — `0 < kIdx` (else `b₀ = t_α` forces `gridV` constant, false),
   hence `kIdx ≥ d_α ≥ 1 + Q·D₀`; count `|S_K ∩ [0,L)| ≤ H_K m_K L / (2(1+Q_K D₀_K))`.
3. **`G4EntropyTransfer.lean`** — `E0` as a limit `Prop`, `E0 G4` from `entropy_E1`, the
   `T_E`/`T_S`/`T_mix` `Prop`s, the masked witness via `realOfDigits`, and `not_T_E`.
4. Then (and only then) brief §5's (S): `H₂` subadditivity + a checked entropy-to-TV
   inequality.  And the §6 positive branch: which extra arithmetic property (translated-grid
   averaging) defeats the witness.

Campaign **G5** (dormant for this run), in order:
1. **The decisive probe in Lean**: generalise C2 (`G4LocalContraction.norm_localSum_le`) from
   an indicator model to a valuation model — default class `v_p = 0` (mass `≥ 1/2`), active
   classes `v_p = 1` (mass `(1/p)(1−1/p)`, phase `xᵢ`), junk `v_p ≥ 2` of mass `≤ k/p²`.
   Paper check: `∑_p k/p² = O(T) = L^{0.02+o(1)}` against a gain `L^{1−o(1)}` — closes.
2. The weight interface itself (`w(n) ≤ log₂ n`, `w(dm) = w(d)+w(m) −` defect), then
   `G4Transport`, `G4Remainder`/`G4FarTail`/`G4MediumPrimes`, then `G4SmallPrimeVector`.
3. The `Ω` series identity `∑_n Ω(n)/bⁿ = ∑_{q prime power} 1/(b^q − 1)`.
4. Second target if the port stalls twice: **effective** disjunctivity — the schedule is
   explicit and the samples are `n < X`, so a first-occurrence bound `N(b, ℓ)` is already
   inside the proof; extracting it means `homit : ∀ m` ⇝ `∀ m ≤ M₀` through `G4Wiring`.
5. Legacy (not this campaign): cited-only ledger nodes (`philipp_psi_mixing`,
   `vandehey_matrix_action`); `k ≥ 2` Mahler lower side via the escape engine.

### Long-term
The conjecture graph toward the sink `IsNormal 2 (Real.log 2)`: the ln-two
ladder (`LnTwoFreq`, `ConditionalDisjunctive`), the run tower
(`LnTwoExpSep`/`LnTwoPolySep`), the shared Diophantine-wall interface.

### To completion
No axiom debt to discharge — "completion" here means new nodes/edges, not a
shrinking ledger.  The two `CFScheduleA` residues are `Prop` nodes as of 2026-09-01.

## Axiom ledger

Real `#print axioms` output, re-run this lap (2026-09-14 review lap 16, HEAD `4991939`,
build 🟢 8935 jobs).  Every UNCONDITIONAL headline: trust triple only; the single exception is
flagged.  G4 rows come first.  Nothing in the G4 wing has a `sorry` or an axiom — its debt is
carried honestly as the named unproved `Prop`s `SeparatingFrameExists` / the
`ScheduleWitness` hypothesis, which is exactly what makes `isDisjunctive_four_of_witness`
conditional.  **Brief §4 is closed**: all five of `PropA`, `PropB`, `PropC`, `PropD`,
`PropJackson` are now *theorems* about the concrete `gridFrame`, two of them modulo named
real inequalities that live in the witness.

| headline theorem | paper claim | `#print axioms` shows | verdict |
|---|---|---|---|
| `G4.Sched.entropy_E0` | **sample entropy `H₂(Z^{G₄}_K) > (1/5)m_K H_K`** for every admissible `K ≥ 33856` — UNCONDITIONAL, about the quantized sample only (brief §4 E0) | trust triple | 🟢 clean (entropy lap 6) — NOT a normality claim |
| `G4.Sched.entropy_E1` | **`H₂ ≥ m_K H_K − 50√K·H_K`** for `K ≥ 160000` — UNCONDITIONAL (brief §4 E1, `C = 50`) | trust triple | 🟢 clean (entropy lap 7) — implies E0's ratio `≥ 1 − 200/√K` |
| `G4.isDisjunctive_base` | **`3 ≤ b → IsDisjunctive b (∑_n ω(n)/bⁿ)`** — UNCONDITIONAL, the campaign endpoint generalised (brief §7.1) | trust triple | 🟢 clean — no `sorry`, no `native_decide`, no local axiom in the cone |
| `G4.isDisjunctive_four` / `isDisjunctive_two` | **G₄ disjunctive in base 4 and base 2** — UNCONDITIONAL, the attended frozen endpoint | trust triple | 🟢 clean |
| `G4.isDisjunctive_primeSum` / `every_word_occurs_base` / `isDisjunctive_root` | prime-sum form, every finite word, root bases (uncond.) | trust triple | 🟢 clean |
| `G4.irrational_primeSum` | **`3 ≤ b → Irrational (∑' p, 1/(bᵖ−1))`** (uncond.) — the `b ≥ 3` half of the Tao–Teräväinen family, independent route | trust triple | 🟢 clean (lap 16) |
| `G4.every_word_occurs_base_late` / `every_binary_word_occurs_late` | every word occurs *arbitrarily late*, hence infinitely often (uncond.) | trust triple | 🟢 clean (lap 16) |
| `IsDisjunctive.irrational` / `IsDisjunctive.exists_ge` | disjunctive ⇒ irrational; every interval hit arbitrarily late (uncond., any base) | trust triple | 🟢 clean (lap 16) |
| `G4.isDisjunctive_four_of_witness` | G4 disjunctive base 4 — **CONDITIONAL** on a `ScheduleWitness` for every omitted cylinder (= brief §5) | trust triple | 🟢 clean; the hypothesis IS the residual candidate content — never report as the endpoint |
| `G4.separatingFrameExists_of_witness` | §5 witness ⇒ `SeparatingFrameExists` (uncond.) | trust triple | 🟢 clean — the audit surface: one frame, all five props |
| `G4.isDisjunctive_four_of_frames` / `…_two_of_frames` | base 4 / base 2 — CONDITIONAL on `SeparatingFrameExists` | trust triple | 🟢 clean, conditional |
| `G4.Frame.finite_contradiction` | §4E finite separating test from A–D + Jackson (uncond.) | trust triple | 🟢 clean |
| `G4.gridFrame_propA` | **§4A** exact affine Lambert transport on the concrete grid (uncond.) | trust triple | 🟢 clean — input CLOSED |
| `G4.gridFrame_propC` | **§4C** uniform joint small-prime Fourier control, whole box (uncond.) | trust triple | 🟢 clean — input CLOSED, closed-form `smallPrimeBound` |
| `G4.Frame.propJackson` | **§4E** product-Fejér smoothing, `κ = 1/(res√(D+1))`, `Λ = (2D+1)^r`, EVERY frame (uncond.) | trust triple | 🟢 clean — input CLOSED, no side conditions |
| `G4.gridFrame_propD_of_bounds` | **§4D** three ranges + far tail ⇒ `PropD` (uncond., given `hbig`, `hfar`) | trust triple | 🟢 clean — input CLOSED modulo two §5 inequalities |
| `G4.gridFrame_propB_of_bound` | **§4B** zonotope tube volume ⇒ `PropB` (uncond., given `hB`) | trust triple | 🟢 clean — input CLOSED modulo one §5 inequality |
| `G4.bigAvg_le'` / `G4.farAvg_le` | §4D medium (`Y`-split, signed L²) and far-tail closed forms (uncond.) | trust triple | 🟢 clean — the brief's §4D tripwire honoured |
| `G4.log_det_one_add_tensorGram_le'` | §4B spectral `log det(1+T_{K²}^{⊗K}) ≤ r(log2+23√K)` (uncond.) | trust triple | 🟢 clean |
| `G4.schedule_budget` | §5 C4: `C·K^{2K+1}8^K < c·L` eventually (uncond.) | trust triple | 🟢 clean |
| `PrimeLambert.primeSumAtBase_four` | `∑_p 1/(4ᵖ−1) = ∑_n ω(n)/4ⁿ` (uncond.) | trust triple | 🟢 clean — the endpoint's identity |
| `PrimeLambert.isDisjunctive_two_of_four` | base-four ⇒ base-two dictionary (uncond.) | trust triple | 🟢 clean |
| `exists_absolutely_normal_cf_normal` | Becher–Yuhjtman 2019 Thm 1 (uncond.) | trust triple | 🟢 clean |
| `exists_absolutely_normal_cf_normal_khinchin` | image-Khinchin (uncond.) | trust triple | 🟢 clean |
| `isNormal_log_two_of_equidistributed` | conditional ln-two | trust triple | 🟢 clean (hypothesis is a named `Prop`, not an axiom) |
| `Mahler.mahler_multiplier` | Mahler 1973 Thm M, sharpened | trust triple | 🟢 clean |
| `Mahler.mahler_lower_bound` / `…_even` | our own lower bounds | trust triple | 🟢 clean |
| `Mahler.mahler_multiplier_quarter` | our own `M(p,1) ≤ (p²+6p+1)/4`, odd prime | trust triple | 🟢 clean |
| `Mahler.mahler_lower_bound_smooth` / `mahler_constant_one_sharp` | our own `sup_g M(g,k)/g^(k+1) = 1` | trust triple | 🟢 clean |
| `Mahler.mahler_lower_bound_bg_adder` / `bgDigit_zero_ne` | our own adder-form certificate + the uniform `B ≡ −4 (mod p)` law | trust triple | 🟢 clean |
| `Adder.FamilyI.mahler_lower_bound_family_I` / `…_prime_family_I` | our own `M(p,1) > ⌊p/2⌋²−2` when `−1 ∈ ⟨p⟩ mod (p+3)/2` | trust triple | 🟢 clean |
| `Adder.FamilyII.mahler_lower_bound_family_II` / `…_prime_family_II` | our own uniform `M(p,1) > (⌊p/2⌋²−2)/3`, every prime `p ≥ 17` | trust triple | 🟢 clean |
| `Adder.Background.Two.mahler_lower_bound_two_cycle` / `…_prime_seven_mod_twelve` | our own `M(p,1) > p(p−1)/6 − 1`, every prime `p ≡ 7 (mod 12)` | trust triple | 🟢 clean |
| `Adder.Background.mahler_lower_bound_drift_one` | our own `M(p,1) ≥ D(p−1)/2 − 1` per drift-one background | trust triple | 🟢 clean |
| `Adder.RunJump.mahler_lower_bound_runjump` / `…_three` / `…_four` | our own run+jump chain: `M(p,1) > b(p−b−1)−1` for `−1 ∈ ⟨p⟩ (mod b)`; `2/9` and `3/16` for `3 ∣ p+1`, `4 ∣ p+1` | trust triple | 🟢 clean |
| `Adder.Farey.mahler_lower_bound_farey` | our own two-background Farey certificate, `⌊p/2⌋²−2` | trust triple | 🟢 clean |
| `Adder.Background.mahler_lower_bound_prime_drift_one` | our own `M(p,1) > ≈p²/6`, **conditional** | trust triple **+ `sorryAx`** | 🔴→ correctly conditional: its one hypothesis `exists_prime_nonresidue` (prime `q ∈ (p/3,p/2)` with `(p\|q) = −1`) is Linnik-strength, disclosed, and reaches NO unconditional theorem |
| `Mahler.mahler_lower_bound_base29` | our own `M(29,1) ≥ 140` | trust triple (`decide +kernel`, no `native_decide`) | 🟢 clean |
| `Mahler.mahler_multiplier_of_zero_runs` / `…_pred_runs` | run branch at `gᵏ` (prime `g`) | trust triple | 🟢 clean |
| `Mahler.mahler_multiplier_lt` / `Literature.berendBoshernitzan_strict_holds` | `M(g,k) < g^(k+1)` (B–B open question) | trust triple | 🟢 clean |
| `Literature.mahler_theoremM_holds` | Mahler 1973, all `g` | trust triple | 🟢 clean |
| `Literature.berendBoshernitzan_bound_holds` | B–B 1994 `2g^(k+1)`, all `g ≥ 2` | trust triple | 🟢 clean |
| `Literature.furstenberg_dense_orbit_holds` | Furstenberg 1967 | trust triple | 🟢 clean |
| `varianceBlockCountPsiPushed_false` | refutation of the schedule brick (own) | trust triple | 🟢 clean |
| `Adder.exists_irrational_mul_omits_digit` / `Adder.c5_sharp` | tower floors (own) | trust triple | 🟢 clean |
| `stoneham_base6_readout` | N2 base-6 Stoneham readout (own) | trust triple | 🟢 clean |
| `Literature.berendBoshernitzan_M31_lower_holds` | B–B `M(3,1)=2`, lower half | trust triple | 🟢 clean |
| `Adder.adder_sixfold_disjunction` | novel candidate | trust triple | 🟢 clean (kernel-tier cert) |
| `Adder.c10_disjunction_universal` | tower C10 | trust triple | 🟢 clean |
| `IsNormal.isDisjunctive` | unconditional API gap | trust triple | 🟢 clean |
| `quadratic_irrationals_disjunctive_of_hypothesisM` | Track D3, conditional | trust triple | 🟢 clean |

Math-axiom count (🟢+🟡+🟠): **0**.  🔴: none.  `src/` carries exactly TWO disclosed
`sorry`s (a stale earlier count said one): `exists_prime_nonresidue`
(`MahlerDriftOne.lean`, Linnik-strength, reached only by the CONDITIONAL
`mahler_lower_bound_prime_drift_one`) and `phaseOscillation`
(`PrimeLambertOscillation.lean`, the OLD irrationality endpoint, which the G4 kickoff
explicitly excludes as a prerequisite and which no G4 declaration imports).  Every
unconditional headline above is `sorryAx`-free, and **no G4 file has a `sorry`**.  The two
former `CFScheduleA` schedule residues are named `def … : Prop` nodes, which no headline
depends on.

**Honest reading of the G4 row set**: the ledger is axiom-clean, but that certifies the
*proofs*, not the endpoint.  G4 is not done: `isDisjunctive_four_of_witness` rests on the
`ScheduleWitness` hypothesis, which is brief §5 and is unproved.  What changed at this lap
is that the hypothesis is now a finite list of **explicit real inequalities in explicit
parameters** rather than any unproved mathematics — and those inequalities were re-derived
from the Lean definitions this lap and do close.

## Pointers

`DIRECTION.md` (**binding directive** — G4 §5, triggers G-T2…G-T5) ·
`KICKOFF-2026-09-14-g4-disjunctivity.md` + the brief at
`~/personal/claude/knowledge/core/projects/normal-numbers-g4-disjunctivity-fable-handoff-2026-09-14.md` ·
newest baton: `ls HANDOFF-2026-09-14-g4-lap*.md | sort -t p -k2 -n | tail -1` ·
`PENDING_WORK.md` §Reflection 2026-09-14 (the §5 re-derivation, the two refuted parameter
values, the two-sided `K` window) · `CHECK-g4-route-deviations.md` (host's independent route
checks) · `ROADMAP.md` · `papers/literature-review.md` §G4 chapter ·
`BRIEF-literature-statements.md` (the novelty tripwire ledger)

---

## Historical campaign ledger (superseded state snapshots)

Everything below is retained as proof-campaign history. In particular, its claims
that image-Khinchin or `ae_tail_average_tendsto` are open are no longer active.

**Track D update (2026-08-26):** the unconditional API gap
`IsNormal.isDisjunctive` is proved, axiom-clean, fully built, and committed as
`b755fd5`.  D3 is also ✅: `QuadraticDisjunctive.lean` freezes Axiom M_b as the
named Prop `QuadraticHypothesisM`, proves the independent missing-word
Hausdorff-dimension bound from an endpoint-safe finite cover, and proves the
exact theorem `quadratic_irrationals_disjunctive_of_hypothesisM`.  For every
`b ≥ 2`, `QuadraticHypothesisM b` alone implies that every quadratic
irrational is `b`-disjunctive.  Guarded axioms for the dimension theorem and
exact wrapper are the standard trust triple, and the full build is green at
8766 jobs.  A fresh review-lap statement probe also checked definitionally that
`QuadraticHypothesisM` is exactly the closed/forward-invariant/dimension-`< 1`
avoidance hypothesis and contains no encoded disjunctivity conclusion.  The
older B5′/B6 status below is retained as historical campaign state.

**B5′ COMPLETE + axiom-clean (10 headlines); B6 affine-images DONE + EXCEEDED (single-map + FULL affine family, any real `r`, `q>0`, all trust-triple). ONE open obligation left in the whole repo: `ae_tail_average_tendsto` — the log-tail SLLN feeding the image-Khinchin headline (witness CF-normal + all affine images CF-normal + Khinchin-typical).** · **Build**: 🟢 green (8760 jobs) · **Updated**: review lap #3 · 2026-08-25 · `53e454c`+

## Where it stands

**B5′ + all of B6-affine are DONE and axiom-clean; the sole live frontier is the
image-Khinchin stretch, reduced to ONE strong-law crux.** The B5′ expedition (ten
headline theorems), the B6 single-map `exists_cfNormal_and_affine_cfNormal`, and the
B6 Tier-2 **full affine family** `exists_cfNormal_and_affine_family_cfNormal'` (any
real `r`, `q>0` — the faithful Vandehey §7 statement) are all proved and
`#print axioms`-clean (trust triple only). B6 was closed via the MEASURE route
(existence is a.e.-trivial; the false schedule crux is dead code, marked REFUTED).
**The one remaining open obligation across `src/` is `ae_tail_average_tendsto K`
(`CFAeKhinchin.lean:343`)**: `∀ᵐ x ∂γ, logBirkhoffSum K n x / n → ∫ logTailFn K dγ`.
Only `K=0` is consumed (g-direct route) — it closes `ae_khinchinTypical` (currently
`+sorryAx`) which grafts into the affine family to yield the image-Khinchin headline.
This is the genuine research core: a **strong law (a.e. Birkhoff convergence) for the
UNBOUNDED log-digit function** under the Gauss measure — no ergodic theorem in
mathlib, so it goes through an L²→a.e. variance argument mirroring the PROVEN
`ae_orbit_freq`. Route (DIRECTION.md CURRENT DIRECTIVE, Approach B / finite
truncation): (1) `integral_blockCount_cross` two-cylinder 2nd-moment identity
[LANDED, axiom-clean], (2) `abs_cov_two_cyl_pair_le` general-`(i,j)` two-cylinder
covariance bound [LANDED, axiom-clean], (3) `variance_truncated_le` uniform-in-M
variance, (4) MCT limit → `variance_logBirkhoffSum_le`, (5) Chebyshev+Borel–Cantelli+
monotone squeeze (transcribe `ae_orbit_freq`), (6) graft → image-Khinchin headline.

- **Track A** (base-b normality): Wall, the ln 2 reduction (conditional on the
  correct equidistribution hypothesis), Stoneham — axiom-clean.
- **Tier 1 = Becher–Yuhjtman** (IMRN 2019): `exists_absolutely_normal_cf_normal`
  — an explicit real absolutely normal ∧ CF-normal. Apparently the first
  formalization in any prover. Axiom-clean.
- **Tier 2 = expedition headline**: `exists_absolutely_normal_cf_normal_khinchin`
  — additionally Khinchin-typical. Axiom-clean.
- **B6 = affine images (active)**: `exists_cfNormal_and_affine_cfNormal` — target
  proved MODULO the crux `sorry`; depends on `sorryAx` until the schedule closes.

## What's happened (newest first)

- **2026-09-08 (grind lap 2)** — **The uniform prime lower bound.**
  `MahlerNumCert.lean` (generic numerator-certificate layer over
  `AdderEscapeCert`), `MahlerFamilyI.lean` (one junction over `1/D`,
  `D = (p+3)/2`: `M(p,1) > ⌊p/2⌋² − 2` when `p^k ≡ −1 (mod D)`; instances
  `M(41,1) ≥ 399`, `M(199,1) ≥ 9799`), `MahlerFamilyII.lean` (second junction =
  the first scaled by `3`: `M(p,1) > (⌊p/2⌋² − 2)/3` for **every** prime `p ≥ 17`,
  via Euler `e = 3φ(D)`).  All trust triple, no `sorry`.

- 2026-08-25 (review lap #3): **B6-affine DONE + EXCEEDED; direction re-pointed at the
  ONE open crux (image-Khinchin's log-tail SLLN); decorrelation core landed.** Inventory
  by real `#print axioms` (HEAD `53e454c`, build 🟢 8760): B5′ (10 headlines), B6 single-map,
  AND B6 Tier-2 full family `exists_cfNormal_and_affine_family_cfNormal'` (any `r`, `q>0`)
  all trust-triple — the measure route is not just done but exceeded (general family + full
  `r`). Confirmed recent laps genuinely narrowed the crux (measure pivot → single-map → full
  family → image-Khinchin assembly → g-direct reduction to ONE tail-average sorry). Prior
  directive (measure route) fully discharged ⇒ rewrote CURRENT DIRECTIVE to PROVE
  `ae_tail_average_tendsto` via the L² variance route, KEY INSIGHT = finite-truncation
  (Approach B) reduces the second moment to Finset algebra + one MCT limit (sidesteps nested
  `integral_tsum`). Hardest-first this lap: LANDED the two decisive decorrelation bricks
  `integral_blockCount_cross` (cross 2nd-moment identity) + `abs_cov_two_cyl_pair_le`
  (general-`(i,j)` two-cylinder covariance) — both axiom-clean, green. No charter trigger fired.

- 2026-08-25 (review lap #2b): **ROUTE PIVOT — schedule crux is FALSE, B6 goes to the
  measure route.** While driving step 1c of the "prove the variance crux" plan, the
  pushforward structure yielded a rigorous counterexample to `variance_blockCount_psi_pushed`
  (`v=[1]`, `ψ(cfCyl wx')⊆cfCyl[2,…,2]` ⇒ pushed count `≡0` at scales `n≤|wx'|` ⇒
  `LHS=n²γv²γ(wx') > RHS` once `n>88/γv≈212`). The crux is FALSE — a deep cylinder is a tiny
  interval, so `blockCount n(ψ·)` is near-constant over it for `n≲|wx'|` at a value ≠ `nγv` ⇒
  2nd moment `Θ(n²)`. So `psi_pushed_chebyshev_brick`/`_poly` establish nothing; both schedule
  z-routes are dead. Took the 2026-08-24-pre-registered "escape #3": pivoted B6 to the MEASURE
  argument (existence is a.e.-trivial). New crux = `ae_isCFNormal` (a.e. CF-normality via
  L²→a.e. Borel–Cantelli from the PROVED `variance_blockCount_le`, no ergodic theorem), then
  ψ⁻¹-preserves-null ⇒ two co-null sets meet ⇒ witness. Wrote OBSTRUCTION + ROUTE-ESCALATION
  docs, rewrote CURRENT DIRECTIVE, marked the false crux REFUTED in-source (kept, not deleted).
  Charter trigger FIRED and handled by pivot, not stop.

- 2026-08-25 (review lap #2): **Whole clean z-side reduced to ONE analytic crux;
  direction re-pointed at it.** Inventory by real `#print axioms`: build green 8757,
  both B5′ headlines trust-triple = DONE, B6 still `+sorryAx` (now via the DEAD
  two-stream `schedA_block_linear`, `:5630`). Confirmed the last ~10 laps were
  genuine crux-narrowing, not leaf-fixation: ψ(xA) irrationality PROVED, the
  Chebyshev/Markov budget + transfer engine built axiom-clean, the conditional-at-`wz`
  route walled by a density-vs-coverage obstruction (`5816044`) then corrected, and
  the clean local-density architecture found — collapsing the entire single-stream
  z-selector (`psi_pushed_chebyshev_brick`→`_poly`) onto ONE disclosed sorry
  `variance_blockCount_psi_pushed` (`:4254`). Found the prior directive STALE (its
  step 1 done, steps 2–3 collapsed); rewrote DIRECTION to mandate PROVING the crux,
  hardest-first, decomposed into (1) restricted ψ-pushed 2nd-moment identity
  (routine), (2) ψ-conjugated interval-base mixing via change-of-variables bounded
  density ratio, (3) geometric-sum assembly. Base-mass factor `γ(cfCyl wx')`
  MANDATORY (its loss walled every prior route). No charter trigger fired.

- 2026-08-25 (review lap): **B6 L4 crux PROVED; direction re-pointed at the z-side
  (ψ(xA) irrationality first).** Inventory by real `#print axioms`: build green
  8757, both B5′ headlines trust-triple = DONE, B6 still `+sorryAx` via the DEAD
  two-stream `schedA_block_linear` (`:4823`, sole `src/` sorry). Found the CURRENT
  DIRECTIVE stale: its mandated crux `schedL4_block_linear` is PROVED (`030d8fb`)
  and its step-4 "z-side = REUSE" is REFUTED (`b178653`). Validated the grind
  ON-PATH (last ~10 laps proved the block-linear crux, landed the x-side, built the
  Z-I engine — genuine crux work). Rewrote DIRECTION to mandate z-side
  re-integration, hardest-first = force ψ(xA) irrational via a per-stage
  diagonalization filler digit over an enumeration of `ψ⁻¹(ℚ)`, keeping the
  freq-good block on the FULL hull (target-shrink RULED OUT: breaks the `¼γwx≤γtar`
  balance). No charter trigger fired.

- 2026-08-24 (review lap): **B6 L4 crux collapsed to the cfK-cap graft; bridge +
  layer 1 PROVED.** Inventory by real `#print axioms`: build green 8757, both B5′
  headlines trust-triple, sole `src/` sorry = the DEAD two-stream
  `schedA_block_linear`. Validated the L4 pivot SOUND and the grind ON-PATH (the
  last ~5 laps located + proved the block-linear support layer and started the
  recursion — genuine crux work, not leaf-fixation). Found the CURRENT DIRECTIVE
  stale in specifics (mandated L4 measure bricks all since DONE) and re-pointed it
  at the real crux `schedL4_block_linear`, whose ONE open sub-obstruction is the
  **cfK cap** (`cfK u ≤ e^{κ|u|}` ⇒ `Nfib` affine in `|wx|`). Confirmed it is a
  positive-measure selection (NOT the refuted hard digit-cap) with its whole
  measure/selection stack already proved, then de-risked it: proved the bridge
  `cfK_le_of_notMem_cfKbadExtSet` + the layer-1 variant
  `exists_multiscale_freq_good_block_steer_len_cfK` (exposes `cfK u ≤ e^{κ|u|}`),
  build green, additive. Rewrote DIRECTION to mandate the graft (layer 2 → 3 →
  `schedL4_block_linear`). No charter trigger fired.

- 2026-08-24 (review lap): **B6 PIVOT RATIFIED — two-stream route DEAD, RESUME
  single-stream L4; broke a FALSE STOP.** Inventory by real `#print axioms`: build
  green 8757, both B5′ headlines trust-triple, sole `src/` sorry = the B6 crux
  `schedA_block_linear` (`:2537`). The prior grind laps hit a genuine obstruction
  (two-stream forces super-exponential blocks, `OBSTRUCTION-2026-08-24`) and
  correctly proposed the single-stream pivot, but then declared the crux
  "operator-gated" and stopped — a false stop (no operator on an autonomous run).
  Discovered the single-stream "L4" route is the ORIGINAL module design
  (`CFScheduleA.lean:24–31`) whose L3 foundation `volume_preimage_affineMap`
  (`CFAffine:94`) is already proved; the two-stream layer was a later drift into
  the wall. Rewrote DIRECTION.md CURRENT DIRECTIVE to resume L4 (brick 1 = the
  ψ-pullback Gauss distortion bound `gaussMeasure(ψ⁻¹ S) ≤ (2/q)·gaussMeasure S`,
  ingredients confirmed present), decomposed the full L4 path in PENDING_WORK, and
  forbade grinding the dead two-stream lemmas / any further box-stuck. Item-2
  (integer-shift, all real `r`) + both signposts remain DONE. No charter trigger
  fired (L4 additive, no forbidden import).

- 2026-08-24 (review lap): **B6 route pivot (hdom refuted).** Inventory (real
  `#print axioms`): build green 8757,
  both B5′ headlines trust-triple, sole `src/` `sorry` = the B6 crux
  `exists_interleaved_affine_witness`. Confirmed the grind laps since the last
  review CORRECTLY diverged from the prior directive: they refuted `hdom`
  (`ec0875d` — steer blocks are `Θ(word)`, dominance impossible) and PROVED the
  replacement crux crack `exists_uniformly_freq_good_block_steer` (`f2b4b33`,
  axiom-clean) + the full uniformly-good-block toolkit (`quadScales*`, multiscale
  measure, interpolation arith) + `chainTail_dev_split_var`. The CURRENT DIRECTIVE
  was STALE (still mandated `chain_orbit_equidist` WITH dominance); rewrote it to
  the **hdom-free `chain_cf_digit_freq_tendsto` variant** (step-4 assembly),
  FORBADE more block/measure atoms, named the route-decisive case (mid-block bound
  closing via `addslack₂` + `o(word)` boundary slack dividing out). No charter
  trigger fired.

- 2026-08-24 (review lap): **B6 course-correction — PIVOT TO THE CRUX.**
  Inventory: build green 8756, B5′ headlines re-verified trust-triple, sole
  `src/` `sorry` = the B6 crux `exists_interleaved_affine_witness`. Diagnosed
  crux-neglect: 11 straight grind laps (11–21) each proved a geometric ATOM
  (axiom-clean, green) but the crux stayed untouched and the recursion/telescoping
  was deferred "next lap" ~7×. Declared the atom toolkit COMPLETE; reset the
  CURRENT DIRECTIVE to build the frequency telescoping hardest-first via an
  abstract generic-chain lemma `chain_orbit_equidist`, naming the route-decisive
  case (dominance vs growing fillers + alternation). No charter trigger fired.

- 2026-08-24 (reflection lap → COMPLETION): **Tier 2 CLOSED — the whole
  expedition is done, axiom-clean.** Steps 1–3 all landed this lap. (1) Rewired
  `CFSchedule.lean` to the summable-**family** refinement (fixed cutoffs
  `khinchinK j`, no level-tied `K_t→∞`). (2) Built the log-tail telescoping in
  `CFCorrect.lean` (`logTailMass` + monotonicity, `uSched_logTail_le`,
  `tailSched_logTail_le`, `xstar_logTail_prefix_bound`, `logTailMass_cfPrefix`)
  and assembled the crux `xstar_log_tail_uniform`, hence `xstar_khinchinTypical`
  (axiom-clean). (3) Route D′: relocated the frozen `khinchinK₀`/`KhinchinTypical`
  defs byte-identical to a new upstream `KhinchinDefs.lean`, dropped Khinchin's
  `import Headline`, and closed the Tier-2 headline
  `⟨xstar, xstar_isAbsolutelyNormal, xstar_isCFNormal, xstar_khinchinTypical⟩`.
  All 10 headlines re-`#print axioms`-verified trust-triple. Also (earlier in the
  lap): ratified route C′ and de-staled the CURRENT DIRECTIVE (it still named the
  superseded Chebyshev/variance plan). ROUTE VERDICT: CONTINUE → reached the
  destination.
- 2026-08-24 (grind run, route C′): **FAMILY machinery COMPLETE + axiom-clean.**
  `volume_logBadZone_le_vol` (Lebesgue bridge), three-zone combine
  (`exists_good_avoiding_bad_khinchin` + `_family`), `exists_refinement_uniform_khinchin_family`
  (log-tail payload at every `j<tK`), `CFLogTail.lean` layering (khinchinK₀-free
  upstream). Found+fixed the level-tied-cutoff design bug via the summable family
  (geometric budget `≤1/7`). CFSchedule still carries the SUPERSEDED single-zone
  threading (true, green, unused) — next lap rewires it to the family form.
- 2026-08-24 (review lap): **Tier-2 route SETTLED, schedule fence relaxed, moment
  seed proved.** Broke the 3-lap "operator-gated" stall (fc801ba/17dc2c9/7d6740f
  were pure route-analysis ending in a false "need operator" stop). Confirmed the
  only route is the additive W6 log-concentration bad zone; relaxed the
  `DIRECTION.md` "don't touch the schedule" fence to additive-only with a
  Tier-1-axiom invariant. Proved `summable_gaussKuzmin_logsq` (moment condition
  `E[(log a₁)²]<∞`, axiom-clean) — the analytic seed of the tail bound.
  Re-verified Tier 1 axiom-clean (trust triple), build green (8735 jobs).
- 2026-08-24 (grind laps): **Tier 1 LOCKED** (`b3bc2c4`,
  `exists_absolutely_normal_cf_normal`, axiom-clean) + Tier-2 assembly seeded:
  `gaussMeasure_Ioo`/`gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit
  law), `Khinchin.lean` (geometric-mean⟺log-average reduction `khinchinTypical_iff_log_tendsto`,
  `khinchinK₀_pos`), `prod_le_cfK`+`wSched_log_sum_le` (total log-mass bound),
  `xstar_log_digit_avg_truncated_tendsto` (finite-truncation slice).
- 2026-08-24 (review lap): **Pillai crux `windowCount_eq_sum_phaseCount` PROVED**
  (axiom-clean) — the `Q`-scale↔`N`-scale phase-count identity, via a
  `Finset.card_nbij'` bijection `i ↔ i/r`; dodged last lap's `r*(i/r)` vs
  `(i/r)*r` omega-atom trap by anchoring on `Nat.div_add_mod` + one explicit
  `Nat.mul_comm`. Re-verified headlines axiom-clean (trust triple), build green
  (8743 jobs). Directive refreshed (it still named the closed `m`-growth
  estimate as THE crux) → FINISH Pillai, now double-limit-first. No trigger fired.
- 2026-08-24 (grind laps): **d-ary side CLOSED** — `xstar_dary_freq_tendsto`
  (base-`d` simple normality every base, axiom-clean); the `m`-growth interior
  crux (`tendsto_gain_div_mSched_sub`) + Pillai combinatorial core
  (`phaseWindowFreq_tendsto`, `card_straddling_phases`, window/slice
  correspondence, `card_matchingValues`).
- 2026-08-23 (reflection lap): re-verified 10 headlines axiom-clean (trust
  triple), build green (8742 jobs), src/ sorry-free. Found DIRECTION/STATUS/
  PENDING_WORK badly STALE — they still named the Lemma-13 assembly the
  "untouched crux", but Lemma 13 + schedule + `xstar` + CF normality all landed
  since. Refreshed all three; reframed the destination into Tier 1 (B–Y
  abs-normal + CF-normal, source-backed) vs Tier 2 (Khinchin, campaign-original
  stretch); set directive to LOCK Tier 1 via the d-ary `m`-growth estimate.
  ROUTE VERDICT: CONTINUE (no trigger fired; strong forward motion).
- 2026-08-23: **CF NORMALITY OF `xstar` PROVED** (`CFCorrect.lean`,
  `xstar_cf_freq_tendsto`) + **d-ary digit extraction / payload accessors**
  (`DaryDigits`/`DaryCorrect`): digit windows are literally the base-d digits;
  each active stage gives a good block. All axiom-clean.
- 2026-08-23: **THE SCHEDULE + Lemma 13 + limit point** — `CFSchedule.lean`
  (uniform Lemma 13, brick sequence, invariants, dominance), `xstar`
  irrational in every scheduled cylinder (`CFLimit` applied). Axiom-clean.
- 2026-08-23: **B–Y Lemma 13 PROVED** (`TBrick.lean`, both `t'=t` and `t→t+1`)
  — the measure-balance selection lemma (good mass ½|I_w| beats CF + Σ d-ary bad
  zones) made UNCONDITIONAL; seed brick + refinement toolkit (`TBrickRefine`).
- 2026-08-23 (review lap): diagnosed input-gathering fixation, redirected to the
  Lemma-13 measure-balance assembly (now proved).

## Outstanding

### Short-term (mirror PENDING_WORK top — image-Khinchin's tail-average SLLN, in `CFAeKhinchin.lean`)
- ✅ **LANDED this lap (bricks 1–2, axiom-clean):** `integral_blockCount_cross` (cross
  2nd-moment identity), `abs_cov_two_cyl_pair_le` (general two-cylinder covariance bound).
1. **`variance_truncated_le K M n`** — uniform-in-M variance of `S_n^M = Σ_{a<M} u_a·blockCount[K+1+a] n`:
   `|∫(S_n^M)² − (n·μ_M)²| ≤ n·(C₃+80C₁C₂)`. Split `Σ_{i,j}` diagonal (i=j: `n·Var(f_M)≤nC₃`,
   distinct cylinders disjoint) vs off-diag (fold brick 2 via `sum_range_dist_le`+`geom_trunc_sum_le`).
2. **`variance_logBirkhoffSum_le K n`** — MCT limit M→∞ on step 1 (`S_n^M ↑ logBirkhoffSum K n` a.e.
   from `logTailTerm_tsum_ae_eq` at each `Tⁱx`; `∫(S_n^M)²↑∫(logBirkhoffSum)²`, `μ_M→μ`).
3. **`chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto`** — transcribe `chebyshev_blockCount` +
   `ae_orbit_freq` (`CFAeNormal.lean:81`); monotone gap-squeeze available (`logTailFn K ≥ 0`).
4. **Graft** `ae_khinchinTypical`'s co-null set into `exists_cfNormal_and_affine_family_cfNormal'`
   ⇒ image-Khinchin headline; re-`#print axioms` clean.

### Long-term
- After image-Khinchin: the campaign's headline set is complete. Possible further stretches
  (affine images of Khinchin-typical, etc.) detach freely but are not required.

### To completion
- B5′ (Track A + Tier 1 + Tier 2): **DONE**, all axiom-clean.
- B6 single-map + full affine family: **DONE**, all axiom-clean.
- image-Khinchin headline: gated on `ae_tail_average_tendsto` (4 items above); bricks 1–2 landed.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-25 review lap #3, HEAD `53e454c`+)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `exists_absolutely_normal_cf_normal` (**Tier 1 = Becher–Yuhjtman**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_absolutely_normal_cf_normal_khinchin` (**Tier 2 headline**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_cfNormal_and_affine_cfNormal` (**B6 affine image**) | uncond (q>0) | trust triple | 🟢 **DONE** (2026-08-25, measure route). Crux `ae_orbit_freq`→`ae_isCFNormal`→`exists_feasible_cfNormal_affine` (`CFAeNormal.lean`, sorry-free) wired into the headline; the false-crux schedule chain is dead code, kept marked REFUTED. |
| `exists_cfNormal_and_affine_family_cfNormal'` (**B6 Tier-2 full family**) | uncond (any `r`, q>0) | trust triple | 🟢 **DONE** (2026-08-25). Faithful Vandehey §7 Tier-2 statement; `volume_notCFNormal_univ` crux (non-CF-normal null on all ℝ). |
| `ae_khinchinTypical` / image-Khinchin headline | uncond | `+ sorryAx` | 🟡 OPEN — gated on `ae_tail_average_tendsto` (log-tail SLLN). Decorrelation bricks 1–2 landed axiom-clean this lap; variance→a.e. chain remaining. |
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | trust triple | 🟢 DONE |
| `isNormal_log_two_of_equidistributed` | cond (orbit equidist.) | trust triple | 🟢 DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | trust triple | 🟢 DONE |
| `xstar_cf_freq_tendsto` (CF normality of x\*) | uncond | trust triple | 🟢 DONE |
| `xstar_dary_freq_tendsto` (d-ary simple normality, every base) | uncond | trust triple | 🟢 DONE |
| `pillai` (simple-to-all-powers ⇒ full normality) | uncond | trust triple | 🟢 DONE |
| `gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit law) | uncond | trust triple | 🟢 DONE |
| `summable_gaussKuzmin_logsq` (Tier-2 moment seed) | uncond | trust triple | 🟢 DONE |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0** proven-but-cited axioms across all 10 B5′ headlines AND both B6 affine headlines
(single-map + full family) — every one 🟢, trust triple only. The only `+sorryAx` is
`ae_khinchinTypical` (image-Khinchin stretch), a **disclosed decomposition `sorry`**
(`ae_tail_average_tendsto`), NOT a cited math axiom — being actively discharged (the L²
variance route; decorrelation bricks landed this lap). No 🟡/🟠 debt on the proven
headlines, no 🔴. Trust triple = propext, Classical.choice, Quot.sound throughout.

## Pointers
DIRECTION.md (CURRENT DIRECTIVE) · ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) ·
JUDGE.md · papers/literature-review.md · newest HANDOFF (`ls HANDOFF-*.md | sort | tail -1`) ·
PENDING_WORK.md · papers/becher-yuhjtman-2019-*.md
