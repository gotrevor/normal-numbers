# HANDOFF: continue the Babel exploration (fresh-context entry point) 🗼

**Read this first, then the docs it points to.  Mode: conjecture-forging** (operator-set,
2026-08-29): the deliverable is simply-stated unformalized conjectures, paths between them,
and probes that could kill them.  🚫 Do NOT propose formalization/discharge moves in this
mode - the operator calls for roads, this session finds paths ([[moonshot-conjecture-graph]]
doctrine line, 2026-08-29).  The one commissioned road runs SEPARATELY:
`BRIEF-adder-disjunction-formalization.md` (a different session grinds it; leave it alone).

## The night's arc (2026-08-29 evening, five stories, all pushed)

| Story | Doc | Probes | What happened |
|---|---|---|---|
| Conjecture slate N1-N5 | `docs/new-conjectures-2026-08-29.md` | `lntwo_wieferich_census.py`, `stoneham6_readout.py`, `e_binary_runs.py` | Wieferich census (5 vs 4.11 expected); Stoneham base-6 = readout of `3^a mod 2^c` (exact); e enters via factorial kicks (all-base) |
| Tower 2nd story | `docs/tower-2026-08-29.md` | `e_kick_barrier.py`, `stoneham6_weyl.py` | FQ coordinate = cosmetic (one digit bit per checksum); e kick-barrier REFUTED by probe; Weyl door armed (√A cancellation); T3c provable brick found (staircase slices = two-exponential family; mid-block = `frac((3/2)^m)`) |
| Babel blueprint | `docs/babel-blueprint-2026-08-29.md` | `lntwo_hotspot_census.py` | 🔑 KEYSTONE: normality ⟺ pure avoidance currency (strong hot-spot theorem + mass conservation); B-ladder = ALL the sand; census green depths 1-12 |
| Collapse hunt W1 | `docs/adder-collapse-hunt-2026-08-29.md` | `adder_collapse_hunt.py` | 💥 HIT: six open-word channels reach entropy EXACTLY zero (integer-graph verified) ⟹ candidate theorem: at least one of {00∈ln2, 001∈ln3, 11∈ln6, 001∈ln18, 010∈ln12, 000∈ln54} occurs i.o. |
| Disjunction factory | `docs/adder-family-2026-08-29.md` | `adder_family_enum.py` | 🌍 UNIVERSALITY (any reals X,Y not both rational; (π,e) free); 7/54 neighbors collapse; 2nd family with 4× smaller certificate; Pythagorean near-miss h=0.0080; Mahler/B-B located as genre ancestor; 🧯 no-singleton negative (factory can't reach one constant, provably) |
| Transversal ceiling | `docs/transversal-ceiling-2026-08-29.md` | `sparse_pair_blocking.py` | 🧱 Operator asked: can enough clauses entail "some channel disjunctive"?  Exact answer: iff transversal-complete (product cover) - and a blocking pair (x=y=Σ2^(−2^k): NO channel disjunctive, probe-verified w/ control) proves universal clauses can NEVER get there.  Survivor: Product-Block Conjecture (∀ finite F, some channel set collapses ALL F-tuples ⟹ some channel visits all of F i.o., witness drifts upward); blocking pairs = free pre-filters for the classification sweep |

## The map (memorize this, it orients everything)

**Three currencies, three machines:**
1. **Depth** (Diophantine): proved 9n run caps; classical road ends at superlinear complexity.
2. **Counting** (the hot-spot B-ladder): normality of ln 2 ⟺ "no word over-visited by a
   constant factor" - one-sided bounds only, keystone proved, ALL remaining sand is the
   graded counting ladder B1(w,C).  Single-constant occurrence = rung zero (one visit to
   one interval).
3. **Occurrence** (the adder factory): produces unconditional cross-constant disjunctions;
   PROVABLY cannot reach a single constant (monotone clauses; ghost-stripping conserved by
   subsystem entropy).  Its exact method boundary: the kick 1/n is not finite-state.

Factory: "not all can fail."  Column: "this one doesn't."  Gap: one visit to one interval.

## Ranked next stories 🥇

1. **The classification theorem (factory → concrete)**: exhaustively map the collapse locus
   - all word tuples on the 6-channel sets, channel sets to height ~5, minimal family size
   (is 5 or 4 possible?), collapse threshold vs word length.  Output: the explicit finite
   map of how joint digit pathology can distribute over the log-lattice.  Pure computation
   + a write-up; `adder_family_enum.py` is the engine (greedy → exhaustive).  ⚡ Now with
   free teeth from story 6: bolt the sparse-pair pre-filter onto the enum (tuples blocked
   by every 0*bin(m)0* language provably never collapse) and cross-check engine vs filter
   - two instruments, independent origins.
1b. **Product-Block hunt** (new, from the transversal-ceiling story): smallest instance
   F = {00, 11} - find a channel set where ALL 2^|M| word assignments collapse.  A hit
   proves "for any pair not both rational, some channel sees both 00 and 11 i.o." - the
   first rung of the graded joint-visit ladder, the strongest occurrence statement no
   blocking pair forbids.
2. ~~**Pythagorean closure**~~ ✅ **CLOSED 2026-08-29 late night**: beam search
   (`pythagorean_closure.py`) found ≥ 8 exact collapses on the musical six - no seventh
   channel needed.  Flagship instance: ln2/`00`, ln3/`11`, ln(3/2)/`100`, ln(4/3)/`11`,
   ln(9/8)/`00`, ln6/`010`, **9 478 live states (smallest certificate known)**.  The
   h = 0.0080 "near-miss" was greedy myopia - a lesson for every other floor quoted from
   greedy runs.  Follow-on: enumerate ALL musical collapses (the beam saw only the top),
   and re-run the OTHER quoted floors non-greedily.
3. **Three tracks**: (ln 2, ln 3, ln 5), channels `ln(2^a 3^b 5^c)` - does collapse need
   fewer channels per track?  (Entropy 3 bits, quadratically more channels.)
4. **Other bases**: the same machine in base 3 - ternary disjunctions for the same constants.
5. **Counting rungs of the B-ladder**: shape a mid-scale counting-separation conjecture
   (how often can `res_n` enter a positioned window) - the frontier of currency 2; also
   T1/PairMiss (≤1 deep event per dyadic window) formal statement + extended census.
6. **Solenoid S2** (union-over-blocks): a visit per word per ∞-many blocks is all α₂,₃
   disjunctivity needs; no known technique exploits the union - genuinely open direction.
7. Parked provable brick: T3c (collatz Legendre separation ⟹ α₂,₃ base-6 run caps at
   explicit slice positions) - available whenever the operator calls for a road.

## Honesty ledgers (consolidated, owed before any outward whisper) 📋

- **Candidate theorem**: kernel verification (= the commissioned brief, running separately);
  FULL novelty sweep - retargeted by universality to carry-automata/combinatorics-on-words:
  forward-citations of Berend-Boshernitzan (Acta Arith. 66, 1994), Waldschmidt *Words and
  Transcendence* (arXiv:0908.4034), Allouche-Shallit, MathSciNet when available; word-openness
  audit (00/11 frontier per Adamczewski-Rampersad; no specific length-3 block known for any
  specific constant - re-verify).
- First-pass verdicts (recorded in the family doc): exact statements in print ~10%; method
  ~15%; short hand proof exists ~35% (would downgrade flagship to "cute proposition",
  factory/schema survive); subsumed by Mahler descendants ~15%.
- All exact collapses = one implementation agreeing with itself (self-tested: exact
  golden-mean entropy, independence additivity, predicted vacuous collapse, hand-verified
  survivor `x = y = (10)^∞`).

## Operating rules for this exploration ⚙️

- **Open words only** in any hunt: {00, 11} + length-3 (0, 1, 01, 10 are known-recurring
  for every irrational - channels carrying them are vacuous; the machinery itself
  rediscovered this boundary).
- Every claimed collapse gets the **exact integer-graph check** (every SCC a simple cycle,
  single-labeled edges), never float-only.
- Universality framing in every write-up: collapses are theorems about ANY pair not both
  rational; named constants are instances.  Cite Mahler 1973 + Berend-Boshernitzan as genre
  ancestors.
- Probes live in `experiments/`, self-testing, uv shebangs; docs in `docs/`; commit green
  and push (direct-to-master sanctioned here).
- DIRECTION.md governs; the conjecture-graph objective (novel mathematics, refutation =
  progress) outranks everything; report-backs lead with what the mathematics SAYS.
