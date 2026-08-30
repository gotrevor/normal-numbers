# BRIEF: formalize the six-fold adder disjunction 🧮🏛️

## RESULT (2026-08-30, autonomous lap)

**PROVED.**  `NormalNumbers.Adder.adder_sixfold_disjunction`
(`src/NormalNumbers/AdderMain.lean`) — the frozen six-fold statement, with
`OccursAt` from `Disjunctive.lean` and "i.o." spelled `∀ N, ∃ n, N ≤ n ∧ …`.

* **Axiom audit (phase-1 checkpoint, real `#print axioms`):**
  `[propext, Classical.choice, Quot.sound,
  NormalNumbers.Adder.main_cert_ok._native.native_decide.ax_1_1]` — trust
  triple plus the single disclosed compiler axiom from the main-certificate
  check (note: per-declaration `_native.native_decide.ax_1_1`, NOT
  `Lean.ofReduceBool` — this pin names native axioms per site).
* **Module-3 route:** `native_decide` for the 73728-state main certificate
  (`AdderCertMain.lean`, ~3 s; omega as a digit-string through `ByteArray`,
  live as a 75-index list, rho/forced as assoc tables).  The **toy pipeline
  is kernel tier end-to-end**: `toy_disjunction` (`AdderEndgame.lean`) has
  axioms exactly `[propext, Classical.choice, Quot.sound]`, certificate by
  kernel `decide` (~1 s).  A kernel-tier swap for the main certificate
  (`AdderCertMainKernel.lean`, chunked-Nat tables, `decide +kernel`) is
  generated and in test at the time of writing — see PENDING_WORK.md for
  its status; if green it replaces the native axiom and the headline
  becomes trust-triple.
* **Modules landed** (all green, committed on `wip/adder-disjunction`):
  `AdderCarry` (floor carries, column identity), `AdderAutomaton`
  (backward-deterministic `famPred`/`HStep`), `AdderShadow` (true state +
  shadowing; `winCode z m k` takes the digit COUNT — window is
  `winCode z m (ℓ-1)`), `AdderCert` (generic C1/C1'/C3' checker + semantic
  extraction), `AdderCertToy`, `AdderDescent` (ω-descent, ρ-lock, forced
  determinism, pigeonhole ⇒ eventually periodic inputs — no König),
  `AdderEndgame` (equal digit streams ⇒ equal reals; periodic digits ⇒
  rational; the generic `no_occurrence_contradiction` engine), 
  `AdderCertMain`, `AdderMain`.
* **Statement-shape deviations:** none in substance.  "`∃ n ≥ N`" is spelled
  `∃ n, N ≤ n ∧ …` (definitionally the binder's meaning).  Endgame
  route-correction honored: irrationality via the already-landed
  `irrational_log_two` (Legendre route), NOT from `lnTwoExpSep_holds`
  (that implication is unsound — see HANDOFF-2026-08-29-adder-foundation).
* **Sanity anchors:** `example : OccursAt 2 (Real.log 2) [0,0] 4` proved
  from `Real.log_two_gt_d9`/`lt_d9` (ln 2 = 0.10110001…₂ ✓);
  `famSize mainFamily = 73728 = by decide`; the Python emitter re-verifies
  C1/C1'/C3' at emit time and the self-test anchors every convention
  against 3492 true bits of ln 2 / ln 3.


**Operator-authorized 2026-08-29 (Trevor, attended session).**  Lane: this is a NOVEL
candidate theorem (occurrence currency) - the formalization IS the independent
verification its honesty ledger owes.  DIRECTION.md governs; two-lanes doctrine applies
(phase-1 tolerances allowed, kernel-tier finite check is the end goal).  Context docs:
`docs/adder-collapse-hunt-2026-08-29.md` (the discovery + exact computation),
`docs/babel-blueprint-2026-08-29.md` §adder-wing (the architecture).  Reference
implementation: `experiments/adder_collapse_hunt.py` (self-testing; rerun it first and
read it - it is the ground truth for every convention below).

Write `## RESULT` at the top of this file when done (treadmill-brief convention).

## The theorem to prove

> **At least one of the following holds:**
> - `00` occurs infinitely often in the binary expansion of ln 2;
> - `001` occurs infinitely often in the binary expansion of ln 3;
> - `11` occurs infinitely often in the binary expansion of ln 6;
> - `001` occurs infinitely often in the binary expansion of ln 18;
> - `010` occurs infinitely often in the binary expansion of ln 12;
> - `000` occurs infinitely often in the binary expansion of ln 54.

Sketch of the frozen statement (adjust encodings to the repo's `OccursAt` conventions,
which live in `src/NormalNumbers/Disjunctive.lean`; "i.o." = `∀ N, ∃ n ≥ N, ...`):

```
theorem adder_sixfold_disjunction :
    (∀ N, ∃ n ≥ N, OccursAt 2 (Real.log 2)  [0,0]   n) ∨
    (∀ N, ∃ n ≥ N, OccursAt 2 (Real.log 3)  [0,0,1] n) ∨
    (∀ N, ∃ n ≥ N, OccursAt 2 (Real.log 6)  [1,1]   n) ∨
    (∀ N, ∃ n ≥ N, OccursAt 2 (Real.log 18) [0,0,1] n) ∨
    (∀ N, ∃ n ≥ N, OccursAt 2 (Real.log 12) [0,1,0] n) ∨
    (∀ N, ∃ n ≥ N, OccursAt 2 (Real.log 54) [0,0,0] n)
```

🧊 **FROZEN: the word-to-constant pairing and the six constants** (they come from the
exactly-verified collapse; do NOT re-hunt or substitute).  DRAFT-restatable: encoding
details (word list order, OccursAt phrasing) after checking repo conventions.  Sanity
anchor before freezing: ln 2 = 0.10110001011100100001...₂, so `00` first occurs at
position 4 (bits 4,5) - confirm your digit/word orientation reproduces that, and confirm
the digit convention handles constants > 1 (digits of the fractional part; integer parts
are irrelevant and all six constants are irrational, so no dyadic edge cases).

## Why it is true (the whole proof, humanly)

Let `X = ln 2`, `Y = ln 3` with binary digit streams `x_m`, `y_m`.  Each constant is
`z⁽ⁱ⁾ = aᵢX + bᵢY` for `(a,b) ∈ {(1,0),(0,1),(1,1),(1,2),(2,1),(1,3)}` (note
`Real.log 6 = Real.log 2 + Real.log 3` etc., via `Real.log_mul`).  Column addition with
carries makes each z-digit a local function of `(x_m, y_m)` and a bounded carry.  If,
for contradiction, NO channel's word occurs beyond some N₀, then the joint
(carry, recent-digits) state walks forever inside an explicit finite automaton.  A
machine-verified certificate (rank function + forced-successor table) shows every
infinite walk in that automaton is eventually periodic.  Eventually periodic
`(x_m, y_m)` makes X rational - contradicting the irrationality of ln 2, which this
repo already owns outright (`lnTwoExpSep_holds` separation ⟹ irrational, or check
whether mathlib has `Irrational (Real.log 2)` directly).  Only ln 2's irrationality is
needed; the other five constants enter through exact floor arithmetic alone.

## The five modules (with the exact mathematics)

### 1. Carry identity (`AdderCarry.lean`, ~300 lines, pure Int.floor)

For a channel `(a, b)`, define the TRUE carry from the reals:

```
T (n : ℕ) : ℤ := ⌊2^n * (a*X + b*Y)⌋ - a*⌊2^n*X⌋ - b*⌊2^n*Y⌋
```

Prove (all elementary floor lemmas):
- **Bounds**: `0 ≤ T n ≤ a + b - 1`  (from `⌊u+v⌋ - ⌊u⌋ - ⌊v⌋ ∈ {0,1}` and
  `0 ≤ ⌊a*u⌋ - a*⌊u⌋ ≤ a-1`).  Note `(1,0)` has `T ≡ 0`.
- **Column identity**: with `d_m(w) := ⌊2^m*w⌋ - 2*⌊2^(m-1)*w⌋ ∈ {0,1}` (the m-th
  binary digit),
  `a*x_m + b*y_m + T m = d_m(z) + 2 * T (m-1)`.
  Derivation: apply `⌊2^m w⌋ = 2⌊2^(m-1) w⌋ + d_m(w)` to z, X, Y and subtract.
  So `T m` is the carry INTO column m (from deeper positions), `T (m-1)` the carry out
  (toward more significant positions) - identical to the probe's automaton with
  `v = a*x + b*y + c_in`, digit `v % 2`, carry-out `v / 2`.

### 2. State, step relation (`AdderAutomaton.lean`, ~150 lines, pure Nat)

State at position m (DEFINED from the reals, so no reachability axioms are ever
needed): per channel, the carry `T_i(m)` and the window of the `ℓᵢ - 1` deeper z-digits
`(d_{m+1}, d_{m+2})` (length-3 words) or `(d_{m+1})` (length-2 words).  Encode as one
`Nat` in mixed radix.  Ambient sizes with TIGHT carry ranges `[0, a+b-1]`:
carries `1·1·2·3·3·4 = 72`, windows `2·4·2·4·4·4 = 1024`, ambient `= 73 728` states.

`HStep (s : State) (σ : Input) (s' : State) : Prop` - decidable, meaning "s' is a
legal one-step-DEEPER state" : for each channel, `v = a*x + b*y + c'` (c' the carry of
s'), digit `v % 2`, carry `v / 2` equals s's carry, windows shift consistently, carries
in range, AND the word test fails (the just-formed `ℓ`-digit window ≠ the channel's
word - this encodes "no occurrence at position m").

Prove the **shadowing lemma**: if no channel word occurs at any position ≥ N₀, then
the true state sequence `S(m)` (from module 1's T and the real digits) satisfies
`HStep (S m) (x_{m+1}, y_{m+1}) (S (m+1))` for all m ≥ N₀.

### 3. The certificate (`AdderCertificate.lean`, the crux, ~500-1500 lines incl. data)

Offline-computed data (see "Certificate generation" below), three tables over ambient:
- `live : State → Bool` (the set L),
- `ρ : State → ℕ` (rank),
- `forced : State → Option (Input × State)`,
- `ω : State → ℕ` (dead-depth).

Four LOCAL, DECIDABLE conditions - this is the entire finite content:
- **(C1)** ∀ s ∈ L, ∀ σ, s' with `HStep s σ s'` and `s' ∈ L`:
  `ρ s' < ρ s ∨ (forced s = some (σ, s') ∧ ρ s' = ρ s)`.
- **(C1')** `forced s = some (σ, s')` implies `HStep s σ s'` and `s' ∈ L`.
- **(C3')** ∀ s ∉ L, ∀ σ, s' with `HStep s σ s'`: `s' ∉ L ∧ ω s' < ω s`.
- (Range closure is built into HStep; no other condition exists.)

~74k states × 4 inputs ≈ 300k primitive checks.  Kernel route: the frozen-table
`decide +kernel` pattern (KB: `lean-journey/reference/`, the frozen-table leaf); chunk
by state ranges if needed.  Phase-1 fallback: `native_decide`, disclosed, stripped
later per two-lanes doctrine.

### 4. Descent glue (`AdderDescent.lean`, ~250 lines, no computation)

From an infinite HStep path inside L (true path is in L: if some S(m) ∉ L, (C3')
gives an infinite strictly-ω-decreasing sequence - impossible):
- (C1) makes ρ non-increasing along the path; drops are finite (well-founded ℕ).
- Beyond the last drop every step equals `forced`, a FUNCTION - so the state sequence
  is an orbit of a function on a finite type: eventually periodic (pigeonhole), with
  the input labels `(x_m, y_m)` a function of the state: eventually periodic digits.
- No König's lemma, no compactness, no SCC theory - none of that is needed formally.

### 5. Endgame (`AdderEndgame.lean`, ~350 lines)

- Eventually-periodic binary digits ⟹ rational (geometric series over the repo's
  `realOfDigits`/Bridge machinery).
- Contradiction with `Irrational (Real.log 2)` (derive from in-repo separation
  `lnTwoExpSep_holds`, one short argument, or mathlib if present).
- Quantifier bookkeeping: "some word occurs at some position ≥ N₀, for every N₀"
  pigeonholes over six channels into one channel occurring infinitely often.
- Assemble the frozen disjunction.

## Certificate generation (do this FIRST, it de-risks everything)

Extend `experiments/adder_collapse_hunt.py` with an emitter:
1. Rebuild the automaton on the LEAN conventions exactly (tight carries `[0, a+b-1]`,
   window encoding, mixed-radix order) - the probe's own space is a superset (carries
   to a+b, KMP states instead of windows); the certificate MUST match the Lean ambient
   bit-for-bit, so regenerate, do not reuse.
2. Compute L (iterative dead-end pruning; record ω = pruning round), SCCs (Tarjan),
   verify every SCC is a simple cycle with single-labeled edges, ρ = reverse
   topological height on the condensation of the DEEPENING relation (HStep direction),
   forced = the unique intra-SCC (input, successor) per cycle state (None elsewhere).
3. Re-verify (C1), (C1'), (C3') in Python before emitting - the emitter must refuse to
   write a certificate that fails its own conditions.
4. Emit as compact Lean data (`Array UInt8`/`ByteArray` + decoder beats 74k literals).

**Integration dry run before the real family**: run the whole pipeline end-to-end on
the 3-channel VACUOUS family `(1,0)/'01', (0,1)/'01', (1,1)/'10'` (also exactly
collapsing, few hundred states).  It proves a known-true statement ("01 occurs i.o. in
ln 2, or 01 in ln 3, or 10 in ln 6") through every module including the kernel check,
at toy scale.  This is the route-decisive probe for module 3's performance; do it
before generating the big certificate.

## Traps ⚠️

- **Orientation**: the probe processes deep-to-shallow and ran KMP on REVERSED words;
  the window design above works in natural orientation.  Trust the module-2 spec, and
  anchor against ln 2's actual bits before freezing (position-4 `00` above).
- `digitOf` conventions for x > 1 and the repo's word-list order in `OccursAt` - read
  the definitions, don't assume; the pairing word↔constant is what is frozen, not a
  particular list-literal spelling.
- Do NOT import or prove irrationality for the five other constants - only ln 2's is
  used.  Resist the symmetric-looking scope creep.
- `v = a*x + b*y + c` reaches 7 on channel (1,3) - carry range 4 there is correct.
- Keep the automaton in `Nat` end to end; the reals touch only modules 1, 2 (shadowing)
  and 5.
- Performance: mixed-radix `Nat` states, `Array`-backed tables, no `Fin` gymnastics in
  the checked kernel terms.

## Done-when

1. The frozen six-fold disjunction is proved, `sorry`-free.
2. `#print axioms adder_sixfold_disjunction` = trust triple (phase-1 checkpoint may
   carry `Lean.ofReduceBool` from `native_decide` - disclose in RESULT and leave the
   kernel-tier swap as the recorded remainder if not completed).
3. The certificate generator re-verifies its conditions in Python at emit time, and the
   toy-family pipeline is kept as a regression example.
4. RESULT section at the top of this file: statement location, axiom audit output,
   which route module 3 took (kernel vs native), line/time notes, any statement-shape
   deviations with reasons.

Out of scope: novelty sweep and word-openness audit (literature work, stays with the
operator); any outward artifact (paper prose, announcements); re-running the hunt or
changing the family; borrow-automata extensions (ln(3/2) family) - later brief.
