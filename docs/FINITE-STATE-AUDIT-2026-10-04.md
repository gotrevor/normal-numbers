# Finite-state lane (E3) audit, 2026-10-04

Lane: `docs/ENGINE-PROPOSALS-2026-10-04.md` §E3.  Branch `proof/finstate`.  Lean record:
`src/NormalNumbers/FiniteStateSelection.lean` (headlines, leaves, cited hypotheses) and
`src/NormalNumbers/FiniteStateSelectionStretch.lean` (stretch nodes, non-synchronous sibling).

## Pick

Two questions from Pulari, *On Normality and Equidistribution for Separator Enumerators*,
arXiv:2602.01199v2 (3 Feb 2026), §5 "Discussion and open questions".  Both are about Mayordomo's
`f`-normality (arXiv:2208.00157, whose closing question Pulari answers negatively in general and
positively for finite-state coherent enumerators).

| Question | Exact wording | Answer frozen | Lean |
|---|---|---|---|
| Q-DPDT | "One concrete setting is when the naming map is computable by a deterministic pushdown transducer.  In particular, does there exist such a separator enumerator `f` and a point `x∈[0,1)` for which the integer sequence `(k^n a_n^f(x))_{n≥1}` is `k`-adically equidistributed while `dim^f_FS(x)<1`?" | Yes for `k ≥ 5`, with a real-time (letter-to-letter) DPDT | `PulariDPDTQuestion`, `pulariDPDTQuestion_of_lit` |
| Q-weak | "It would be interesting to determine whether some weaker condition (e.g. levelwise surjectivity or bounded-to-one behavior on each `Σ^n`) suffices for the same equidistribution characterization, or whether non-invertible finite-state relabelings can already break it." | For synchronous relabelings the question collapses: dense image forces levelwise surjectivity, which forces invertibility on reachable states, so the characterization holds for every synchronous Mealy relabeling that is a separator enumerator | `PulariWeakening`, `pulariWeakening_of_lit` |

Pulari's arXiv source keeps a commented-out sentence announcing "a separator enumerator computable
by a deterministic pushdown transducer" as the counterexample, and the surviving `O(n log n)`-time
construction still carries labels `lem:pushdown-se`, `prop:pushdown-dim0`.  This suggests (our
inference) that a pushdown version was attempted and withdrawn before v1, and Q-DPDT is what
remained.

## The construction

* **Names.**  The free-reduction coder `encRun` (stack = free reduction of the input under
  `aa → ε`): a letter equal to the stack top cancels it and emits `0`; any other letter is pushed
  and emits its difference from the old top.  Its inverse `decRun` is a one-state real-time DPDT
  (`mirrorDPDT`, `mirrorDPDT_runFrom`, `isDPDTEnum_mirror`) and, at each step, a permutation of the
  input letter, so it is a bijection on every `Σ^n` (`decRun_encRun`, `encRun_decRun`,
  `decRun_levelSurj`).  This is Carton–Perifel's compressor `𝒯_k` recoded to stay inside `Σ` and
  to preserve length.
* **Point.**  `cpReal k = 0.w₁w̃₁w₂w̃₂⋯` (Carton–Perifel 2024, Prop. 2.1), `wₙ` all length-`n` words
  in lexicographic order (`cpSeq`, `cpPrefix`).
* **Why it works.**  Levelwise bijectivity gives `k^n a_n^f(x) = ⌊k^n x⌋`
  (`bestBelow_grid_of_levelSurj`), equidistributed since `x` is normal
  (`kAdicEquidist_floor_of_normal`).  The name of `x↾n` is `encRun(x↾n)` (`pre_encSeq`).  Each
  block `w w̃` starts on an empty stack (`red(w w̃) = ε`) and the mirror half cancels
  `(|w| + |red w|)/2 ≥ |w|/2` letters, each emitting `0`, so `0` has frequency `≥ 1/4` along block
  ends (`length_le_four_mul_count_zero`); for `k ≥ 5` the names are not normal
  (`not_isNormal_encSeq_cpSeq`), so their FS-dimension is `< 1` (`fsDim_lt_one_of_not_normal`), and
  the decoder transfers the bound to `dim^f(x)` (`fDim_le_fsDim_of_decode`).

## Difficulty check

* **Proved implications** (Lean, no `sorry` in the proof term itself): `mirrorEnum_cpReal_facts_of_not_normal`,
  `pulariDPDTQuestion_of_lit`, `pulariWeakening_of_lit`, `fsDim_lt_one_of_not_normal`,
  `mirror_not_mealy`, `pulariDPDTQuestion_of_zeroFreqHalf` (stretch); the coder/decoder algebra and
  the DPDT realization; the `decide` anchor `encRun_cpPrefix_five_one_anchor`.
* **Unproved premises.**  Leaves with confidence in their docstrings:
  `isSepEnum_grid_of_levelSurj` 92, `bestBelow_grid_of_levelSurj` 92,
  `kAdicEquidist_floor_of_normal` 92, `fDim_le_fsDim_of_decode` 88, `fsDim_le_one` 95,
  `pre_encSeq` 97, `length_le_four_mul_count_zero` 92, `not_isNormal_encSeq_cpSeq` 90,
  `mealy_levelSurj_of_isSepEnum` 95, `exists_invertible_of_levelSurj` 93.  All elementary; none
  carries the crux, which is the counting identity `C = (|w| + |red w|)/2`.
* **Cited hypotheses (need a referee).**
  * `Literature.cartonPerifel_normal`: normality of `w₁w̃₁w₂w̃₂⋯`.  Their Prop. 2.1 asserts it in
    the statement; the proof is a one-line pointer to the Champernowne argument (Becher–Carton
    2018, Thm 7.7.1).  Transcribed for all `k ≥ 2`; their "large enough `k`" concerns compression.
    Referee point: the base range, and whether the pointer proof is adequate.
  * `Literature.fsDim_one_isNormal`: "`inf_T liminf K^T(S↾n)/n = 1` ⇒ normal", the composite of
    Bourke–Hitchcock–Vinodchandran 2005 and Doty–Moser (cs/0609096) Thm 3.11, as Pulari Lemma 1
    composes them.  Referee point: that our `FST` (outputs in `Σ*`, no injectivity, start state `0`)
    matches the Doty–Moser decompressor model.
  * `Literature.pulari_coherent_eqchar` (only for Q-weak and the guard): Pulari Thm 3, read through
    `⌊·⌋` (his Lemma 6 makes the sequence integral).
* **Mechanism.**  The stack lets a one-pass relabeling turn mirrored structure into cheap names.
  A finite control cannot: `mirror_not_mealy` derives, from Pulari Thm 3, that no synchronous Mealy
  machine computes `decRun`.  That is the known-true control: on the finite-state class the
  construction must fail, and the Lean statement says it does.
* **Known-false sibling.**  `delayEnum` (stretch): a two-state, non-synchronous finite-state
  relabeling with `k ∣ k^n a_n^f(x)` (`k_dvd_scaled_delayEnum`), never `k`-adically
  equidistributed (`not_kAdicEquidist_delayEnum`), while normal points stay `delayEnum`-normal
  (`isFNormal_delayEnum_of_normal`).  Synchronicity, not finiteness of memory alone, is what
  `pulariWeakening_of_lit` uses.
* **Where the mechanism runs out.**  The `1/4` bound separates from `1/k` only for `k ≥ 5`.
  `ZeroFreqHalf` (open, 60%) would give `k ≥ 3`; base 2 (`PulariDPDTBaseTwo`) is out of reach of
  free reduction (no drift on `ℤ/2 * ℤ/2`).

**Success estimates.**  Q-DPDT answer correct as stated (`k ≥ 5`): 85% (risks: the Carton–Perifel
normality transcription, definitional drift between our `fDim` and Mayordomo's).  Q-weak answer:
93%.  A treadmill discharging every main-file leaf: 70%.  The answer to Q-weak is a collapse
rather than a construction; a referee may call it an observation.  Q-DPDT is the substantive one.

## Probe (numerics, with control)

`encRun` applied to `cpPrefix k N` (Python re-implementation of `encStep`/`decStep`; round trip
`P(Q(x)) = x` asserted):

| k | prefix length | zero-frequency of names | 1/k |
|---|---|---|---|
| 2 | 16388 | 0.5147 | 0.5000 |
| 3 | 12030 | 0.5030 | 0.3333 |
| 4 | 12744 | 0.5020 | 0.2500 |
| 5 | 5860 | 0.5027 | 0.2000 |
| 7 | 2268 | 0.5040 | 0.1429 |

Control: the same coder on the non-mirrored lexicographic concatenation (`k = 5`) gives 0.1765, so
the excess zeros come from the mirror halves.  The Lean anchor `encRun_cpPrefix_five_one_anchor`
checks the first block exactly (6 zeros in 10 letters).

## Prior-art searches (all 2026-10-04)

| Search | Result |
|---|---|
| `papers followups 2602.01199` (Pulari) | 0 citing papers |
| `papers followups 2205.00734` (Carton–Perifel) | 1: Bienvenu–Gimbert–Pulari 2502.12307 (Agafonov/Schnorr–Stimm for probabilistic automata); not about enumerators |
| arXiv author listing, Pulari (asker), newest first | 2602.23030 (FS-independent normal pairs), 2602.01199, 2510.18736 (Markov-chain FS dimension, Agafonov generalization), 2502.12307, …; sources of 2602.23030 and 2510.18736 grepped: no "separator", no "pushdown" |
| arXiv author listing, Mayordomo (expert, poser of the original question) | 2509.05211, 2502.09995, 2411.04959, 2312.10204, 2208.00157; none on pushdown enumerators.  2208.00157 §"Conclusions and open questions" is the source of the original equidistribution question; 2312.10204 (Calvert et al.) mentions equidistribution only in passing |
| arXiv author listing, Carton (expert) | 2606.30496, 2406.18383, 2406.09868, 2405.08532, 2405.01953, …, 2205.00734; none on enumerators |
| arXiv author listings, Nandakumar, Calvert | nothing on enumerators after 2602.01199 |
| arXiv full text `"separator enumerator"` | only 2602.01199 (plus unrelated graph-theory hits) |
| arXiv full text `"f-normality"` | only 2602.01199 (rest unrelated) |
| arXiv full text `pushdown normal sequence` | 2205.00734 only |
| Web: "separator enumerator f-normality pushdown transducer equidistribution Mayordomo Pulari" | only 2602.01199 (v1, v2) |
| Web: "Normality and automata" Becher Carton Heiber pushdown | BCH 2015 (JCSS 81) and Carton–Perifel 2024, which closes BCH's open "?" (deterministic one-stack compression) |
| `gh pr list/issue list --repo google-deepmind/formal-conjectures --search` "separator enumerator", "finite-state dimension", "pushdown", "Agafonov", "normal sequence automaton", "Pulari" (`--state all`) | nothing relevant |

## Other candidates considered

| Candidate | Status |
|---|---|
| BCH 2015 (JCSS 81) open "?": can a deterministic pushdown transducer compress a normal word? | Answered yes by Carton–Perifel 2024 (arXiv:2205.00734); used here as an input |
| Agafonov for probabilistic selectors | Answered (Bienvenu–Gimbert–Pulari 2502.12307); Markov-chain generalization 2510.18736 |
| Pulari 2602.01199 "widest natural family" | Not frozen; the two headlines bracket it (synchronous FS: holds; synchronous one-stack: fails) |
| Bergelson–Downarowicz 2506.12929 items 2, 3 (Kamae/`DeterministicBD` link) | Unchanged from the 2026-10-02 sweep; this toolkit does not move their crux |

**Not searched this pass** (limits of the prior-art claim): Becher–Carton–Heiber "Finite-state
independence" open questions; Carton–Vandehey non-oblivious group selection; Airey–Mance
normality-preserving operations for Cantor series; journal-only versions of 2602.01199.

## Required declarations

`src/NormalNumbers/FiniteStateSelection.lean:pulariDPDTQuestion_of_lit,pulariWeakening_of_lit,mirror_not_mealy,mirrorEnum_cpReal_facts_of_not_normal,PulariDPDTQuestion,PulariWeakening,cartonPerifel_normal,fsDim_one_isNormal,pulari_coherent_eqchar`

## Update 2026-10-04 (later): leaves discharged

All ten leaves of `FiniteStateSelection.lean` are proved; `pulariDPDTQuestion_of_lit`,
`pulariWeakening_of_lit` and `mirror_not_mealy` now rest only on the three cited `Literature.*`
hypotheses.  The counting core went through a sharper invariant than the audit planned:
`count_inv` (`|s| + |w| ≤ 2·#0 + |stack|` for any coder run) plus the mirror-return lemma
`encStk_reverse` (on a reduced stack, reading `w` then `w̃` restores the stack) give
`block_count` (`#0 ≥ |w|` on `w w̃`) and `cpPrefix_count` (`#0 ≥ |prefix|/2` at every block end).
Consequence, new: `not_isNormal_encSeq_cpSeq_of_three` and `pulariDPDTQuestion_of_lit_three`
answer Q-DPDT for every base `k ≥ 3`, bypassing the open `ZeroFreqHalf` node.  Base 2
(`PulariDPDTBaseTwo`) is still open: the `1/2` lower bound does not separate from `1/2`.
