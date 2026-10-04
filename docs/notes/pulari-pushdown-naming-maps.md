# Pulari's two questions on naming maps: answers checked in Lean

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

S. Pulari, [arXiv:2602.01199](https://arxiv.org/abs/2602.01199) (v2, 3 Feb 2026), §5 "Discussion and open questions", asks two questions about finite-state dimension relative to a naming map (separator enumerator) `f`, Mayordomo's `dim^f_FS`.  This note records answers to both.  Each is a Lean theorem, linked below at commit [`115de863`](https://github.com/gotrevor/normal-numbers/tree/115de8635b467fd649b556f8400a336ffb16c1ae).  Both rest on cited published results, stated as hypotheses; their transcription is the part most worth an expert's eye.

## 1. Deterministic pushdown naming maps: yes

Pulari asks: "One concrete setting is when the naming map is computable by a deterministic pushdown transducer.  In particular, does there exist such a separator enumerator `f` and a point `x ∈ [0,1)` for which the integer sequence `(k^n a_n^f(x))_{n≥1}` is `k`-adically equidistributed while `dim^f_FS(x) < 1`?"

**Theorem.**  Yes, for every base `k ≥ 7`, with a real-time (letter-to-letter) deterministic pushdown transducer.  Assuming in addition that the Carton–Perifel sequence below is normal for every `k ≥ 2` (a believed lemma, stated separately), yes for every `k ≥ 3`.

- [`PulariDPDTQuestion`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L384): the question as a Lean statement.
- [`pulariDPDTQuestion_of_lit`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L1280): `k ≥ 7`.
- [`pulariDPDTQuestion_three`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L1292): `k ≥ 3`, through the lemma [`isNormal_cpSeq`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L1255) (open in Lean).

**Construction.**  `x = 0.w₁w̃₁w₂w̃₂…`, where `wₙ` lists all length-`n` words in lexicographic order and `w̃ₙ` is its mirror image (Carton–Perifel, [arXiv:2205.00734](https://arxiv.org/abs/2205.00734), Prop. 2.1).  The naming map is the decoder of a free-reduction coder: reading a letter equal to the top of the stack, the coder pops it and outputs `0`; any other letter is pushed, and the coder outputs its difference from the old top (mod `k`).  The decoder permutes each input letter according to the stack, so it is a bijection on every length `n`.  Hence `f` hits every grid point, is a separator enumerator, and `k^n a_n^f(x) = ⌊k^n x⌋`, which is `k`-adically equidistributed because `x` is normal.  The names of the prefixes of `x` are the coder's output.  Each block `w w̃` forces at least `|w|/2` cancellations, so the output is not normal ([`not_isNormal_encSeq_cpSeq`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L1031)), its finite-state dimension is below 1, and the decoder carries that bound to `dim^f_FS(x)`.

**The stack is needed.**  No synchronous finite-state machine computes this decoder ([`mirror_not_mealy`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L1329)), by the answer to question 2.

**Base 2 is open here** (`PulariDPDTBaseTwo` in `FiniteStateSelectionStretch.lean`): the cancellation count does not separate there.

## 2. Non-invertible synchronous relabelings: they cannot break the characterization

Pulari asks: "It would be interesting to determine whether some weaker condition (e.g. levelwise surjectivity or bounded-to-one behavior on each `Σ^n`) suffices for the same equidistribution characterization, or whether non-invertible finite-state relabelings can already break it."

**Theorem.**  For synchronous (letter-to-letter) finite-state relabelings, the characterization of Pulari's Theorem 3 holds for every one that is a separator enumerator, with no invertibility assumed ([`PulariWeakening`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L392), [`pulariWeakening_of_lit`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L1315)).

The reason is short: a synchronous relabeling with dense image is surjective on every length, which for a synchronous machine is the same as being invertible on reachable states, so Theorem 3 applies.  So levelwise surjectivity is not a weaker condition in the synchronous case, and a bounded-to-one non-injective synchronous relabeling is never a separator enumerator.  Relabelings that are not letter-to-letter remain open.

## Cited inputs

- [`Literature.cartonPerifel_normal`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L349): Carton–Perifel Prop. 2.1, stated for `k ≥ 7` (their proposition says "large enough `k`" and the paper notes `k ≥ 7` suffices).
- [`Literature.fsDim_one_isNormal`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L361): finite-state dimension 1 implies normality (Bourke–Hitchcock–Vinodchandran 2005, with Doty–Moser Thm 3.12 for the decompression form).
- [`Literature.pulari_coherent_eqchar`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L369): Pulari's Theorem 3.

Pulari's §2 leaves the pushdown naming map undefined; [`IsDPDTEnum`](https://github.com/gotrevor/normal-numbers/blob/115de8635b467fd649b556f8400a336ffb16c1ae/src/NormalNumbers/FiniteStateSelection.lean#L181) is a real-time subclass of the Carton–Perifel model, so the answer to question 1 holds under any reasonable reading.

## What is not claimed

- Question 1 in base 2, or for `3 ≤ k ≤ 6` without the separate normality lemma.
- Question 2 for relabelings that are not letter-to-letter.
- Priority beyond our search: forward citations of 2602.01199 (none found), recent arXiv by the asker and nearby authors, and `google-deepmind/formal-conjectures`.  Corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 115de8635b467fd649b556f8400a336ffb16c1ae
lake exe cache get
lake build NormalNumbers.FiniteStateSelection
```

Questions and corrections: please open an issue on this repository.
