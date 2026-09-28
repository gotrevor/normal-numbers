# HANDOFF 2026-08-24 — B6: both isolated analytic doubts PROVED; item-3 = coupled bookkeeping

**Branch/HEAD**: master @ `db7c65f`, `lake build` green (8757 jobs), tree clean.
Sole active `src/` sorries: (1) the feasible crux `exists_interleaved_affine_witness`
(`CFScheduleA.lean`, now carries `hr : -q < r ∧ r < 1`), (2) the `TODO(shift)`
general-`r` case inside `exists_cfNormal_and_affine_cfNormal` (leaf: `IsCFNormal_add_int`).
B5′ headline stays trust-triple `[propext, Classical.choice, Quot.sound]` (re-checked);
B6 deliverable carries disclosed `sorryAx`.

## Working within DIRECTION.md (item 2/3: build the hdom-free chain limit)
Obeyed. All work additive in `CFScheduleA.lean`. Did NOT resurrect `hdom` or filler.

## This lap's arc (8 commits `8359029..db7c65f`, all axiom-clean)
1. **`exists_freq_good_extend_affine_steer_uniform`** — two-stream affine step emitting
   UNIFORM-PREFIX-good blocks (calls `exists_uniformly_freq_good_block_steer_len` per
   stream), exposing `n₁` + `n₁²≤|u|·√|u|` per stream. The `hblock` payload for
   `chain_orbit_equidist_uniform`. (Directive item-2, discharged.)
2. **CRUX WAS FALSE for `r∉(-q,1)`** (e.g. `(1,5)`: `x∈(0,1)∧x+5∈(0,1)` is impossible).
   Restricted crux to feasible `hr`; kept deliverable UNCONDITIONAL via `by_cases` +
   disclosed `TODO(shift)` (integer-shift invariance of CF-normality). ⚠️ JUDGE-FLAG in
   PENDING_WORK for altitude ratification of the statement change.
3. **`mem_wordFamily_eventually`** — coverage (every genuine `v` ∈ `wordFamily t` for
   `t ≥ max|v|(v.sum)`); mirrors `sched_t_tendsto` for the `hblock` per-`v` threshold.
4. **`slack_telescoping`** — THE `hslack` `o(word)` obligation, PROVED via
   `Asymptotics.IsLittleO.sum_range`. Given `word(s+1)=word s+blk s`, `C=o(blk)`,
   `blk→∞`, `blk s ≤ ρ·word s`: `∀ε>0 ∀s₀ ∃K ∀k≥K, ∑_{i≤k}(C(s₀+i)+c) < ε·word(s₀+k)`.
   The route-decisive analytic doubt — SETTLED.
5. **`exists_uniform_block_param_tight`** — word-independent block length:
   `m=max(⌈√max(Lc,Nfib)⌉+1,(⌈2/β⌉+1)²)` with `m²≤6(Lc+Nfib)+2+2(⌈2/β⌉+1)⁴` (LINEAR
   in Lc,Nfib; the old lemma was `m²~Nfib²` quadratic). Supplies `hgeom` (item i).
6. **`gaussMeasure_Ioo_toReal_ge/le`** — `(v−u)/(2ln2) ≤ μ_G(u,v) ≤ (v−u)/ln2` on
   `[0,1]`. Pins measure ratios to WIDTH ratios up to factor 2 (item ii core).

## Status: both ISOLATED analytic doubts are kernel-proved
- Does the hdom-free slack telescope? YES (`slack_telescoping`).
- Can block length be kept `O(word)`? YES (`exists_uniform_block_param_tight`).
Remaining item-3 is COUPLED BOOKKEEPING, not a new analytic wall.

## NEXT — item-3 build order (revised, in PENDING_WORK top; hardest-first)
- **(ii) measure-ratio lemma `γtar ≥ q·c₀·γwx`** — from a WIDTH bound
  `|target| ≥ c·|cfCylinder wx|` + today's density lemmas. ⚠️ needs the STREAM-BALANCE
  invariant `|wx_s| ~ |wz_s|` (else a stream's cylinder is exp. narrower and the ratio
  blows up). This is the one remaining genuinely-new fact.
- **(iii) length-exposing affine step** — do NOT rebuild `_len`; call the non-`_len`
  `exists_uniformly_freq_good_block_steer` DIRECTLY (returns exact `|u|=n₁+m²`), feeding
  `m` from `exists_uniform_block_param_tight`, proving `hbound` from (ii) and `hres` from
  `Nfib~|wx|`. Output exposes `|u| ≤ tight-bound`.
- **(iv) `SchedStateA` + promotion + balance** — mirror `CFSchedule.SchedState`/`sched`
  (`Nat.rec`+choice). State carries `(wx,wz,e,f)` + interval invariant
  `cfCylinder wx ⊆ ψ⁻¹(Ioo e f)` + promotion counter `t` (fixed family across stages,
  bump when `|w_s|` long enough) + BALANCE `||wx|−|wz||` bounded. Choose `δ_s=schedEps t`,
  `L_s` to force `blk≤ρ·word`.
- **(v) chains → assemble** — `wxSeq/wzSeq`, limit points via
  `exists_irrational_mem_iInter_cfCylinder` + `eq_of_mem_iInter_Icc` +
  `irrational_mem_Ioo_of_mem_iInter_cfCylinder` (all READY), feed BOTH into
  `chain_orbit_equidist_uniform` (`hblock` from `δ_s→0`+coverage; `hslack` from
  `slack_telescoping`). ⇒ `CFOrbitEquidist` both streams ⇒ feasible crux.
- Then `exists_cfNormal_and_affine_cfNormal` feasible case closes; the `TODO(shift)`
  leaf (`IsCFNormal_add_int`) closes the general-`r` case.

## Watch-outs
- `Σ` (U+03A3) is a RESERVED token — never use it inside identifiers (`hΣf` fails to
  parse). Use `hSf` etc.
- `open Asymptotics Finset in` must precede a doc comment, not follow it. `Asymptotics`
  is now opened file-wide (line 42).
- After the crux closes, re-`#print axioms exists_absolutely_normal_cf_normal_khinchin`
  — MUST stay trust-triple.
- Feasibility `hr : -q < r ∧ r < 1` is exactly `(0,1)∩ψ⁻¹(0,1) ≠ ∅`; the seed state is
  built INSIDE that interval.
