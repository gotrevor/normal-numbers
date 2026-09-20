# HANDOFF 2026-09-20 — campaign B reaches its pre-registered FINISH LINE

Branch `wip/g5-prime-subset`.  Build 🟢 **9103 jobs**.  `src/` = the two pre-expedition
forbidden-drift `sorry`s (`phaseOscillation`, `exists_prime_nonresidue`); **zero `axiom`s**.

This lap opened on the attended `RoughIndependence` override (now closed, see
`HANDOFF-2026-09-20-rough-independence.md`) and then returned to the standing CURRENT
DIRECTIVE of 2026-09-16 — *campaign B FINAL: the `a`-side, and then STOP*.  Both of the
directive's terminating conditions are now met.

## 1. The terminal objective: DONE, with its audit theorem

`SchedB.isDisjunctive_weightA_logLog` had already landed in earlier laps (steps 1–3 of the
mandated order: `G4PhaseA`, `G4WeightAWitness`, `G4WeightASched`).  Step 4's **audit theorem
was missing**; it is now in `G4WeightStatement.lean`:

```
audit_isDisjunctive_weightA_logLog :
  ∀ a c bounded/tame as stated, b ≥ 3,
  IsDisjunctive b (∑' n, (∑_{p ∣ n} a_p + ∑_{p ∣ n} c_p (v_p(n) − 1)) / bⁿ)
```

Every abbreviation unwound — no `TWeight`, no `weightALambert`.  Trust-triple clean.

## 2. The one permitted stretch: REFUTED IN THE KERNEL

The directive's single permitted stretch was the general additive `f` with `f(p^v) ≤ a_p +
c_p(v−1)`, `f(p) = a_p`, `f` non-decreasing — hoped to ride the far-field domination
`sum_abs_farPartW_le_of_layer` "with no new §4D work".  It cannot, and the reason is upstream of
§4D entirely.  New file **`src/NormalNumbers/G4AdditiveRigidity.lean`** (sorry-free,
trust-triple clean) proves it, as theorems about the bare `TWeight` interface:

| theorem | content |
|---|---|
| `TWeight.ov_eq` | `mul_eq` forces `ov d m = w(m) + w(d) − w(dm)` |
| `TWeight.wN_prime_pow_second_diff` | for **any** `W`, prime `p`, `v ≥ 1`: `w(p^{v+2}) − w(p^{v+1}) = w(p^{v+1}) − w(p^v)` |
| `TWeight.wN_prime_pow_first_diff` | the first difference is constant from `v = 1` |
| `TWeight.wN_prime_pow_affine` | `w(p^v) = w(p) + (v−1)(w(p²) − w(p))`, `v ≥ 1` |
| `TWeight.ov_one` | `ov d 1 = w(1)` |
| `TWeight.wN_mul_of_modEq_one` | `m ≡ 1` mod every prime of `d` ⟹ `w(dm) = w(d) + w(m) − w(1)` |
| `TWeight.wN_prime_pow_mul` | both at once: `w(p^v·m) = w(p) + (v−1)(w(p²)−w(p)) + w(m)` |
| `TWeight.addWeightN` + `affine_of_addWeightN_isTWeight` | an additive weight admits the interface ⟹ every per-prime profile is affine on `v ≥ 1` |
| `TWeight.weightAN_prime_pow`, `addWeightN_affine_eq_weightAN` | converse: every affine profile **is** realised, and the affine families are exactly `w_{a,c}` |

The proofs are short — `ov_congr` at `d = p`, `m = p^v`, `m' = p^{v+1}` (congruent mod `p`,
both `0`) for the affine law, and at `m' = 1` for the multiplicative one.  Nothing is assumed
about the weight beyond the interface: not additivity, not multiplicativity, not monotonicity.

**Consequence.**  `G4WeightInterface`'s prose claim — "the exact affine transport identity holds
iff every `g_p` is affine on `v ≥ 1`" — is now a machine-checked biconditional, in a stronger
form than the prose (it is about the interface, not about a chosen additive model).  So
`w_{a,c}` is not *a* class the machine happens to handle: it is **the** class the transport
interface admits.  A non-affine `f` is not a `TWeight` at all, so no far-field domination
argument can reach it.  The stretch is a **proved obstruction**, per the directive's 🚦 rule.

## 3. Where that leaves the repo

Both FINISH LINE conditions are satisfied and the directive's own closing instruction is
"write the handoff and stop; do not open a successor campaign by re-parametrizing again".

The two `sorry`s left in `src/` are **both on the directive's ⛔ forbidden-drift list**:

* `PrimeLambertOscillation.phaseOscillation` — the *base-two* constant `∑ ω(n)/2ⁿ`, the
  proved-dead case, superseded in the literature by Tao–Teräväinen arXiv 2512.01739 Thm 1.3;
  the `b ≥ 3` half is ours (`irrational_primeSum`, trust-triple clean).
* `MahlerDriftOne.exists_prime_nonresidue` — a prime in `(p/3, p/2)` with a prescribed Legendre
  symbol; Linnik-strength, unconditionally open, not in mathlib.

So the repo does not need more work *inside* this directive; it needs a new directive from an
altitude lap.

## 4. Candidate next directives (for the altitude lap, not acted on here)

1. **Widen the transport interface.**  The rigidity theorems say exactly what `ov_congr`
   costs.  Relaxing it to "`ov d m` depends on `m` mod `(rad d)^k`" would admit non-affine
   profiles; the open question is whether §4D's periodicity budget survives.  This is the
   mathematically live continuation, and it is now *precisely formulated* rather than vague.
2. **Is every normalised `TWeight` additive?**  `wN_mul_of_modEq_one` gives additivity when
   `m ≡ 1` mod `rad d`.  Whether general coprime `d, m` follow looks like it needs Dirichlet
   (choose a prime `q ≡ m` mod `rad d`) — attempted and *not* settled this lap; recorded as
   open, not as refuted.
3. The SD-sector thread of the other override: probe `SmoothRoughDecoupling`
   (`HANDOFF-2026-09-20-rough-independence.md`), the only unprobed node in the new `G₄` chain.
