# Probe: Route A's crux - does the φ·x transducer keep a compact, bounded-distortion state?

*Ren, 2026-08-24.  Instrument: `experiments/route_a_window.py` (pure stdlib, uv shebang,
`selftest` mode).  Target of the probe: `papers/vandehey-2017-open-problem-attack-map.md`
§3, "Route A (the real attack): Vandehey with a COMPACT fiber".*

---

## 0.  The ask

> A computational probe of Route A's crux.  The whole program hinges on one
> empirical-checkable claim: run the φ·x transducer on random CF input and watch whether
> the projectivized state keeps returning to a compact bounded-distortion window with rapid
> loss of memory.  That's a one-afternoon uv script, and it converts "50% hunch" into
> either "the mechanism visibly works, write the blueprint" or "the state drifts, the
> program is dead" - before a single Lean line.

## 1.  Verdict 🎯

**The mechanism visibly works - and the probe located the two places where §3's wording is
wrong, both of them repairable, one of them a genuine sharpening of the hardest lemma.**

| Route A claim | Probe says | Confidence |
|---|---|---|
| The state does not drift; the dynamics ignores the conjugate place | ✅ confirmed, quantitatively | 90% |
| "W = a compact window in **PGL₂(ℝ)**" | ⚠️ **false as stated** - and false in the *proved* case too, so it is not an obstruction, it is a mis-statement.  What is true is **bounded distortion** | 85% |
| "Post-emission boundedness should be automatic exactly as in the integer case" | ❌ **the integer case's boundedness is an INTEGER DESCENT, not geometry** - this is the real content of "the first lemma to prove carefully" | 85% |
| Lemma 2.2 (burst uniformly bounded) ports | ❌ **does not port**; replacement measured and derived: `burst ≈ ln(a)/λ`, λ = Lévy.  Lemma 6.1 survives because `∫log a dμ < ∞` | 90% |
| "Doeblin/coupling condition … Birkhoff–Hopf supplies asymptotic loss of memory" | ✅ but must be **distributional**; pathwise merging is **provably impossible** (one-line proof, §5.3).  Loss of memory measured and it is fast | 85% |

**Recommendation: write the blueprint.**  Nothing the probe found is a wall; the two
corrections make §3's first lemma *sharper and more honest*, and the burst finding hands
the blueprint a concrete quantitative lemma in place of a citation that does not port.
The 35%-priced crux (i) - uniformity over *all* CF-normal inputs - is only lightly poked
(§4.5) and remains the open risk.

## 2.  Why the probe is DIFFERENTIAL, and why that matters

The original design was "measure φ, apply a threshold".  That is worthless here: there is
no a-priori scale for `log‖G‖`, and any statistic could be blamed on the transducer rather
than on ℤ[φ].  So every measurement is run **side by side on maps where Vandehey's Theorem
1.1 is TRUE** (`2x`, `3x`, `x/2`, `(x+1)/2`) **and on maps where §7 problem 1 is OPEN**
(`φx`, `x/φ`, `x+φ`, `√5·x`).

The integer controls calibrate the scale.  A statistic that behaves identically on both
sides cannot separate "provable" from "unprovable" and is therefore not evidence against
Route A - *whatever its absolute value*.  A statistic that separates them is a candidate
wall.  This turned out to matter: two of the headline statistics behave badly on **both**
sides, which would have read as "Route A is dead" under the threshold design.

## 3.  The instrument

**Exactness.**  Every decision that steers the run is exact integer arithmetic in ℤ[φ]
(`u + v·φ`); floats appear only in reported statistics.  Signs use
`2(u+vφ) = A + B√5`, and logs use `|N(e)| = |A²−5B²|/4` to recover whichever archimedean
place cancels - so the real place stays accurate to full precision even when the integer
coefficients are 60 000 bits and the value they represent is O(1).

**The transducer** (verified in `selftest` T1 against an independent CF computation):

```
x = [0; a₁, a₂, …],  A_a = [[0,1],[1,a]],  x = A_{a₁}(Tx)
state  G ← G·A_a        consume one input digit
emit c when G([0,1]) ⊆ [1/(c+1), 1/c];  then G ← A_c⁻¹·G
```

⚠️ **This is NOT Vandehey's §2 transducer** - see §5.1.  It computes the same output
stream (that is what T1 checks), by a weaker renormalisation.  Frequency and memory
results are therefore about the right object; window results are about *this* state.

**Statistics.**  `lognorm_real` = log‖G‖/√|det| (compactness in PGL₂) · `lognorm_conj`
(same at the Galois place) · `log κ` = log of sup|G′|/inf|G′| on [0,1] (distortion) ·
`log|J|` · distinct post-emission states · burst / wait / `c₁` = output-per-input.

**Inputs.**  `lebesgue` - exact CF digits of a genuinely uniform random real, realised
lazily from random bits (a digit is emitted only when both endpoints of the dyadic
interval agree on it, and CF-prefix sets are intervals, so agreement at the endpoints is
agreement throughout).  `structured` - CFs of `p/q` concatenated: **deterministic,
measure-zero**, the only input that says anything about crux (i).  `adversarial` -
uniform real with planted digits up to 10¹⁵.  `periodic`, `iid` - red controls.

**Teeth** (`./route_a_window.py selftest`, all five pass):

| | test | what it would catch |
|---|---|---|
| T1 | output vs an independent exact CF of `φ·(p/q)` | a wrong transducer - everything else would be noise |
| T2 | integer M repeats states constantly; ℤ[φ] M **never** repeats (a theorem, §5.3) | broken ℤ[φ] arithmetic or a mis-canonicalised state |
| T3 | skip legal emissions with p=0.5 → `lognorm` max must blow up | a window statistic that cannot detect drift (it moves +99.7 nats) |
| T4 | a periodic input under an **integer** map → output TV 12.3× worse | a frequency statistic with no power |
| T5 | independent inputs must **not** couple | a coupling detector that fires on noise |

T4 needed fixing mid-flight, and the reason is itself a small finding: a periodic input
under `x ↦ φx` gives a **Gauss-typical-looking output**, because φ·(quadratic) is
*quartic*.  The red control has to keep the output inside one real quadratic field, which
only an integer map does.

## 4.  Results

### 4.1  The differential table

`compare`, 3000 steps, exact uniform-real input:

```
map       status     med     p99   p99.9     MAX   medkap  maxkap  burst      c1 conj/step
2x        PROVED   1.040   4.559   7.042   7.335    0.673   1.386      4  1.0077    0.000
3x        PROVED   1.060   4.992   6.951   7.474    0.811   1.386      4  1.0130   -0.000
x/2       PROVED   1.040   5.065   6.475   7.781    0.673   1.386      4  0.9857    0.001
(x+1)/2   PROVED   1.040   5.092   6.472   7.169    0.673   1.386      4  0.9953    0.000
phi       OPEN     1.178   5.169   6.933   7.766    0.701   2.507      9  0.9830    2.353
x/phi     OPEN     1.147   5.860   7.453   9.359    0.692   2.424      9  0.9653    2.354
xphi      OPEN     1.169   5.463   7.085   7.949    0.696   2.277      9  0.9883    2.354
sqrt5x    OPEN     1.160   5.161   7.477   9.073    0.703   2.472      9  0.9857    2.355
```

The OPEN rows sit inside the PROVED spread on the whole state distribution (median, p99,
p99.9, max, median distortion) and on `c₁`.  Two columns separate - `maxkap` and `burst` -
and they are §5.2's finding.

### 4.2  The conjugate place dies at exactly the predicted rate

`conj/step` = **2.353–2.355 nats/step** for all four ℤ[φ] maps, **0.000** for all four
integer maps.  Predicted: `G^σ_n = B_n⁻¹ σ(M) P_n` with `B`, `P` integer (hence
self-conjugate), so with no telescoping the growth is `‖B‖·‖P‖ ≈ e^{2λn}`,
`2λ = 2·π²/(12 log 2) = 2.373`.  Measured 2.354.

This is the whole thesis of §1 of the attack map in one number: **Dirichlet's units destroy
the finiteness certificate at a linear rate while every dynamical column is unchanged.**
Entry coefficients grow 3.40 bits/step, which is also the run-length limit (cost is
quadratic; 9 000 steps takes 92 s for phi against 10 s for the integer maps, and 18 000 did not finish in 25 min).

### 4.3  The window survives a 10¹⁵ digit

`window --input adversarial`, planting digits 10³ … 10¹⁵ every 25 steps:

```
max lognorm after a HUGE digit: 6.903   after a normal digit: 8.733
```

The state is **calmer** after a planted 10¹⁵ digit than after an ordinary one, and returns
to the window within one step (per-digit trace in the tool output).  Crux risk (ii)'s
worry - that unbounded-rank excursions blow the state up - is empirically not about the
window.  `max log κ` was **2.507 at 3 000 steps and 2.507 at 9 000 steps**: saturated.

### 4.4  Memory: a clean red/green pair

`memory`, 120-digit burn-ins, 1 200 shared steps:

| | `2x` (PROVED) | `φ` (OPEN) |
|---|---|---|
| exact state merge | **step 3** | **never** |
| longest common output tail | 1217 / 1220 | **0** |
| state-law TV, different start | 0.0842 | 0.1367 |
| state-law TV, same start (noise floor) | 0.0983 | 0.1458 |
| output 2-block TV, different start | 0.0665 | 0.0868 |

Pathwise: the finite-state synchronising mechanism fires instantly for `2x` and **provably
cannot** fire for `φ` (§5.3).  Distributionally: both sit **at or below their own noise
floor**, i.e. the state law does not remember its start.  Birkhoff–Hopf contraction of the
input blocks - the mechanism §3 cites - measured directly: mean Hilbert diameter
**0.213 (k=2) → 0.013 (k=4) → 0.000 (k=8)**.  Memory of anything before an 8-digit block
is gone.  "Rapid" is justified.

### 4.5  A deterministic, measure-zero input (the only non-vacuous frequency test)

A random input proves nothing about the theorem: for a.e.  `x`, both `x` and `Mx` are
CF-normal for free, so the whole frequency test is vacuous there.  The `structured`
stream is not: it is a single deterministic sequence in a Lebesgue-null set.

`freq --map phi --input structured`, 6 000 input digits:

```
stream                       TV 1-block TV 2-block TV|d<6     P(d>=6)   n
input                        0.0854     0.1256     0.0747     0.1718    6000
output (Mx)                  0.0113     0.0241     0.0097     0.2159    5429
random-real baseline         0.0192     0.0319     0.0128     0.2332    5429
noise floor (half-vs-half)   -          0.0603
Gauss tail mass P(d>=6) = 0.2224
```

The input is measurably off Gauss (`TV|d<6` = 0.075, tail mass 0.172 vs 0.222) and stays
off: 0.088 even at 200 000 digits (it converges, slowly).  **The φ-image is at sampling
noise - indistinguishable from the CF of a random real, and slightly better than the
baseline.**  `TV|d<6` conditions away the tail bucket, so the input's truncated digit
range cannot flatter either side; the effect survives that.

⚠️ Read this carefully: it does **not** show the input is CF-normal, and it is one input.
What it shows is that whatever structure the input still carries at this length, the
transducer has already washed out - which is loss of memory visible in the statistic the
theorem is actually about.

## 5.  Three corrections to attack-map §3

### 5.1  "Post-emission boundedness should be automatic exactly as in the integer case" - no

Read against the PDF (`papers/vandehey-2017-matrix-actions-cf-normality.pdf` §2):
`M_D` is the set of det ±D matrices satisfying one of six Type I–VI sign/inequality
conditions, and finiteness comes from *"the above conditions paired with determinant
requirement"* giving `|α|,|β|,|γ|,|δ| ≤ |D|`.  Lemma 2.1 reduces any `M·J·A_j` back into
`M_D`, and its termination argument is:

> *"at every stage … we rearrange the coordinates and subtract at least 1 from one of them
> (no coefficients grow in size) … Thus after some finite number of steps we must arrive at
> a matrix `M_m ∈ M_D`."*

**That is an integer descent.**  It terminates because ℤ is discrete and well-ordered
below.  Over ℤ[φ] there is nothing to descend on - the ring is dense, the unit group is
infinite, and "subtract at least 1" has no meaning.  So the integer case's boundedness is
*not* geometric and does not transfer by analogy; Route A's window lemma needs a genuinely
different proof (a contraction/renormalisation argument), not "the same argument with
compactness substituted for finiteness".

This is the sharpest thing the probe found and it *raises* the value of §3's own remark
that this is "the first lemma to prove carefully" - it is a lemma, and its integer
ancestor gives no help with the proof, only with the statement.

### 5.2  Drop "compact in PGL₂(ℝ)"; keep "bounded distortion"

Vandehey's normal forms have entries ≤ D, so his states *are* compact in PGL₂.  The
**greedy** post-emission states are not - in either case.  Structurally: a state whose
image interval straddles `1/c` at depth ε has `|J| ≈ ε`, hence `s(r+s) ≈ D/ε`, hence
entries ~ √(D/ε), unbounded.  Empirically, for `2x`: max `lognorm` 6.64 → 7.34 → 9.47 →
9.90 at n = 1 000 → 8 000, and distinct states 259 (n=3 000) → 432 (n=8 000), still
climbing - **in the case where the theorem is TRUE.**

But `log κ` (distortion) is **bounded in both**: exactly **1.386 = log 4** for every
integer control, saturating at **≈ 2.5** for every ℤ[φ] map.  So the invariant that
survives the weaker renormalisation, on both sides, is bounded distortion - and §3's own
phrase "a compact window in PGL₂(ℝ) of bounded-distortion maps" should keep its second
half and drop its first, or else be stated for the *reduced normal forms* rather than the
raw post-emission state.

### 5.3  "Doeblin/coupling condition" cannot be pathwise - and needn't be

For `M = diag(φ,1)`, two states `B₁⁻¹MP₁` and `B₂⁻¹MP₂` coincide iff
`M⁻¹(B₂B₁⁻¹)M = P₂P₁⁻¹` is integral; for `V` integer,
`M⁻¹VM = [[v₁₁, v₁₂/φ],[v₂₁φ, v₂₂]]` is integral only if `v₁₂ = v₂₁ = 0`, so `V` is
diagonal and the two runs had the same input prefix.  **Exact merging is impossible, and
so (by Serret, same computation) is exact output-tail coupling.**  Confirmed: never in
1 200 steps, common tail 0, against `2x` merging at step 3.

That is not a failure - it is the reason §3 is right to reach for Birkhoff–Hopf.  But the
blueprint must state the merging hypothesis **distributionally** (the state's empirical law
converges to ρ independent of the start), never as a coupling/synchronising word, and the
Saloff-Coste–Zúñiga citation should be replaced accordingly.  §4.4 measures the
distributional version holding, at the noise floor.

### 5.4  Lemma 2.2 does not port; here is the replacement

Vandehey's proof of Lemma 2.2 derives bounded burst *from* finiteness - *"there are only
finitely many choices for `−γ′/α′`, since `M_D` is a finite set, so `m` must be uniformly
bounded"* - so it has no ℤ[φ] analogue by construction.  Measured (`burst` mode, one
planted digit `a` through 40 random states):

```
a          ln a    2x        3x        phi       x/phi     xphi      sqrt5x
1e+01      2.30    1.60      1.75      2.05      1.98      2.10      1.57
1e+05      11.51   1.60      1.75      9.93      9.93      9.40      9.18
1e+12      27.63   1.60      1.75      22.73     23.20     23.45     24.43
1e+25      57.56   1.60      1.75      47.40     49.42     45.60     48.62
```

Integer columns **flat** over 24 orders of magnitude - that is Lemma 2.2, visible.  Every
ℤ[φ] column grows like `0.843·ln(a)`, and `0.843 = 1/λ` with λ = π²/(12 log 2) = 1.1866,
Lévy's constant.  Derivation matching the measurement: one input digit of size `a` pins the
image interval to precision ~`a⁻²`, i.e.  `2 ln a` nats, and CF digits carry λ nats each,
so `burst = 2 ln a / (2λ) = ln(a)/λ`.

**Proposed replacement lemma**: `burst(M, a) ≤ C_M + λ⁻¹ log(1+a)`.  This is unbounded, so
Lemma 2.2 is genuinely lost - but `∫ log a dμ < ∞` (the same finiteness that makes
Khinchin's constant exist), so the *mean* burst is finite and **Lemma 6.1's
`ℓ(n) = c₁n(1+o(1))` survives**.  Measured `c₁`: 0.965–0.989 for the ℤ[φ] maps against
0.986–1.013 for the integer controls.

Why the difference exists, structurally: for integer `M` the state's `G(0)` is a rational
of bounded height, so its CF is short and the burst stops; over ℤ[φ] the height drifts at
the conjugate place (§4.2), so `G(0)` has a long CF and a precise-enough input digit
unspools more of it.

## 6.  What this does NOT show

- **Nothing is proved.**  Every "bounded" here is "did not grow over the run", on runs
  capped by quadratic cost (9 000 steps for φ).
- **Crux (i) is barely touched.**  §4.5 is one deterministic input.  Uniform merging along
  *arbitrary* CF-normal inputs - the attack map's 35% risk - needs the `f_j^±` squeeze and
  cannot be settled by any finite experiment.  The instrument is ready for more inputs:
  any object with `.next()` plugs in, and `freq` reports the input's own distance from
  Gauss, so a candidate stream validates itself in the same run.
- **The measured state is not Vandehey's** (§5.1/5.2).  Implementing his Type I–VI
  reduction over ℤ[φ] - and watching whether *that* state stays bounded - is the obvious
  follow-on and would upgrade §5.2 from "distortion is what survives" to a direct test of
  the real window lemma.  Note there is no reduction *procedure* to implement over ℤ[φ]
  yet; that is the lemma.
- **The `structured` stream is not proven CF-normal**, only converging (TV 0.126 at 6k →
  0.088 at 200k).  Heilbronn's theorem makes it plausible; that is all.
- **No claim about §6.1's tightness gap.**  The fiber-side tightness that a compact `W`
  would give is what §4.3 supports; the *base*-side tightness of a CF-normal point's
  empirical measures - the obligation Airey–Mance leave Vandehey owing - is untouched here.

## 7.  Running it

```
./route_a_window.py selftest                                  # the teeth, ~2 min
./route_a_window.py compare  --steps 3000                      # the differential table
./route_a_window.py burst                                      # Lemma 2.2 vs its replacement
./route_a_window.py window   --map phi --input adversarial     # planted 10^15 digits
./route_a_window.py memory   --map phi                         # merging, both senses
./route_a_window.py freq     --map phi --input structured      # the non-vacuous frequency test
./route_a_window.py all      --map phi                         # everything + how to read it
```

Maps: `phi`, `x/phi`, `xphi`, `sqrt5x` (OPEN) · `2x`, `3x`, `x/2`, `(x+1)/2` (PROVED).
Inputs: `lebesgue`, `structured`, `adversarial`, `iid`, `periodic:1,2,3`.
Cost is quadratic in `--steps` (coefficients grow 3.4 bits/step); 9 000 steps takes 92 s for the Z[phi] maps, 10 s for the integer ones.

## 8.  Follow-ons, in value order

1.  **Implement the Type I–VI reduction over ℤ[φ]** - or discover there is none, which is
   itself the answer.  This is §5.1 turned into code, and it is the actual window lemma.
2.  **Feed a second and third structured CF-normal candidate** (Adler–Keane–Smorodinsky's
   explicit construction; a Champernowne-style stream weighted to Gauss).  Cheap, and it is
   the only lever this instrument has on crux (i).
3.  **Measure the stationary law ρ on W** - §3 predicts it may be singular and says nothing
   needs smoothness.  Worth knowing what it looks like before the counting section is
   written.
4.  **Repeat the whole table for a non-unit determinant over a different field** (`√2·x`
   over ℤ[√2]) to check that nothing here is special to ℚ(√5) or to det being a unit.
   `sqrt5x` already gives one non-unit data point and behaves identically.
