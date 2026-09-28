# ROUTE ESCALATION — 2026-09-15 — the base-`2^k` directive, **step 3**

Trigger: **E-T13** (lap-126-close CURRENT DIRECTIVE).  Steps 1 and 2 of that directive both
SUCCEEDED and are in kernel; the route fails at **step 3, "transport to the read"**.

## What is proved (keep, all axiom-clean)

| declaration | module | content |
|---|---|---|
| `abs_offset_class_le`, `abs_posAvgR_sub_le` | `G4EntropyOffsetClass` | step 1 — any sub-family of offset classes, same constant |
| `sum_resClasses_eq_sum_resPos`, `abs_posAvgRes_sub_le` | `G4EntropyResidue` | step 2 — for `k ∣ ℓ`, the positions `≡ c (mod k)` are a union of offset classes; same constant |
| `subLaw`, `H₂_subLaw_ge`, `abs_posAvgRes_subLaw_le`, `posAvgRes_subLaw_eq_digits` | `G4EntropySubLaw` | an arbitrary sub-family `S ⊆ P_K` of sample times, residue-certified |
| `winCountR`, `fullGoodWPreR`, `fullW_band_prefix_winCountR_bounds`, `fullW_prefix_winCountR_bounds`, `mem_res_iff_locRes`, `locRes_mod` | `G4EntropyResRead` | the residue-restricted counting layer for the read |

Step 2's identification is exactly as the directive predicted: `posEquiv` **is** the arithmetic map
`(r, j) ↦ r + jℓ`, and `k ∣ ℓ` makes `r + jℓ ≡ r (mod k)`.  E-T13's two *named* failure modes did
not fire.

## The failing step, exactly

The directive's step 3 says:

> Within window `a` of band `i` the needed class is `q ≡ (fTW i + a·kk i) (mod 2)` — it *depends
> on `a`*, but **both** parity classes carry the same bound, so this costs nothing.

**That last clause is false, and here is why.**  `mem_res_iff_locRes` (proved) says a read position
in window `b` lies in read-class `c` iff its local offset lies in class `locRes i k c b`, and
`locRes_mod` says `locRes` depends on `b` only through `b % k`.  Since `kk i = 40000 + i` is **odd
for odd `i`**, the needed local class genuinely alternates with `b`.  So what must be bounded is

    `∑_{b < a} N_b(locRes i k c b)`,   `N_b(r) := #{q ≡ r (mod k) : v occurs in window b at q}`.

The certificate controls, for each **fixed** `r`, the sum `∑_{b<a} N_b(r)` — it is an average over
the band, not a per-window statement.  To split off `{b : b ≡ e (mod k)}` one needs that family to
be a restriction the entropy machinery can price.  It is neither:

* **not a sample-time set.**  `winStartsW i` is the image of `bandW i ×ˢ Atoms` under
  `(n, α) ↦ 2·kIdx (gridAt i) n α = 2(n − t_α)/d_α`, and `fnthW i b` is the `b`-th element **in
  sorted order**.  The multipliers `d_α` differ (all within `1 ± 1/K` of `dRef`), so for a fixed
  `n` the `|A|` atom starts are spread over a position range of relative width `1/K`, inside which
  `≈ |bandW|·|A|/K` starts of *other* sample times interleave.  Rank parity is therefore not a
  function of `n`.  (The flank sandwich `cutLo`/`cutHi` only brackets rank-prefixes by sample-time
  prefixes to within `1 + 16/K` — plenty for prefixes, useless for parity.)
* **not a coordinate set.**  A coordinate restriction to `B ⊆ A` costs `δ|A|/|B|`, which is fine
  for `|B| ≥ |A|/k` — but rank parity is not a function of `α` either, and the per-`α` fix
  (restrict to coordinate `{α}` and the sample set `S_α = {n : b(n,α) ≡ e}`) costs `δ|A|` per
  coordinate.  `Fintype.card (gridAt i).Atom ≤ (K²+1)^K`, so that is fatal.

Three exact statements of the gap, all checked against the four decompositions tried:

1. `∑_c (restricted count at read-class c) = (unrestricted count)` is certified, and so is
   `∑_{b<a} N_b(r)` for each fixed `r`.  For `k = 2` that is **2 equations in 4 unknowns**
   (`[c₀, b even]`, `[c₀, b odd]`, `[c₀+1, b even]`, `[c₀+1, b odd]`); the read-class count is a
   combination the two equations do not determine.
2. The "rotate the class assignment" family `S_j := ∑_b N_b(locRes(b + j))` sums over `j` to the
   unrestricted count and gives nothing more.
3. Writing the gap as `Δ = ∑_{p} (−1)^p · 1[v at read position p]` and bounding it by
   `√(a · ∑_b D_b²)` (which would suffice, since `kk i · 2^{−ℓ} → ∞`) needs the pair-correlation
   counts `C_t` for all `t ≤ kk i`; the capture bound costs `B(t+ℓ)` per `t` and the alternating
   sum over `t` accumulates `kk i · B̄ ≫ 1`.  Refuted.

**Conclusion.**  The offset-class route reaches every *fixed* local class of every band, which is
exactly base-`2^k` normality of a read whose window length were divisible by `k`.  It cannot reach
`IsNormal 4 fullRealW`, because `fullPosW`'s window length `kk i` is odd for odd `i` and the
compensating index is the sorted **rank**, which the certificate cannot see.  Nothing in the
lap-126-close directive survives this.

## The successor route, and why it is better

`IsNormal 4 fullRealW` is **true** — it follows from the proved `IsNormal 2 fullRealW` by the
classical theorem *normal to base `b` ⟺ normal to base `b^K`* (Maxfield).  The directive forbade
"Wall + Maxfield", and rightly: the u.d./Fourier route gives only
`∑_{j<K} S_N(h b^j) = o(N)` — the sum over classes again, the *same* obstruction.

But there is an **elementary, self-contained** proof that avoids both Wall and Fourier, and it is
now in kernel as `NormalNumbers/BlockRigidity.lean`:

> **Block rigidity** (`Sys.eq_uniform`, axiom-clean).  Let `F m k ≥ 0` be attached to the base-`b`
> word of length `m` and value `k < b^m`, with
> * `F 0 0 = 1`;
> * `F m k = ∑_{s<b} F (m+1) (k·b + s)`               (refine on the right);
> * `F m k = ∑_{t<b^K} F (m+K) (t·b^m + k)`            (`K` prepends close up, mod `K`);
> * `F m k ≤ C·b^{−m}`.
>
> Then `F m k = b^{−m}`.

Proof (all finite sums): the energy `A m = ∑_k b^m (F m k)²` has increments
`Var m = A (m+1) − A m ≥ 0` (Cauchy–Schwarz on the refinement), is bounded by `C`, and the shift
relation makes `Var m ≤ Var (m+K)` (Cauchy–Schwarz again).  A summable sequence that is
nondecreasing along each class mod `K` is identically `0`; hence `A m = A 0 = 1`, and equality in
Cauchy–Schwarz forces `F m k = b^{−m}`.  Measure-theoretically this is "a `σ^K`-invariant measure
`≪` Bernoulli must **be** Bernoulli", i.e. ergodicity of the Bernoulli shift — but with no measure,
no compactness and no ergodic theorem.

**How it applies.**  For a base-`b` normal sequence `d`, a nonprincipal ultrafilter `g ≤ atTop`,
and `F m k := lim_g (K/n)·#{p < n : p ≡ 0 (mod K), the length-`m` word of value `k` occurs at p}`:
the three relations are exact identities up to `O(1)/n`, and `bdd` holds with `C = K` because the
`K` classes together carry the unrestricted density `b^{−m}`.  So `F m k = b^{−m}` for **every**
ultrafilter, hence (`tendsto_iff_ultrafilter`) the density converges — which is precisely
`IsNormal (b^K)`.

Next: the ultrafilter/density layer (`BlockRigidity` → `IsNormal b y → IsNormal (b^K) y`), then
`IsNormal 4 fullRealW` and `IsNormal (2^k) fullRealW` as corollaries of `isNormal_fullRealW`.
This is strictly more than the directive's 🎯 (it holds for every base and every normal number),
and it leaves `fullRealW`, `fullPosW`, `fullDigW` and `G4EntropyWStatement` untouched.
