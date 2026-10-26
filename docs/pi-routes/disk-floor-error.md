# The disk tail-floor size bound is already available

The old route-3 handoff proposed a structured bound on
\(\sum_{d>D}\chi_4(d)\{16^n/d\}\) modulo \(8^n\) as a way to reopen the route.  A **size bound that vanishes after this scaling** is already a consequence of the route's perimeter estimate and two elementary classical arithmetic inputs.  It does not supply digit visits.

The new declarations are in `src/NormalNumbers/PiDisjunctiveRoutes/DiskFloorError.lean`, namespace `NormalNumbers.PiDisjunctiveRoutes.DiskFloorError`.

Let \(X=16^n\), \(R=4^n\), and

\[
L_D=\sum_{1\le d\le D}\frac{\chi_4(d)}d,
\qquad
E_n(D)=\sum_{1\le d\le D}\chi_4(d)\left(\frac Xd-\left\lfloor\frac Xd\right\rfloor\right).
\]

`floorError_eq` identifies the latter sum with the Lean definition `floorError n D`.  `floorError_abs_le` proves \(|E_n(D)|\le D\).

The two explicit inputs are:

- `DiskDivisorIdentity`, the already-stated sum-of-two-squares divisor formula:
  \(\operatorname{diskCount}(R)=1+4\sum_{d\le R^2}\chi_4(d)\lfloor R^2/d\rfloor\).
- `LeibnizRemainderBound`, the alternating-series bound
  \(|L_D-\pi/4|\le1/(D+1)\).  This is recorded as a hypothesis `Prop`, not an axiom or a proved Lean theorem.  In this cutoff convention the next nonzero denominator is at least \(D+1\).

The existing geometric theorem gives
\(|\operatorname{diskCount}(R)-\pi R^2|\le5R\).  Consequently

\[
4E_n(X)=4X(L_X-\pi/4)
       +(\pi X-\operatorname{diskCount}(R))+1.
\]

The first term has absolute value at most 4.  Thus **`total_floorError_bound`** proves, from the two inputs,

\[
|E_n(X)|\le\frac{5R+5}{4}.
\]

Subtracting the first \(D\) terms and using \(D\le R\) gives the proved **`tail_floorError_scaled_bound`**:

\[
\boxed{\left|\frac4{8^n}\sum_{D<d\le16^n}
\chi_4(d)\left\{\frac{16^n}d\right\}\right|
\le\frac{14}{2^n}\qquad(D\le4^n).}
\]

This explicitly covers fixed cutoffs and growing cutoffs up to \(4^n\).  No assertion about every possible cutoff, or about correlations of these errors across different n, is made.

The exact-rational check in `scripts/pi_disk_floor_probe.py` verifies the identities and bounds for \(n=0,1,2,3\); its output is `disk-floor-probe.json`.  Hand-countable disks of radii 1, 2, and 4 are the known-answer control.  Replacing the character by the constant function 1 breaks the perimeter-scale bound at n=2 and n=3, so the observed cancellation is not a generic property of fractional parts.  These finite checks are separate from the conditional all-index Lean theorems.

## What remains

The tail floor errors can be discarded at the digit-shadow scale; the surviving harmonic main term still contains the pi orbit.  This is a correction to the proposed research target, **not a no-go theorem for all disk arithmetic**.  A useful reopening would need information that forces visits to real residue intervals, such as an additional relation across scales.  Merely sharpening the displayed size bound does not provide such a relation.  Pi disjunctivity remains unproved.
