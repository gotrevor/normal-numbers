# Prime-density dimension: active attended override

Trevor authorized continuing real mathematics in the main worktree on 2026-09-21.
This scoped directive supersedes old DIRECTION campaigns.  One Opus/low lap;
stop after this target, never fall back to an older campaign.

## Mathematical deliverable

Create `src/NormalNumbers/PrimeModelPrimeDimension.lean`, importing
PrimeModelBrunLower and PrimeModelRadicalMoment.  Prove `prime_density_dimension`:
for natural h>=1, natural y>=2, any finite set U of primes p with h<p and p<=y,

    Brun.Dimension U (fun p => (h:Real)/p) y
      ((4:Real)^h * Real.exp (16*(h:Real))) (24*h).

No dimension, interval prime-sum, Mertens, or equivalent analytic estimate may
be left as a hypothesis.  Reuse `Radical.mertens_crude`, already proved.
All existing theorem statements and `Brun.Dimension` are frozen.  If the exact
claim is false, give a concrete obstruction; do not silently weaken it.

Then prove `prime_density_brun_lower`: instantiate `brun_lower_fundamental`
with these constants and g(p)=h/p, retaining only the elementary hypotheses
on U,h,y,s (exp 2<=y; s>=80*(24*h); s>=40*log(4^h*exp(16*h))+4).
Its conclusion must include all three original weight properties, not merely
an existential wrapper conditional on the estimate we are here to prove.

## Route already assessed

Read papers/prime-model-sieve-assessment.md, especially dimension-input review.
For 2<=w<=y, partition into log-dyadic intervals (v,v^2], each reciprocal
prime mass <=8 by mertens_crude.  At most ceil(log(log y/log w)/log 2)
blocks give sum 1/p <=8+12*log(log y/log w).  Handle w=y separately.
Small primes h<p<=2h: inverse product p/(p-h) <=4^h via the whole integer
interval product (2h choose h).  Large primes p>2h: -log(1-h/p)<=2h/p.
Combine: K=4^h*exp(16h), dimension=24h.  For t<2 use w=2; prime2 is
in the small part if present.  Subsets decrease the positive bounds.
An equivalent direct partial-summation proof is fine if simpler.
No new dependencies or pin changes.  A source in the universe cache is not
necessarily a declared built dependency.

## Scope and completion

Only the new module, its root import, this kickoff and a dated handoff are
worker-owned.  Do not edit G4 files or other existing proof modules.  Commit
a compiling skeleton early, then meaningful proof advances.  Success is the
prime-density input discharged, not a sorry tally or a fresh conditional node.
Run the module and full builds, record the exact theorem assumptions and any
remaining application work.  Add concrete small-prime controls in Lean.
Use box done --green only after both named targets are proved; then stop.
