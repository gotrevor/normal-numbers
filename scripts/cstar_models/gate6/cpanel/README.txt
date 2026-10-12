Gate 6 causal panel (2026-10-12).  Run from tmp/ (inputs: tmp/W181.txt, tmp/costlap/ZX.rec = pass-0 slice E records,
tmp/costlap/U/{phi,ex}.0.txt = post-update snapshot, tmp/costlap/T2/pass1 = post-update records on q3 % 5000 < 15).
frac.py   step 1: failure fractions on identical parent IDs (output frac_out.txt).
panel.py  step 2: the panel, fixed before any evaluation (panel.txt, md5 recorded in the commit).
cpanel.c   exact5b0 + PANEL/POINTS/EDGES modes; per-pair node/time caps (PNODECAP, PTIME), depth-cap counter,
           tight variants: UNION (met-set union on ambiguity), WORLDS (one vector per consistent ambiguity world),
           RSPLIT=1/2/3 (x:r bisection 1:1, 1:2, 2:1).  Build: leanc -O2 cpanel.c -lm -lpthread.
realpar.py independent exact real-cell semantics (true delta, closed windows, closed bins); controls: level-12 good
           cells 2554/4096 (= rootCheck), xcheck.py: Python block value == C point evaluator on 120 real cells (n 18-84).
find.py    real good parents in each pair's bins (random good walk + 2^16 completions), exact value vs target.
probes.py  2^-82-box point probes, uniform in the pair box and in the tight evaluator's terminal failing sub-box.
classify.py -> classify.txt (the table).
