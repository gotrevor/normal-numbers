#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Empirical null: is the adversarial KS actually elevated, or is it seed noise?

Six pairwise comparisons per run inflate the max, so the tabulated 5% two-sample
critical value is the wrong yardstick.  Build the null from the UNPERTURBED
schedule across seeds and compare the perturbed runs to that."""
import sys
sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent))
from adversarial import doeblin

SEEDS = [101, 202, 303, 404, 505]
rows = {}
for sch in ("none", "squares", "powers", "brutal"):
    vals = []
    for sd in SEEDS:
        w, c, _, n = doeblin(sch, 120, 130, sd)
        vals.append(w)
    rows[sch] = vals
    print(f"{sch:>9}: " + " ".join(f"{v:.4f}" for v in vals)
          + f"   mean {sum(vals)/len(vals):.4f}  max {max(vals):.4f}")

base = rows["none"]
bmean = sum(base) / len(base); bmax = max(base)
print(f"\nnull (schedule=none): mean {bmean:.4f}, max {bmax:.4f} over {len(SEEDS)} seeds")
for sch in ("squares", "powers", "brutal"):
    v = rows[sch]; m = sum(v) / len(v)
    over = sum(1 for x in v if x > bmax)
    print(f"  {sch:>8}: mean {m:.4f}  ({m - bmean:+.4f} vs null)   seeds above null-max: {over}/{len(SEEDS)}")
