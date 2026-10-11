# gate-6 tail re-screen with a core's OWN f (run sums) and e' (layer-cake), from sharedF.js CELLS output.
# usage: tail_kf.py g F kf.json [BMAX GRID]
import sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '..')
import tail5_refined as R
g = Fr(sys.argv[1]); F = set(map(int, sys.argv[2].split(','))) if sys.argv[2] else set()
d = json.load(open(sys.argv[3]))
bmax, grid = (sys.argv[4], sys.argv[5]) if len(sys.argv) > 5 else ('300', '50')
R.G = g ** 6
orig = R.is_pp
R.is_pp = lambda b: orig(b) or b in F
R.load_f = lambda: [Fr(x).limit_denominator(10**9) for x in d['f']]
R.load_e = lambda: {Fr(b).limit_denominator(1000): Fr(x).limit_denominator(10**9) for b, x in zip(d['betas'], d['e'])}
sys.argv = ['x', bmax, grid, 'i,ii,iii']
R.main()
