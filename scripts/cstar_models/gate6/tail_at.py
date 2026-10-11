# gate-6 tail re-screen: tail5_refined with G = g^6 and bases in F excluded (Ren's design recipe).
# usage: tail_at.py g F(comma) [BMAX GRID]
import sys
from fractions import Fraction as Fr
sys.path.insert(0, '..'); sys.path.insert(0, '.')
import tail5_refined as R
g = Fr(sys.argv[1]); F = set(map(int, sys.argv[2].split(','))) if sys.argv[2] else set()
bmax, grid = (sys.argv[3], sys.argv[4]) if len(sys.argv) > 4 else ('300', '100')
R.G = g ** 6
orig = R.is_pp
R.is_pp = lambda b: orig(b) or b in F
sys.argv = ['x', bmax, grid, 'i,ii,iii']
R.main()
