exec(open('realpar.py').read())
import random, subprocess
W3 = [int(l) for l in open('../W181.txt')]; PHI = [int(l) for l in open('phi_after.txt')]
EX = {}
for l in open('ex_after.txt'):
    q5, r3, e = map(int, l.split()); EX[(q5, r3)] = e
rng = random.Random(1); pts = []; py = []
for n in (18, 24, 30, 36, 48, 60, 72, 84):
    k = 0
    while k < 15:
        a = rng.randrange(1 << n); s = sft_state(a, n)
        if s < 0 or not good(n, a): continue
        b3s, b5s, (m3, m5, X3, X5_, p3, p5) = binsets(n, a)
        if len(b3s) != 1 or len(b5s) != 1: continue
        q3, q5 = s * NB3 + b3s[0], s * NB5 + b5s[0]
        if W3[q3] * PHI[q5] == 0: continue
        lo, hi = block_value(n, a, s, W3, PHI, EX)
        pts.append(f"{q3} {q5} {X3 << (90 - n)} {p3 << (90 - n)} {X5_ << (90 - n)} {p5 << (90 - n)}\n"); py.append((n, lo, hi)); k += 1
open('xc_pts.txt', 'w').writelines(pts)
out = subprocess.run("WORLDS=1 MAXB5=20 POINTS=xc_pts.txt bin/cpanel 128 24 6 0 6 16 ../W181.txt check phi_after.txt 1 ex_after.txt | grep POINT", shell=True, capture_output=True, text=True).stdout.split('\n')
agree = 0; bad = []
for (n, lo, hi), l in zip(py, out):
    v = int(l.split()[4])  # C prints v*DEN/NUM
    vc = v  # compare raw sums: convert python sum to same scale
    vp = lo * 5**6 // 9**6
    if abs(vp - vc) <= 1: agree += 1
    else: bad.append((n, lo, hi, l))
print('agree', agree, 'of', len(py)); [print(b) for b in bad[:5]]
