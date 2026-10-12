# (iii-b) driver: per panel pair, real good parents in the pair's closed bins (random good walk to level n-K, then
# all 2^K completions filtered by bins/state/goodness), exact block value vs target.  Caps: CAP parents, TCAP seconds.
exec(open('realpar.py').read())
import pickle, time, sys, random
from multiprocessing import Pool
W3 = [int(l) for l in open('../W181.txt')]; PHI = [int(l) for l in open(sys.argv[1])]
EX = {}
for l in open(sys.argv[2]):
    q5, r3, e = map(int, l.split()); EX[(q5, r3)] = e
lv = pickle.load(open('levels.pkl', 'rb'))
K, CAP, TCAP, NLEV = 16, int(sys.argv[4]), float(sys.argv[5]), 3
def walk(n, rng):
    st = [(0, 0, 0)]  # (a, state, level) DFS with random child order
    ms = {3: 0, 5: 0}
    path = [(0, 0)]; a, s = 0, 0; l = 0; tries = 0
    while l < n:
        bits = [0, 1]; rng.shuffle(bits); ok = False
        for bit in bits:
            a2, s2 = 2 * a + bit, T[s][bit]
            if s2 < 0: continue
            g = True
            for b in (3, 5):
                m, _ = scale(b, l + 1); D = dfl(b, l + 1); one = 1 << (l + 1)
                mprev, _ = scale(b, l)
                for mp in range(mprev, m):
                    p = b ** mp; L = p * a2; H = L + p; A0 = L >> (l + 1)
                    if any(H + D >= A * one and L <= A * one + D for A in (A0, A0 + 1)): g = False; break
                if not g: break
            if g: a, s, l, ok = a2, s2, l + 1, True; break
        if not ok:
            tries += 1
            if tries > 50: return None
            back = rng.randrange(1, 20); a >>= back; l = max(0, l - back); s = sft_state(a, l)  # crude backtrack
    return a, s
def task(args):
    kind, q3, q5 = args
    rng = random.Random(q3 * 100003 + q5); t0 = time.time()
    s = q3 // NB3; r3, r5 = q3 % NB3, q5 % NB5
    tgt = W3[q3] * PHI[q5]; e = EX.get((q5, r3))
    if e is not None and e < tgt: tgt = e
    res = []; levels = lv[(q3, q5)][:NLEV]; walks = 0
    if not levels or tgt <= 0: return (kind, q3, q5, tgt, res, walks, time.time() - t0)
    i3, i5 = r3 // M3, r5 // M5
    while len(res) < CAP and time.time() - t0 < TCAP:
        n = rng.choice(levels); w = walk(n - K, rng); walks += 1
        if not w: continue
        a0, s0 = w
        m3, p3 = scale(3, n); m5, p5 = scale(5, n)
        c3 = ((p3 * (a0 << K)) % (1 << n)) / 2.0 ** n if n < 1000 else (((p3 * (a0 << K)) % (1 << n)) >> (n - 60)) / 2.0 ** 60
        c5 = ((p5 * (a0 << K)) % (1 << n)) / 2.0 ** n if n < 1000 else (((p5 * (a0 << K)) % (1 << n)) >> (n - 60)) / 2.0 ** 60
        d3 = p3 / 2.0 ** n if n < 1000 else (p3 >> (n - 60)) / 2.0 ** 60; d5 = p5 / 2.0 ** n if n < 1000 else (p5 >> (n - 60)) / 2.0 ** 60
        x5lo, x5hi = X5[i5] / 2.0 ** 90, X5[i5 + 1] / 2.0 ** 90
        for j in range(1 << K):
            x3 = (c3 + j * d3) % 1.0
            if not (i3 / 128 - 1e-9 <= x3 <= (i3 + 1) / 128 + 1e-9): continue
            x5 = (c5 + j * d5) % 1.0
            if not (x5lo - 1e-9 <= x5 <= x5hi + 1e-9): continue
            a = (a0 << K) + j
            st = s0
            for i in range(K - 1, -1, -1):
                st = T[st][(j >> i) & 1]
                if st < 0: break
            if st != s: continue
            b3s, b5s, sg = binsets(n, a)
            if r3 not in b3s or r5 not in b5s: continue
            if not good(n, a): continue
            lo, hi = block_value(n, a, s, W3, PHI, EX)
            res.append((n, a, lo, hi, len(b3s) * len(b5s)))
            if len(res) >= CAP: break
    return (kind, q3, q5, tgt, res, walks, time.time() - t0)
if __name__ == '__main__':
    P = [tuple([l.split()[0]] + list(map(int, l.split()[1:]))) for l in open('panel.txt') if l[0] != '#']
    with Pool(int(sys.argv[6])) as pool:
        out = pool.map(task, P, chunksize=1)
    pickle.dump(out, open(sys.argv[3], 'wb'))
    N, D = 9**6, 5**6
    for kind, q3, q5, tgt, res, walks, tt in out:
        nf = sum(1 for r in res if D * r[3] < N * tgt)   # upper value below target: genuine witness
        mn = min((D * r[2] / (N * tgt) for r in res), default=None)
        print(kind, q3, q5, 'parents', len(res), 'genuine', nf, 'minratio', None if mn is None else round(mn, 6), 'walks', walks, 'time %.0f' % tt)
