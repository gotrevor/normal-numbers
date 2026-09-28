"""Probe Vandehey 2017 Lemma 2.1's descent: does reduce(J .) terminate in M_D?

State N = [[a,b],[c,d]].  Step: e = min(floor(a/c), floor(b/d)) (inf when the
denominator is 0), N <- A_e^{-1} N = [[a-ec, b-ed],[c,d]], then N <- J N.
Start from M * B j for M in M_D.
"""
INF = float('inf')

def isMD(D, M):
    a, b, c, d = M
    if a*d - b*c not in (D, -D):
        return False
    return (
        (c == 0 and b >= 0 and a > 0 and d > 0 and b < d) or
        (d == 0 and a >= 0 and b > 0 and c > 0 and a < c) or
        (a == 0 and d >= 0 and b > 0 and c > 0 and d < b) or
        (b == 0 and c >= 0 and a > 0 and d > 0 and c < a) or
        (a < 0 and b > 0 and c > 0 and d > 0 and abs(a) < c) or
        (b < 0 and a > 0 and c > 0 and d > 0 and abs(b) < d))

def mdset(D):
    out = []
    for a in range(-D, D+1):
        for b in range(-D, D+1):
            for c in range(-D, D+1):
                for dd in range(-D, D+1):
                    if isMD(D, (a, b, c, dd)):
                        out.append((a, b, cc := c, dd))
    return out

def fl(x, y):
    if y == 0:
        return INF
    return x // y

def step(N):
    a, b, c, d = N
    e = min(fl(a, c), fl(b, d))
    if e == INF:
        return None, None
    a, b = a - e*c, b - e*d
    return (c, d, a, b), e   # apply J after reduce

def run(D, M, j, cap=200):
    # M * B j,  B j = [[0,1],[1,j]]
    a, b, c, d = M
    N = (b, a + b*j, d, c + d*j)
    seen = []
    # first: reduce only (d0), no J yet -- but we fold it in: check MD after each reduce
    a, b, c, d = N
    e = min(fl(a, c), fl(b, d))
    if e == INF:
        return ('infden', N)
    d0 = e
    N = (a - e*c, b - e*d, c, d)
    for i in range(cap):
        if isMD(D, N):
            return ('ok', i)
        if N in seen:
            return ('loop', N, seen)
        seen.append(N)
        a, b, c, d = N
        N2 = (c, d, a, b)  # J N
        a, b, c, d = N2
        e = min(fl(a, c), fl(b, d))
        if e == INF:
            return ('infden2', N2)
        N = (a - e*c, b - e*d, c, d)
    return ('cap', N)

if __name__ == '__main__':
    import collections
    bad = collections.Counter()
    examples = {}
    for D in range(1, 9):
        S = mdset(D)
        for M in S:
            for j in range(0, 10):
                r = run(D, M, j)
                if r[0] != 'ok':
                    bad[(D, r[0])] += 1
                    examples.setdefault((D, r[0]), (M, j, r))
        print(f'D={D}: |M_D|={len(S)}  failures so far {sum(bad.values())}')
    print(bad)
    for k, v in list(examples.items())[:6]:
        print(k, v)
