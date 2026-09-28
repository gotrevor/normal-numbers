exec(open('probes/raney_reach.py').read().split("for D in [2,3,5,7,11,13,4,6,9]")[0])

def iota(M):           # J*M : swap rows
    a,b,c,d = M
    return (c,d,a,b)

def quot(M):           # canonical representative of {M, iota M}
    return min(M, iota(M))

def study(D, JMAX=80, LMAX=12):
    S = states(D)
    # check iota preserves S and commutes with delta
    okS = all(iota(M) in S for M in S)
    trans = {}
    for M in S:
        for j in range(1, JMAX+1):
            trans[(M,j)] = reduce(mul(M,Bm(j)))[0]
    okC = all(trans[(iota(M),j)] == iota(trans[(M,j)]) for M in S for j in range(1,JMAX+1))
    # emitted word swap?
    def swap(w): return ['R' if x=='L' else 'L' for x in w]
    okW = all(reduce(mul(iota(M),Bm(j)))[1] == swap(reduce(mul(M,Bm(j)))[1])
              for M in S for j in range(1,JMAX+1))
    Q = sorted(set(quot(M) for M in S))
    qtrans = {}
    for P in Q:
        for j in range(1,JMAX+1):
            qtrans[(P,j)] = quot(trans[(P,j)])
    qsucc = {P:set(qtrans[(P,j)] for j in range(1,JMAX+1)) for P in Q}
    best=[]
    for z in Q:
        R={z}
        for l in range(1,LMAX+1):
            R = {P for P in Q if qsucc[P] & R}
            if len(R)==len(Q):
                best.append((z,l)); break
    print(f"D={D}: |S|={len(S)} |S/i|={len(Q)}  iota-closed={okS} commutes={okC} out-swaps={okW}")
    if best:
        m=min(l for _,l in best)
        zs=[z for z,l in best if l==m]
        print(f"    minimal uniform common-reach length = {m}; #targets at that length = {len(zs)}; e.g. {zs[:3]}")
    else:
        print("    NO uniform common reach within LMAX")

for D in [2,3,5,7,11,13,17,19,23]:
    study(D)
