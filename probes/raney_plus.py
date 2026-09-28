exec(open('probes/raney_reach.py').read().split("for D in [2,3,5,7,11,13,4,6,9]")[0])
def iota(M):
    a,b,c,d = M
    return (c,d,a,b)
def delta(M,j): return reduce(mul(M,Bm(j)))[0]
def dbar(M,j):  return iota(delta(M,j))

def study(D, JMAX=200):
    S = states(D)
    P = [M for M in S if det(M)==D]
    z = (1,0,0,D)
    ok1 = {}
    for M in P:
        wit=[]
        for j1 in range(1,JMAX+1):
            M1 = dbar(M,j1)
            for j2 in range(1,JMAX+1):
                if dbar(M1,j2)==z:
                    wit.append((j1,j2)); break
            if wit: break
        ok1[M]=wit[0] if wit else None
    miss=[M for M in P if ok1[M] is None]
    # what does one big digit give?
    onestep = {}
    for M in P:
        onestep[M] = [dbar(M,j) for j in (D, D+1, 2*D, 2*D+1, 3*D+1, 5*D+3)]
    print(f"D={D}: |P|={len(P)}  target z={z}  unreached={len(miss)}")
    if miss: print("   missing:", miss[:5])
    else:
        mx=max(max(w) for w in ok1.values())
        print(f"   max digit used: {mx}; sample witnesses:", list(ok1.items())[:4])
    # is dbar(M, j) for large j always of the form (1,r,0,D) or ...?
    forms=set()
    for M in P:
        for j in range(3*D+1, 3*D+8):
            forms.add(tuple(1 if x>0 else 0 for x in dbar(M,j)))
    print("   large-digit image shapes:", sorted(forms))
for D in [2,3,5,7,11,13]:
    study(D)
