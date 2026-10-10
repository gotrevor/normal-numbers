import random
from fractions import Fraction as F
def rank(M):
    M=[r[:] for r in M]; rk=0; cols=len(M[0]) if M else 0
    for c in range(cols):
        p=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]/M[rk][c]; M[i]=[x-f*y for x,y in zip(M[i],M[rk])]
        rk+=1
    return rk
def test(a1,a2,b1,b2,K,L,R1,R2,S1,S2):
    G1={a1**r*a2**s for r in range(R1) for s in range(S1)}
    G2={r*b2+s*b1 for r in range(R2) for s in range(S2)}
    if not (L<=len(G1) and (K-1)*L<len(G2)): return None
    rows=[[F(r*b2+s*b1)**k*(a1**r*a2**s)**l for l in range(L) for k in range(K)]
          for r in range(R1+R2-1) for s in range(S1+S2-1)]
    return rank(rows)==K*L
random.seed(1); bad=0;n=0
pairs=[(F(2),F(3)),(F(1,2),F(5,3)),(F(-2),F(3)),(F(2,3),F(7)),(F(4),F(9,2))]
for _ in range(3000):
    a1,a2=random.choice(pairs)
    b1=random.randint(-3,3); b2=random.randint(-3,3)
    K=random.randint(1,4);L=random.randint(1,4)
    R1,R2,S1,S2=[random.randint(1,4) for _ in range(4)]
    r=test(a1,a2,b1,b2,K,L,R1,R2,S1,S2)
    if r is None: continue
    n+=1
    if not r: bad+=1; print("COUNTER",a1,a2,b1,b2,K,L,R1,R2,S1,S2)
print(n,bad)
