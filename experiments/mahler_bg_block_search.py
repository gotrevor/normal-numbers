import sys
from itertools import product
g,k,Bmax=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
def rep(g,d): return (g**d-1)//(g-1)
def res(g,a,B,m,d): return ((m*a%(g-1))*rep(g,d)+m*B)%g**d
def avoid(g,k,a,B,m,d,W): 
    r=res(g,a,B,m,d); return (r+1)*g**k<=W*g**d or (W+1)*g**d<=r*g**k
def maxM(g,k,a,B,W,cap):
    # find largest M such that all m<=M satisfy: hback and avoid for all d in 1..D+k where D = stab threshold
    M=0
    while M<cap:
        m=M+1; b=m*a%(g-1)
        if b*rep(g,k)==W: break
        # stabilization threshold for this m
        D=1
        while b*rep(g,D)+m*B>=g**D: D+=1
        if not all(avoid(g,k,a,B,m,d,W) for d in range(1,D+k+1)): break
        M=m
    return M
best=(0,)
for a in range(0,g-1):
  for B in range(1,Bmax+1):
    for Wt in product(range(g),repeat=k):
        W=sum(w*g**(k-1-i) for i,w in enumerate(Wt))
        M=maxM(g,k,a,B,W,2*g**(k+1))
        if M>best[0]: best=(M,a,B,Wt,W); print(best,flush=True)
print("BEST",best)
