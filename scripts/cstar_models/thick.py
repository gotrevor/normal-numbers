import math,sys
from fractions import Fraction as F
def windows(bases,c,smin):
    W=[]
    for b in bases:
        n=0
        while True:
            r=b**(-(n+c)) if isinstance(c,int) else b**(-(n+c))
            if 2*r<smin: break
            bn=b**n
            for A in range(0,bn+1):
                W.append((A/bn-r,A/bn+r))
            n+=1
    return W
def gaps(W,lo=0.0,hi=1.0):
    W.sort(); G=[]
    for a,b in W:
        if G and a<=G[-1][1]: G[-1][1]=max(G[-1][1],b)
        else: G.append([a,b])
    return G
def thickness(G,minsize):
    # hull = [end of first gap, start of last gap] (first/last gaps contain 0 and 1)
    hl=G[0][1]; hr=G[-1][0]; inner=[g for g in G[1:-1] if g[1]-g[0]>=minsize]
    # for each gap find nearest gap of size>= own on each side (or hull end)
    idx=sorted(range(len(inner)),key=lambda i:-(inner[i][1]-inner[i][0]))
    import bisect
    big=[] # sorted list of (left,right) of processed (larger) gaps
    worst=(1e9,None)
    lefts=[]
    for i in idx:
        g=inner[i]; s=g[1]-g[0]
        k=bisect.bisect(lefts,g[0])
        L=g[0]-(big[k-1][1] if k>0 else hl)
        R=(big[k][0] if k<len(big) else hr)-g[1]
        t=min(L,R)/s
        if t<worst[0]: worst=(t,g,s)
        big.insert(k,g); lefts.insert(k,g[0])
    return worst,(hl,hr),len(inner)
if __name__=='__main__':
    c=float(sys.argv[1]); smin=float(sys.argv[2]); bases=[int(x) for x in sys.argv[3:]]
    G=gaps(windows(bases,c,smin))
    print(thickness(G,smin*8))
