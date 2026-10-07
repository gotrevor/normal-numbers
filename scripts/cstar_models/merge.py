import sys,bisect
from thick import windows,gaps,thickness
def merge(G,tau,minsize):
    G=[list(g) for g in G]
    changed=True; it=0
    while changed:
        changed=False; it+=1
        hl=G[0][1]; hr=G[-1][0]
        n=len(G); sizes=[g[1]-g[0] for g in G]
        # nearest gap of size>=s to left/right: monotone stack
        left=[None]*n; st=[]
        for i in range(n):
            while st and sizes[st[-1]]<sizes[i]: st.pop()
            left[i]=st[-1] if st else None; st.append(i)
        right=[None]*n; st=[]
        for i in range(n-1,-1,-1):
            while st and sizes[st[-1]]<sizes[i]: st.pop()
            right[i]=st[-1] if st else None; st.append(i)
        kill=set(); newG=[]
        # merge violators greedily, largest-first
        order=sorted(range(1,n-1),key=lambda i:-sizes[i])
        mark=[None]*n
        for i in order:
            if sizes[i]<minsize: break
            s=sizes[i]
            for j in (left[i],right[i]):
                if j is None: continue
                br = G[i][0]-G[j][1] if j<i else G[j][0]-G[i][1]
                if br< tau*s:
                    a,b=min(i,j),max(i,j)
                    G[a]=[G[a][0],max(G[b][1],G[a][1])]
                    for k in range(a+1,b+1): G[k]=None
                    changed=True; break
            if changed: break
        G=[g for g in G if g is not None]
        # coalesce
    return G,it
if __name__=='__main__':
    c=float(sys.argv[1]); smin=float(sys.argv[2]); tau=float(sys.argv[3]); bases=[int(x) for x in sys.argv[4:]]
    G=gaps(windows(bases,c,smin))
    G2,it=merge(G,tau,smin*8)
    meas=1-sum(g[1]-g[0] for g in G2 if g[1]>0 and g[0]<1)
    print('iters',it,'hull',G2[0][1],G2[-1][0],'gaps',len(G2),'thick',thickness(G2,smin*8)[0][0])
