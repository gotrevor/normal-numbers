"""Incremental trimmed product: exact M_W(g,k) = least M s.t. channels 1..M collapse for block W.
Graph for one channel m: states (window (k-1 digits), carry in [0,m)), edge on prepended digit x if the k-window of channel-m digits != W.
Product with trimming to nontrivial SCCs (|E|>|V|) after each channel.
"""
import sys
from itertools import product
sys.setrecursionlimit(1000000)

def chan_digits(m, xs, c, g):
    out=[]
    for x in reversed(xs):
        v=m*x+c; out.append(v%g); c=v//g
    return out[::-1]

def nontrivial_scc_trim(nodes, edges):
    # nodes: list of hashable; edges: dict node -> list of (label, node)
    idx={v:i for i,v in enumerate(nodes)}; n=len(nodes)
    adj=[[idx[w] for (_,w) in edges[v]] for v in nodes]
    # Tarjan iterative
    index=[None]*n; low=[0]*n; onst=[False]*n; st=[]; cnt=0; comp=[-1]*n; ncomp=0
    for root in range(n):
        if index[root] is not None: continue
        stack=[(root,iter(adj[root]))]; index[root]=low[root]=cnt; cnt+=1; st.append(root); onst[root]=True
        while stack:
            v,it=stack[-1]; adv=False
            for w in it:
                if index[w] is None:
                    index[w]=low[w]=cnt; cnt+=1; st.append(w); onst[w]=True; stack.append((w,iter(adj[w]))); adv=True; break
                elif onst[w]: low[v]=min(low[v],index[w])
            if adv: continue
            stack.pop()
            if stack: u=stack[-1][0]; low[u]=min(low[u],low[v])
            if low[v]==index[v]:
                while True:
                    w=st.pop(); onst[w]=False; comp[w]=ncomp
                    if w==v: break
                ncomp+=1
    sizes=[0]*ncomp; ecount=[0]*ncomp
    for v in range(n):
        sizes[comp[v]]+=1
        for w in adj[v]:
            if comp[w]==comp[v]: ecount[comp[v]]+=1
    keep=[c for c in range(ncomp) if ecount[c]>sizes[c]]
    keepset=set(keep)
    newnodes=[v for v in nodes if comp[idx[v]] in keepset]
    newedges={v:[(l,w) for (l,w) in edges[v] if comp[idx[w]]==comp[idx[v]]] for v in newnodes}
    return newnodes,newedges

def channel_graph(g,k,m,W):
    nodes=[]; edges={}
    for w in product(range(g),repeat=k-1):
        for c in range(m):
            nodes.append((w,c))
    for (w,c) in nodes:
        es=[]
        for x in range(g):
            xs=(x,)+w
            if tuple(chan_digits(m,list(xs),c,g))!=W:
                nw=xs[:k-1] if k>1 else ()
                es.append((x,(nw,(m*xs[-1]+c)//g)))
        edges[(w,c)]=es
    return nodes,edges

def prod_graph(A,B):
    # states (a,b) with same window; edges with same label
    an,ae=A; bn,be=B
    bidx={}
    for b in bn: bidx.setdefault(b[0],[]).append(b)
    nodes=[]; edges={}
    for a in an:
        for b in bidx.get(a[0],[]):
            nodes.append((a[0],a[1]+(b[1],)))  # merged: window, carry tuple + carry
    # need edges: map from (window, carries) -> list
    aeD={a:ae[a] for a in an}; beD={b:be[b] for b in bn}
    # represent A nodes as (window, carrytuple), B nodes as (window, c)
    for (w,cs) in nodes:
        a=(w,cs[:-1]); b=(w,cs[-1])
        bl={}
        for (l,t) in beD[b]: bl[l]=t
        es=[]
        for (l,t) in aeD[a]:
            if l in bl:
                es.append((l,(t[0],t[1]+(bl[l][1],))))
        edges[(w,cs)]=es
    return nodes,edges

def M_W(g,k,W,Mmax=None,verbose=False):
    W=tuple(W)
    # channel 1 as base with carry tuple
    n1,e1=channel_graph(g,k,1,W)
    nodes=[(w,(c,)) for (w,c) in n1]
    edges={(w,(c,)):[(l,(t[0],(t[1],))) for (l,t) in e1[(w,c)]] for (w,c) in n1}
    nodes,edges=nontrivial_scc_trim(nodes,edges)
    m=1
    while nodes:
        m+=1
        if Mmax and m>Mmax: return None, len(nodes)
        B=channel_graph(g,k,m,W)
        nodes,edges=prod_graph((nodes,edges),B)
        nodes,edges=nontrivial_scc_trim(nodes,edges)
        if verbose: print(f"   after channel {m}: {len(nodes)} live states", flush=True)
    return m, 0  # channels 1..m collapse; 1..m-1 escape

if __name__=="__main__":
    import time
    for g,k in [(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1),(7,1),(5,2),(8,1),(9,1),(10,1),(11,1),(13,1)]:
        t0=time.time(); best=0; arg=None
        for W in product(range(g),repeat=k):
            mw,_=M_W(g,k,W)
            if mw>best: best=mw; arg=W
        print(f"g={g} k={k}: M(g,k) = {best}  (block {arg})   g^k-1={g**k-1}  g^(k+1)={g**(k+1)}  [{time.time()-t0:.1f}s]", flush=True)
