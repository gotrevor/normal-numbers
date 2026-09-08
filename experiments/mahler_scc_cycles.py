import sys; sys.path.insert(0,'experiments')
from mahler_exact_M import channel_graph, prod_graph, nontrivial_scc_trim
g,k,M=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); W=tuple(int(c) for c in sys.argv[4])
n1,e1=channel_graph(g,k,1,W)
nodes=[(w,(c,)) for (w,c) in n1]
edges={(w,(c,)):[(l,(t[0],(t[1],))) for (l,t) in e1[(w,c)]] for (w,c) in n1}
nodes,edges=nontrivial_scc_trim(nodes,edges)
for m in range(2,M+1):
    nodes,edges=prod_graph((nodes,edges),channel_graph(g,k,m,W)); nodes,edges=nontrivial_scc_trim(nodes,edges)
print("live states after channel",M,":",len(nodes))
# find a short cycle: BFS from each node to itself
import collections
best=None
for s in nodes[:200]:
    prev={s:None}; q=collections.deque([s]); found=None
    while q and not found:
        v=q.popleft()
        for (l,w) in edges[v]:
            if w==s: found=(v,l); break
            if w not in prev: prev[w]=(v,l); q.append(w)
    if found:
        path=[found[1]]; v=found[0]
        while v!=s: pv,l=prev[v]; path.append(l); v=pv
        path=path[::-1]
        if best is None or len(path)<len(best): best=path
print("cycle digits (prepended order, i.e. most significant last):",best, "len",len(best))
