import sys, random; sys.path.insert(0,'experiments')
from mahler_exact_M import channel_graph, prod_graph, nontrivial_scc_trim
g,k,M=7,2,175; W=(0,0)
n1,e1=channel_graph(g,k,1,W)
nodes=[(w,(c,)) for (w,c) in n1]
edges={(w,(c,)):[(l,(t[0],(t[1],))) for (l,t) in e1[(w,c)]] for (w,c) in n1}
nodes,edges=nontrivial_scc_trim(nodes,edges)
for m in range(2,M+1):
    nodes,edges=prod_graph((nodes,edges),channel_graph(g,k,m,W)); nodes,edges=nontrivial_scc_trim(nodes,edges)
# enumerate simple cycles (small graph)
idx={v:i for i,v in enumerate(nodes)}
cycles=set()
def dfs(start,v,path,labels,seen):
    for (l,w) in edges[v]:
        if w==start: cycles.add(tuple(labels+[l]))
        elif w not in seen and idx[w]>idx[start]:
            dfs(start,w,path+[w],labels+[l],seen|{w})
for s in nodes: dfs(s,s,[s],[],{s})
cyc=sorted(cycles,key=len)
print("cycles (lsd-first labels):",[ ''.join(map(str,c)) for c in cyc])
# Build alpha digits msd-first from a long random walk (walk goes lsd->msd), then reverse
random.seed(7); v=nodes[0]; seq=[]
for _ in range(3000):
    l,w=random.choice(edges[v]); seq.append(l); v=w
dig=seq[::-1]  # msd first
L=len(dig)
val=0
for d in dig: val=val*g+d
# alpha ~ val/g^L ; m*alpha digits = digits of m*val (padded to L), ignore last 6
bad=[]
for m in range(1,M+1):
    X=m*val; s=[]
    for _ in range(L): s.append(X%g); X//=g
    s=s[::-1][:L-6]
    if any(s[i]==0 and s[i+1]==0 for i in range(len(s)-1)): bad.append(m)
print("channels with 00 in mixed walk:",bad[:10], "count",len(bad))
print(''.join(map(str,dig[:120])))
