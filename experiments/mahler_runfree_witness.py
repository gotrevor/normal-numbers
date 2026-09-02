from mahler_exact_M import *
from itertools import product
import sys
def live_graph(g,k,W,M):
    W=tuple(W)
    n1,e1=channel_graph(g,k,1,W)
    nodes=[(w,(c,)) for (w,c) in n1]
    edges={(w,(c,)):[(l,(t[0],(t[1],))) for (l,t) in e1[(w,c)]] for (w,c) in n1}
    nodes,edges=nontrivial_scc_trim(nodes,edges)
    for m in range(2,M+1):
        B=channel_graph(g,k,m,W)
        nodes,edges=prod_graph((nodes,edges),B)
        nodes,edges=nontrivial_scc_trim(nodes,edges)
    return nodes,edges
for g,W,M in [(5,(1,),5),(7,(1,),8),(11,(2,),24),(13,(0,),34),(17,(4,),63),(17,(0,),62),(23,(0,),119)]:
    nodes,edges=live_graph(g,1,W,M)
    labs=sorted(set(l for v in nodes for (l,_) in edges[v]))
    # digit transition structure: which digit pairs (prepended x, then rightmost...) -- print allowed 2-windows via a sample path
    # sample a long backward path: follow edges greedily with variety
    import random
    random.seed(1)
    v=nodes[0]; seq=[]
    for _ in range(60):
        es=edges[v]
        l,t=random.choice(es); seq.append(l); v=t
    print(f"g={g} W={W} channels 1..{M}: live states {len(nodes)}, digits used {labs}")
    print("   sample word (right-to-left prepend order, so reverse = left-to-right):", list(reversed(seq)))
