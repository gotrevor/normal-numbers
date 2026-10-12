import glob, sys
from collections import Counter
rec={}
for f in glob.glob('../costlap/T2/pass1/u*.txt'):
    for l in open(f).read().split('\n')[2:]:
        p=l.split()
        if len(p)==4: rec[(int(p[0]),int(p[1]))]=int(p[2])
def load(fn):
    D={}
    for l in open(fn):
        x=l.split(); d=dict(zip(x[4::2],x[5::2])); D[(x[1],int(x[2]),int(x[3]))]=dict(st=x[8],ratio=float(x[7]),v=int(x[10]),dc=int(x[x.index('depthcap')+1]),cap=int(x[-1]),t=float(x[x.index('time')+1]),nodes=int(x[x.index('nodes')+1]))
    return D
for fn in sys.argv[1:]:
    D=load(fn)
    print(fn, Counter((k[0],d['st']) for k,d in D.items()), 'depthcap>0', Counter(k[0] for k,d in D.items() if d['dc']>0), 'cap', sum(d['cap'] for d in D.values()), 'maxtime %.1f'%max(d['t'] for d in D.values()), 'maxnodes', max(d['nodes'] for d in D.values()))
    if 'after' in fn and 'ord' in fn: print('record match', sum(1 for k,d in D.items() if k[0]=='F' and rec.get(k[1:])==d['v']))
