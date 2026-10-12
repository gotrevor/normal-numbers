# Step (4)-(5): classify the 40 newly failing pairs.  (ii) = sound tight evaluators (WORLDS + RSPLIT 1/2/3, MAXB 28/32,
# 60 s cap); LOOSE if any passes.  GENUINE if a concrete real good parent has exact (upper) value below target.
import re
def st(fn):
    return {(l.split()[2], l.split()[3]): (l.split()[8], float(l.split()[7])) for l in open(fn) if l.startswith('PAIR')}
V = {k: st(f) for k, f in (('R1', 'tWR28_1.txt'), ('R2', 'tWR28_2.txt'), ('R3', 'tWR28_3.txt'))}
O = st('ord_after_full.txt')
real = {(l.split()[1], l.split()[2]): l.split() for l in open('real_after.txt') if l[0] in 'FC'}
pr = {}
for l in open('pr.txt'):
    x = l.split(); pr[(x[0], x[1])] = int(x[3]) + int(x[5])
rows = []; cnt = {}
for l in open('panel.txt'):
    if l[0] == '#': continue
    k, q3, q5 = l.split(); key = (q3, q5)
    if k != 'F':
        ok = all(V[v][key][0] == 'PASS' for v in ('R1', 'R3')) and O[key][0] == 'PASS'
        cnt['control ok'] = cnt.get('control ok', 0) + ok; continue
    rl = real[key]; npar, ngen = int(rl[4]), int(rl[6])
    loose = [v for v in V if V[v][key][0] == 'PASS']
    cls = 'GENUINE' if ngen else 'LOOSE' if loose else 'UNRESOLVED'
    if ngen and loose: cls = 'BUG'
    cnt[cls] = cnt.get(cls, 0) + 1
    rows.append(f"| {q3} {q5} | {int(q3)//3072} | {int(q5)%832%13} | {O[key][1]:.6f} | {max(V[v][key][1] for v in V):.6f} {','.join(loose) or '-'} | {npar} / {ngen} | {pr.get(key, 0)} | {cls} |")
print("| pair q3 q5 | s | j5 | (i) ratio | (ii) best ratio, passing variants | real parents / below target | failing probes /400 | class |")
print("|---|---|---|---|---|---|---|---|"); print('\n'.join(rows)); print(cnt)
