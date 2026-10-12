exec(open('realpar.py').read())
import pickle
lv = {}
for l in open('panel.txt'):
    if l[0] == '#': continue
    k, q3, q5 = l.split(); q3, q5 = int(q3), int(q5); r3, r5 = q3 % NB3, q5 % NB5
    lv[(q3, q5)] = []
sc = {}
for n in range(12, 12001, 6):
    m3, p3 = scale(3, n); m5, p5 = scale(5, n)
    sc[n] = (bins_closed(p3, n, R3), bins_closed(p5, n, R5))
for (q3, q5) in lv:
    j3, j5 = q3 % NB3 % M3, q5 % NB5 % M5
    lv[(q3, q5)] = [n for n in sc if j3 in sc[n][0] and j5 in sc[n][1]]
pickle.dump(lv, open('levels.pkl', 'wb'))
for k, v in lv.items(): print(k, len(v), v[:4])
