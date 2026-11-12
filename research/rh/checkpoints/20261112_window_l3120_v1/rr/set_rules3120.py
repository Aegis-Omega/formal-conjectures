"""Set the data constants of port_rules3120.json from rr43_data.pkl (L = 31/20): the box maxima of `Box`,
`A0lit`/`A1lit` of `In` and `Cu ≥ 31/(40π²)` of `Err` (KK = 156, NP = 2000; the other rules of the 49/32 port
do not depend on the data). Run in rr/ after gen_rr3120.py.  usage: python3 set_rules3120.py"""
import json
import pickle

KK = 156
d = pickle.load(open('rr43_data.pkl', 'rb'))
t, rt, dl, rd, g1 = d['tLit'], d['rtLit'], d['dLit'], d['rdLit'], d['g1']
new = dict(rhoq=max(rt[0:KK + 1]), rhoHq=max(rt[KK + 1:]), rDq=max(rd), tmq=max(abs(x) for x in t[0:KK + 1]),
           tmHq=max(abs(x) for x in t[KK + 1:]), dmq=max(abs(x) for x in dl),
           A0lit=sum(x * x for x in g1), A1lit=sum((m * g1[m + KK]) ** 2 for m in range(-KK, KK + 1)))
assert min(abs(x) for x in g1) >= 2 ** 81
R = json.load(open('port_rules3120.json'))
n = 0
for mod in ('Box', 'In'):
    for r in R[mod]['str']:
        for k, v in new.items():
            if r[1].startswith(f'def {k} : ℤ := '):
                r[1] = f'def {k} : ℤ := {v}'
                n += 1
for r in R['Err']['str']:
    if r[1].startswith('def Cu : ℝ := '):
        r[1] = 'def Cu : ℝ := 78525 / 1000000'
        n += 1
assert n == 9, n
open('port_rules3120.json', 'w').write(
    '{\n' + ',\n'.join(f' {json.dumps(k)}: {json.dumps(v, ensure_ascii=False)}' for k, v in R.items()) + '\n}\n')
print('set', n, {k: v for k, v in new.items() if not k.startswith('A')})
