"""Ball comparison of blocks JSON files: A11, G11, CB entrywise overlap against the first file, plus the scalar fields."""
import sys, json
from flint import arb, acb, ctx
ctx.prec = 256
files = sys.argv[1:]; P = [json.load(open(f)) for f in files]
for key in ('L', 'N', 'NP', 'tail_order', 'tail_weights', 'K2', 'Amax', 'Eco'):
    vals = [p[key] for p in P]
    if key in ('K2', 'Amax', 'Eco'):
        b = [arb(v) for v in vals]; print(key, 'all overlap' if all(x.overlaps(b[0]) for x in b) else 'MISMATCH', [v[:24] for v in vals])
    else: print(key, 'identical' if all(v == vals[0] for v in vals) else 'DIFFER', vals[0])
def mat(p, nm): return [[acb(arb(re), arb(im)) for re, im in row] for row in p[nm]]
B = {nm: mat(P[0], nm) for nm in ('A11', 'G11', 'CB')}
for f, p in zip(files, P):
    out = []
    for nm in ('A11', 'G11', 'CB'):
        X = mat(p, nm); k = len(X); Y = B[nm]
        bad = [(i, j) for i in range(k) for j in range(k) if not X[i][j].overlaps(Y[i][j])]
        rad = max(max(float(X[i][j].real.rad()), float(X[i][j].imag.rad())) for i in range(k) for j in range(k))
        out.append(f"{nm}: nonoverlap={len(bad)}{' first ' + str(bad[0]) if bad else ''} maxrad={rad:.2e}")
    print(f.split('/')[-2], 'k=%d' % k, ' | '.join(out))
