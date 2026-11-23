"""Where does the j-th eigenvalue of the window form leave the bulk? Compare with l_k = ln(gamma_k / 2 pi)."""
import math, re, sys
rows = []
for l in open(sys.argv[1]):
    m = re.match(r'l=([\d.]+) T\*=([\d.]+) N=\d+: (.*)', l)
    if m: rows.append((float(m.group(1)), [float(x) for x in m.group(3).split()]))
gam = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832]
lk = [math.log(g / (2 * math.pi)) for g in gam]
for c in (0.3, 0.1, 0.03):
    print(f'threshold {c}:')
    for j in range(2, 12):
        cross = None
        for (l0, e0), (l1, e1) in zip(rows, rows[1:]):
            if e0[j] >= c > e1[j] > 0:
                cross = l0 + (l1 - l0) * (math.log(e0[j]) - math.log(c)) / (math.log(e0[j]) - math.log(e1[j])); break
        k = j - 2
        if cross is None: print(f'  eigenvalue {j+1}: no crossing'); continue
        print(f'  eigenvalue {j+1}: l = {cross:.3f}   l_{k+1} = {lk[k]:.3f} (gamma = {gam[k]:.2f})   diff {cross - lk[k]:+.3f}')
