import sys, time; sys.path.insert(0, '.')
from qwhp import lowest_hp
import mpmath as mp
N = int(sys.argv[1]); mz = sys.argv[2] == 'mz'
for a in [float(x) for x in sys.argv[3].split(',')]:
    t0 = time.time(); v = lowest_hp(a, N, int(sys.argv[4]), mz)
    print(f'a={a} N={N} {"lam0" if mz else "lam"}={mp.nstr(v, 8)}  ({time.time()-t0:.0f}s)', flush=True)
