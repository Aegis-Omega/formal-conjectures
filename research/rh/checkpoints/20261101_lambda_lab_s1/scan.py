import numpy as np, sys
sys.path.insert(0, '.')
from qw import lowest
print(' a     2a    | lam_a N=12  N=20  N=28     | lam0_a (moment-zero) N=12  N=20  N=28')
for a in [0.2,0.3,0.4,0.5,0.6,0.6875,0.75,0.85,0.95,1.05,1.15,1.25,1.4,1.6]:
    r = [lowest(a, N) for N in (12, 20, 28)]
    z = [lowest(a, N, True) for N in (12, 20, 28)]
    print(f'{a:6.4f} {2*a:5.3f} | ' + '  '.join(f'{x:10.3e}' for x in r) + ' | ' + '  '.join(f'{x:10.3e}' for x in z), flush=True)
