"""cert43.py assumes every diagonal of P is at least 1/2 in its units. Multiply P by a power of 4 so that it is.
usage: python3 rescale_pkl.py   (rewrites rr43_data.pkl in place; positivity is unchanged)
"""
import pickle
from fractions import Fraction as Fr

d = pickle.load(open('rr43_data.pkl', 'rb'))
P, PS = d['P'], d['Pscale']
e = []
for i in range(len(P)):
    x, k = Fr(P[i][i], 2 ** PS), 0
    while x * Fr(4) ** k >= 2:
        k -= 1
    while x * Fr(4) ** k < Fr(1, 2):
        k += 1
    e.append(k)
s = max(0, max(e))
print('exponents', min(e), max(e), 'shift', s)
d['Pscale'] = PS - 2 * s
pickle.dump(d, open('rr43_data.pkl', 'wb'))
