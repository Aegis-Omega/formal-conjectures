"""cert43.py writes cert43_<q>.pkl even when it prints `ok False`. A pass is the inequality eta < eps.
usage: python3 check_cert_pkl.py cert43_80.pkl   (exit 0 only if eta < eps and no exponent dd is negative)
"""
import pickle
import sys

d = pickle.load(open(sys.argv[1], 'rb'))
ok = d['eta'] < d['eps'] and all(x >= 0 for x in d['dd'])
print('q %d  eps %d  eta %d  min dd %d  eta < eps: %s' % (d['q'], d['eps'], d['eta'], min(d['dd']), d['eta'] < d['eps']))
sys.exit(0 if ok else 1)
