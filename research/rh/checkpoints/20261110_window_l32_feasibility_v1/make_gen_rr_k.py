"""Derive gen_rr_k.py from ../20261031_window_l118/gen_rr_lt.py: the number of atoms (frequencies |k| <= KK),
the far bound TF and the fixed slack of epsIn become parameters, and the prime power 4 enters for LT >= log 4.
usage: python3 make_gen_rr_k.py PATH/gen_rr_lt.py > gen_rr_k.py
then:  python3 gen_rr_k.py LT NP EPS KAPPA RHO_LOW RHO_HIGH RHO_DIAG KK [TF] [SLACK_EXP]
"""
import re
import sys

t = open(sys.argv[1]).read()


def rep(a, b):
    global t
    assert a in t, a
    t = t.replace(a, b)


rep("RL, RH, RDG = (float(x) for x in sys.argv[5:8])", "RL, RH, RDG = (float(x) for x in sys.argv[5:8])\nKK = int(sys.argv[8])")
rep("assert LT < mp.log(4)\nPRIMES = [(2, 2 * mp.log(2) / mp.sqrt(2)), (3, 2 * mp.log(3) / mp.sqrt(3))]",
    "assert LT < mp.log(5)\nPRIMES = [(2, 2 * mp.log(2) / mp.sqrt(2)), (3, 2 * mp.log(3) / mp.sqrt(3))]\n"
    "if LT >= mp.log(4):\n    PRIMES.append((4, 2 * mp.log(2) / mp.sqrt(4)))")
for a, b in (("k <= 70", "k <= KK"), ("range(-70, 71)", "range(-KK, KK + 1)"), ("range(71, NP + 1)", "range(KK + 1, NP + 1)"),
             ("range(71)", "range(KK + 1)"), ("+ 70]", "+ KK]"), ("[1:71]", "[1:KK + 1]"), ("[71:]", "[KK + 1:]"),
             ("[0:71]", "[0:KK + 1]"), ("range(1, 71)", "range(1, KK + 1)"), ("140 * ulp", "(2 * KK) * ulp"),
             ("NP - 69", "NP - KK + 1"), ("NP - 70", "NP - KK"), ("range(141)", "range(2 * KK + 1)"),
             ("range(139)", "range(2 * KK - 1)"), ("i - 70 + s", "i - KK + s"), ("n = 139", "n = 2 * KK - 1"),
             ("range(1, NP + 72)", "range(1, NP + KK + 2)"),
             ("TF = 13\n", "TF = int(sys.argv[9]) if len(sys.argv) > 9 else 13\n"),
             ("/ (1 - gam) ** 2 + Fr(1, 10 ** 12)",
              "/ (1 - gam) ** 2 + Fr(1, 10 ** (int(sys.argv[10]) if len(sys.argv) > 10 else 12))")):
    rep(a, b)
t = re.sub(r"(?<![\d.])141(?!\d)", "(2 * KK + 1)", t)
sys.stdout.write(t)
