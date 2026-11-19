"""Derive gen_cert32.py (trace certificate generator at L = 3/2, M = 4, 299 atoms) from
../20261031_window_l118/gen_cert118.py by literal substitution.
usage: python3 make_gen_cert32.py PATH/gen_cert118.py > gen_cert32.py
then:  python3 gen_cert32.py OUT.lean --eval            (scratch file that #evals the chunk checks)
       python3 gen_cert32.py CvSTraceCertL32V1.lean cert32_totals.json
"""
import sys

t = open(sys.argv[1]).read()
for a, b in (("('100', '1 / 3', 645, 43)", "('100', '1 / 3', 1563, 43)"), ("TOP = 315", "TOP = 621"),
             ("Layout: width 1/150 on [0, 4], 1/30 on [4, 20], 1/6 on [20, 100], 1/3 on [100, 315]; m = 33/20.",
              "Layout: width 1/150 on [0, 4], 1/30 on [4, 20], 1/6 on [20, 100], 1/3 on [100, 621]; m = 33/20."),
             ("Writes CvSTraceCertL118V1.lean", "Writes CvSTraceCertL32V1.lean"),
             ("gen_cert118.py", "gen_cert32.py"), ("cert118_totals.json", "cert32_totals.json"),
             ("CvSTraceIntegralL118V1", "CvSTraceIntegralL32V1"), ("CvSTraceCertL118V1", "CvSTraceCertL32V1"),
             ("CvSTraceCellL118V1", "CvSTraceCellL32V1"), ("trace_premises_L118", "trace_premises_L32"),
             ("h118", "h32"), ("L = 11/8", "L = 3/2"), ("(11 / 8", "(3 / 2"), ("Fin 141", "Fin 301"),
             ("139 atoms", "299 atoms"), ("ScertM 3", "ScertM 4"), ("`M = 3`", "`M = 4`"),
             ("m0 + w2Hi + w3Hi", "m0 + w2Hi + w3Hi + w4Hi"), ("def Tq : ℚ := 7 / 2", "def Tq : ℚ := 3"),
             ("      58 ≤ (2 * Real.pi)", "      66 ≤ (2 * Real.pi)"), ("`κ = 58`", "`κ = 66`"),
             ("`T = 7/2`", "`T = 3`"), ("AEGIS.CvSTraceDistV1", "AEGIS.CvSTraceDistK150V1"),
             ("open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3\n",
              "open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3\nopen AEGIS.CvSTraceM4SlackV1\n")):
    assert a in t or a == "cert118_totals.json", a
    t = t.replace(a, b)
sys.stdout.write(t)
