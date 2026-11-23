"""Derive gen_cert4932.py (trace certificate generator at L = 49/32, M = 4, 311 atoms) from
../20261031_window_l118/gen_cert118.py by literal substitution (as make_gen_cert32.py at L = 3/2).
usage: python3 make_gen_cert4932.py PATH/gen_cert118.py > gen_cert4932.py
then:  python3 gen_cert4932.py OUT.lean --eval            (scratch file that #evals the chunk checks)
       python3 gen_cert4932.py CvSTraceCertL4932V1.lean cert4932_totals.json
"""
import sys

t = open(sys.argv[1]).read()
for a, b in (("('100', '1 / 3', 645, 43)", "('100', '1 / 3', 1563, 43)"), ("TOP = 315", "TOP = 621"),
             ("Layout: width 1/150 on [0, 4], 1/30 on [4, 20], 1/6 on [20, 100], 1/3 on [100, 315]; m = 33/20.",
              "Layout: width 1/150 on [0, 4], 1/30 on [4, 20], 1/6 on [20, 100], 1/3 on [100, 621]; m = 33/20."),
             ("Writes CvSTraceCertL118V1.lean", "Writes CvSTraceCertL4932V1.lean"),
             ("gen_cert118.py", "gen_cert4932.py"), ("cert118_totals.json", "cert4932_totals.json"),
             ("CvSTraceIntegralL118V1", "CvSTraceIntegralL4932V1"), ("CvSTraceCertL118V1", "CvSTraceCertL4932V1"),
             ("CvSTraceCellL118V1", "CvSTraceCellL4932V1"), ("trace_premises_L118", "trace_premises_L4932"),
             ("h118", "h4932"), ("L = 11/8", "L = 49/32"), ("(11 / 8", "(49 / 32"), ("Fin 141", "Fin 313"),
             ("139 atoms", "311 atoms"), ("ScertM 3", "ScertM 4"), ("`M = 3`", "`M = 4`"),
             ("m0 + w2Hi + w3Hi", "m0 + w2Hi + w3Hi + w4Hi"), ("def Tq : ℚ := 7 / 2", "def Tq : ℚ := 3"),
             ("      58 ≤ (2 * Real.pi)", "      66 ≤ (2 * Real.pi)"), ("`κ = 58`", "`κ = 66`"),
             ("`T = 7/2`", "`T = 3`"), ("AEGIS.CvSTraceDistV1", "AEGIS.CvSTraceDistK156V1"),
             ("open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3\n",
              "open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3\nopen AEGIS.CvSTraceM4SlackV1\n")):
    assert a in t or a == "cert118_totals.json", a
    t = t.replace(a, b)
sys.stdout.write(t)
