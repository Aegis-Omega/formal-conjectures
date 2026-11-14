# `--trust=0` replay of the window 3/2 trace modules

Date: 2026-11-11. Local build (Lean 4.33.1, Mathlib `0df444a`), every module recompiled from source
with `lean --trust=0` into a fresh output directory.

| Module | exit | errors | sorry | seconds |
|---|---|---|---|---|
| `CvSExpL32V1` | 0 | 0 | 0 | — |
| `CvSTraceM4SlackV1` | 0 | 0 | 0 | — |
| `CvSTraceDistK150V1` | 0 | 0 | 0 | — |
| `CvSTraceCellL32V1` | 0 | 0 | 0 | 20 |
| `CvSTraceIntegralL32V1` | 0 | 0 | 0 | 7 |
| `CvSTraceCertL32V1` | 0 | 0 | 0 | 2934 |

```
'AEGIS.CvSTraceCertL32V1.all_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTraceCertL32V1.total_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTraceCertL32V1.trace_premises_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Scope: the lab modules these six import were compiled at default trust; the `--trust=0` replay
covers the six modules of this checkpoint. Not run in CI. This closes the item "trace `--trust=0`
UNKNOWN" of the 2026-11-11 status table. RH remains OPEN.
