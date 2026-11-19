# Errata (2026-11-14): the printed upper bounds of `CERTIFIED.txt`

`certify.py` prints `CERTIFIED_UPPER_BOUND lambda0_a <= R.upper().str(6, radius=False)`. The
enclosure `R` of `QW(v)/‖v‖²` is correct, but the six-digit decimal of its upper endpoint is rounded
to nearest, not upward. At `a = 3/4` and `a = 3/2` the printed number is below the enclosure:

| a | enclosure (`CERTIFIED.txt`) | printed (`CERTIFIED.txt`, README table) | rounded up (`CERTIFIED_OUTWARD.txt`) |
|---|---|---|---|
| 3/4 | `[7.67846075110e-10 +/- 2.63e-22]` | `7.67846e-10` (too low) | `7.67847e-10` |
| 1 | `[1.93608583536e-18 +/- 9.68e-31]` | `1.93609e-18` | `1.93609e-18` |
| 5/4 | `[4.98548768515e-23 +/- 3.20e-35]` | `4.98549e-23` | `4.98549e-23` |
| 3/2 | `[4.22158275532e-26 +/- 2.40e-38]` | `4.22158e-26` (too low) | `4.22159e-26` |

`certify_outward.py` is `certify.py` with one change: the printed bound is the upper endpoint rounded
up to six significant digits in exact rational arithmetic, with an assertion that it is at least the
endpoint. `CERTIFIED_OUTWARD.txt` is its complete output for the same four runs (K = 40, 800 bits);
the four enclosures are identical to those of `CERTIFIED.txt`. `certify.py`, `CERTIFIED.txt` and
`README.md` are kept byte for byte: the handoff review
`../20261102_claude_handoff_and_prime_reflection_v1/ClaudeHandoffReview/SOURCE_MANIFEST.json` pins
them. The consequence in the README (`c ≤ 8.45e-26`) holds with the corrected bound
(`2 · 4.22159e-26 = 8.44318e-26`). Not RH; these are arb numbers, not Lean-checked.

sha256: `certify_outward.py` `5cbc83f4cf617ae811e3581daed95e7369e490129f6b98dac9e65332c14d1c58`, `CERTIFIED_OUTWARD.txt` `e2560469ff8c239075c5be4336fd8a8ed99507545300c3e04c2b5b1a4c5ffcdb`.
