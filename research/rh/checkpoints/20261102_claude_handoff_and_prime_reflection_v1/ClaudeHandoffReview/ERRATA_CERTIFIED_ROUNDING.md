# Erratum (2026-11-14): the printed bounds in `CERTIFIED.txt`

`CERTIFIED.txt` here is the pinned copy of the original producer output (`SOURCE_MANIFEST.json`) and
is kept unchanged. Its `CERTIFIED_UPPER_BOUND` lines print the upper endpoint of each enclosure
rounded to nearest, so at `a = 3/4` (`7.67846e-10`) and `a = 3/2` (`4.22158e-26`) the printed value
is below the enclosure on the line before it. The upward-rounded values are `7.67847e-10` and
`4.22159e-26`; they are regenerated in
`../../20261101_lambda_lab_s1/CERTIFIED_OUTWARD.txt` by `certify_outward.py` (see `ERRATA.md` there).

The bounds this review states in `REVIEW.md` (`77/10^11` at `3/4`, `43/10^27` at `3/2`) and the
directed rational endpoints of its final receipts are above the enclosures and are not affected.
