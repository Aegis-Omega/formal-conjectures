# Existing certificates and the moment trace interface

The existing L=21/20 certificate already proves the actual window sign for
0 <= L < 21/40. Its 133 batch source files are recoverable from the committed
consolidated archive. PR80's preserved final log reports the original standard
axiom audits. This continuation does not claim a fresh replay of those batches.

The existing Aegis-Omega/AEGIS-OMEGA PR699 source at
0c1477fb032bb979a1bc61efd23caa4cacfe376c contains rigorous Arb Krein/slack
and trace certificates. They are labelled INTERVAL_CERTIFIED_NOT_LEAN.
Their data and normalization must be reused faithfully.

A new run of the existing trace algorithm at N=70, with unchanged L1.2 slack,
gives normalized residual <= 0.180615 when both moment exponentials are
included, versus <= 1.926202 for the moment-zero block alone. These are
different trial spaces. No theorem permits using the first number with the
second space.

The current Lean trace input is T = integral s(t) R(t) dt. The Arb scripts
report integral s(t) R(t) dt / (2*pi). Multiply by 2*pi to align them.

There is also a strict support issue: the existing L1.2 correction has boundary
terms at 1.2, whereas the current fixed LT=1.2 wrapper requires LT < L.
Using the existing L1.3 correction and its unchanged slack resolves this
parameter mismatch at the level of the data. Its new N=70 trace calculation
on LT=1.2 gives normalized residual <= 0.181964 with both moment directions,
versus <= 2.048209 without them. This is an Arb result, not a Lean integral
certificate. Its m=1.95 is above 31/16 and its candidate T is below 6.

CvSMomentTraceV1 derives the missing orthogonality from the original two
moments and composes the original Cauchy--Schwarz, trace and Krein complement
theorems with the augmented family. Its source is a candidate until the
original-import CI receipt says PASS. It does not assert the numeric bound,
pointwise Krein certificate, or unconditional RH.
