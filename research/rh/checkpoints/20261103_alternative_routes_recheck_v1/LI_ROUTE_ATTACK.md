# An independent Li/Hadamard attack and correction of the route scope

The all-radius Schur sign is a missing producer on ONE active route. It
has not been shown that every possible AEGIS completion must pass through
that producer. The Li/Hadamard route has a different explicit input:
nonnegativity of every multiplicity-weighted paired Li coefficient.
The following work does not prove or formalize another RH equivalence.
It reuses the existing identity and tests a proposed unconditional bridge.

## Existing source, not a new reduction

The read source is AegisRH/Li/RHLiWeightedPairedTargetV1.lean, Git blob
4df8893f13319ce78aa3f336c298823c17f909bc, at branch head
5213510f3a6d5be92db4e334546272ab2a08c024. Its
taylorCoeff_eq_weighted_paired_sum_v1 supplies the actual weighted paired
formula, consuming the provider's existing finite-order/Hadamard inputs.
RHLiPairedLaurentV1.lean, blob 1beed9eb71a4d40b921777b277e4ee7257c1e104,
at head 805703116e4eb312899972d55e13f15cefbc569c, already proves the
Laurent expression and the inverse-pairing identity. Neither is reproved.

The external provider remains pinned to
nicholasbulka/li-criterion-rh-equivalence-lean at
35df682f3b709ffe5fbcfdd452dfa964bd622b87. Recovered Basic.lean defines

    phi f z = f(1/(1-z)),
    taylorCoeff f n = (deriv^[n] (logDeriv (phi f))) 0 / n!.

Its XiGrowth.lean obtains the finite-order bound using the theta Mellin
kernel, not an assumed bound for zeta inside the critical strip. The
already recovered XiGrowth and HadamardBridge bytes match the pinned
provider's Git blobs dd18b3bd669bd380c5754af69934769b45ac448a and
088eef5ee66da37630ef41b873656a7b3726c41d. This is source verification,
not a fresh transitive Lean replay. The provider's original Mathlib pin
is de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11; the AEGIS replay workflow
explicitly rebases it to 0df444a360eaa60ab8c11dca51a86af692955474 and
changes three Factorization proof expressions for compatibility.

## The bridge tested

Candidate: entire finite order at most one, functional-equation symmetry,
conjugation symmetry, zero pairing in the strict critical strip, and
nonnegative Taylor coefficients at the center suffice to make every
paired Li coefficient nonnegative. Adding a finite polynomial ODE does
not save this candidate. This is a proposed generic bridge, NOT a claim
made by the provider and NOT a replacement of the actual zeta target.

For a positive integer b put z=s-1/2 and define the EXACT polynomial

    F_b(s)=z^4+2*(b^2-1/16)*z^2+(b^2+1/16)^2.

Its four simple zeros are 1/4+ib, 1/4-ib, 3/4+ib, 3/4-ib. This follows
by factoring it into ((z-1/4)^2+b^2)*((z+1/4)^2+b^2).
They lie strictly in the critical strip and off the critical line.

F_b is entire of order zero (hence order at most one), real under
conjugation, and satisfies F_b(1-s)=F_b(s). It is strictly positive on
the real axis; all its nonzero center Taylor coefficients are positive.
It has F_b(0)=F_b(1)>0, finite multiplicity-weighted inverse-square sums,
and an elementary finite Hadamard product. It is also holonomic in the
literal differential-equation sense: D^5 F_b=0. No claim is made that
the actual completed zeta is this polynomial or has that differential
equation. In particular this example does not supply the actual Euler
product or the actual theta Mellin kernel.

## Explicit negative coefficient in the provider's normalization

Take b=1. For rho=1/4+i, write w=1-1/rho=(13+16i)/17. Its inverse is
(13-16i)/25. Summing the quartet and pairing inverse/conjugate factors
gives, for m>=1,

    L_m(F_1)=4-2*Re(w^m+w^(-m)).

This L_m is the coefficient at z^(m-1) in logDeriv(phi F_1), so it is
taylorCoeff F_1 (m-1) in the source convention. There is no lost factor
of m, factorial, or multiplicity. Direct Gaussian-integer multiplication
gives (13+16i)^6=44509113-62545184*i. Therefore

    L_6(F_1)
      =[4*(17^6*25^6)-2*44509113*(17^6+25^6)]/(17^6*25^6)
      =-309804177801344/5892961181640625 <0.

This is an exact rational counterexample to the candidate bridge.

A different derivation checks the coefficient directly without zeros:

    phi F_1(z)=P(z)/(256*(1-z)^4),
    P(z)=425-1092*z+1590*z^2-1092*z^3+425*z^4,

so

    logDeriv(phi F_1)(z)
      =(608-96*z-96*z^2+608*z^3)
       /(425-1517*z+2682*z^2-2682*z^3+1517*z^4-425*z^5).

Formal power-series division at zero (denominator 425!=0) gives exactly
the same negative coefficient at degree5. Both exact computations are
performed by verify_counterexample.py; floating-point decisions are
absent. Finite integer certificates in LiQuartetArithmetic.lean concern
the exact arithmetic only, not the analytic identification or RH.

## Finite success does not repair the bridge

At b=20, all four off-line roots have imaginary magnitude20. Exact
rational computation gives strictly positive L_1,...,L_124 but negative
L_125. This is a second explicit finite test, not a theorem about all b
or a numerical experiment presented as a universal proof. It shows why
neither a finite prefix of coefficients nor a finite height exclusion
can replace the omitted global input in this generic construction.

## What this changes

The weighted formula, summability and finite-order foundations are
retained as existing results. The attempted positivity producer from
those broad analytic properties is rejected with exact witnesses. A
successful Li producer must use stronger actual-zeta structure, such as
the Euler-product/theta input beyond its coarse growth consequence, or
another proved mechanism. The example does not rule out such a producer.

This leaves the alternative Li route active; it does not route it back
through Schur by fiat. No step count or proximity to a full proof is
inferred from the number of existing equivalences. RH remains unproved
by this work.
