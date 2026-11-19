# Attack through positive jump energies: exact identity and falsified shortcuts

Status: ordinary mathematical derivation and adversarial examples by the primary
agent. No new independent-agent or Lean verification is claimed for this file.
The full form, angular transform, carrier and normalizations are those checked
in PROOF_COMPOSITION.md. This attempt attacks the missing signed budget; it
does not assert a new RH equivalence or a proof of RH.

Source recovery update: a targeted filename search recovered the existing
`harness/sdk/weil_levy_gap_probe.py`, Git blob
`5729678b1a0293b453ae72c73703890c19d61940`, in Aegis-Omega/AEGIS-OMEGA
commit `5ffb5e2b969cd3873160696d88ea593ac28f77e3`. It ALREADY states the
finite-cutoff Levy–Khintchine decomposition plus adverse scalar shift and
explicitly denies a uniform/global gap. Section1 below reconstructs and
reuses that existing identity; it is not a newly discovered theorem. The
source is preserved in `JumpSource`, with recomputed blob/SHA manifests.
The subsequent scalar/domain/log-concavity falsifiers remain separately
identified arguments. No claim is made that nobody previously wrote them.

## 1. Retain the arithmetic signs in an exact jump-energy identity

Let H be zero-extended from [-R,R], in the logarithmic form domain. Let
c_m=Lambda(m)/sqrt(m) and choose an integer cutoff M with log(M+1)>2R.
Set A_M=2 sum_(m=2)^M c_m and a(t)=exp(t/2)/sinh(t). Let Q0 denote the
complete Archimedean-minus-prime form, omitting the polar term. On the legal
two-exponential-moment class it is exactly the intended Q. Then

    Q0(H)=(w(0)-A_M)||H||²
          +(1/2) integral_0^infinity a(t)||T_t H-H||² dt
          +sum_(m=2)^M c_m ||T_(log m)H-H||².

Proof: the digamma series, or positive Tonelli expansion of 1/sinh(t), gives
w(xi)-w(0)=integral a(t)(1-cos(xi t))dt. Angular Plancherel turns this into
one half of the squared translation difference. Separately

    ||T_t H-H||²=2||H||²-2Re C_H(t).

Insert this identity in EVERY prime term. The result retains all signs,
prime powers, Archimedean tail and factors of two. Extra primes beyond the
support cutoff add 2c_m||H||² to the jump energy and subtract exactly the
same amount from the scalar term. Thus increasing M does not change Q0.

The jump measure is positive, but the scalar coefficient w(0)-A_M is
negative. Replacing this identity by positivity of the jump energies alone
loses the entire required budget. A lower bound for the jump energy on the
legal subspace must actually pay (A_M-w(0))||H||². The high-moment producer
pays this on its complement. It does not pay it on the original full class.

## 2. A scalar ground-state supersolution for the whole pole-free form fails

Take H=1_[-1/4,1/4], E=1/2. This is a piecewise smooth element of the form
domain but does NOT satisfy the two exponential moments. Its correlation is
C_H(t)=E-t for 0<=t<=1/2 and zero for t>1/2. All prime samples vanish since
1/2<log2. In the exact real-space normalization,

    Q0(H)=-C0 E-I(H), C0=log(4pi)+gamma,
    I(H)=integral_0^infinity [exp(t/2)C_H(t)-E]/sinh(t)dt.

For 0<=t<=1/2, 1-2t>=0, so exp(t/2)(1-2t)>=1-2t. Hence

    [exp(t/2)(1-2t)-1]/sinh(t)>=-2t/sinh(t)>=-2.

The near integral is therefore >=-1 after division by E. The tail is
exactly log(tanh(1/4)). Since exp(1/2)>3/2, tanh(1/4)>1/5; and log5<5/3.
Thus I(H)/E>-8/3.

Also C0>8/3. Here is an elementary quantitative proof of the constants,
so no numerical value of gamma is needed:

* exp(7/10)>2 follows from the first five positive Taylor terms; their
  difference from2 is2921/240000. Therefore log2<7/10.
* gamma>H_16-log16-1/16 follows from the integral comparison for harmonic
  sums. H_16-1/16-14/5-1/2=6569/360360>0, so gamma>1/2.
* pi>3 is supplied by the alternating integral for4atan1. Since e<3 and
  exp(1/6)<6/5, exp(13/6)<9*(6/5)<12<4pi. Thus log(4pi)>13/6.
* exp(5/3)>5 follows from Taylor degree4, with excess289/1944.

It follows that Q0(H)/E<-C0+8/3<0. The near integral has no unresolved
singularity: its numerator is O(t), so the displayed quotient is bounded.
The tail was evaluated exactly. Smooth mollification preserves negativity
by form-norm continuity for sufficiently small mollifier radius. Those
smooth negative examples still have nonzero exponential moments.

Consequently a scalar positive-ground-state transform proving Q0>=0 on
the WHOLE compact-support space cannot be the desired argument: that larger
statement is false even in a prime-free window. This does not refute a
matrix-valued/projection argument on the legal moment-zero subspace, nor the
existing local positivity theorem. The polar rank-two term was deliberately
omitted here, and it is not zero for this example.

## 3. Positive arithmetic weights plus the correct moments are insufficient

This example keeps the complete Archimedean form and the actual moments.
It changes the arithmetic weights and is NOT a zeta or Euler-product example.

Choose a nonzero real compact smooth potential phi, supported[-h,h], with
2h<log2. Put U=(D²-1/4)phi and l=log2. Both exponential moments of U vanish
by integration by parts; U is nonzero because a compact homogeneous solution
of D²phi=phi/4 must be zero. Put H=U+T_l U. Its moments also vanish and its
two supports are disjoint. Exactly C_H(l)=||U||²=:E_U>0.

Let A be the complete Archimedean form value of H; it is a finite real
number. Give just the arithmetic jump at l the positive coefficient

    b=(|A|+E_U)/(2E_U)>0.

The resulting full moment-zero form satisfies

    Q_b(H)=A-2b E_U=A-|A|-E_U<=-E_U<0.

Thus positivity of the arithmetic jump measure, the exact gamma term,
compact support and both moment conditions do not by themselves force the
sign. A successful budget must use more of the ACTUAL von Mangoldt values
and their correlations. This counterexample rejects the overly broad
lemma; it is not attributed to the actual zeta weights.

## 4. The actual positive jump measure is not log-concave

One possible variation-diminishing route would require log-concavity of
the jump measure itself. That hypothesis already fails on the actual prime
measure; it must not be imported from positivity of the weights.

Away from0, the positive jump measure in section1 is the sum of a continuous
strictly positive density a(t)/2 and isolated atoms c_m at log m. At l=log2
the atom has mass c_2>0. Choose y=l+d with d>0 so small that the interval
from l to y lies below log3. Put z=(l+y)/2. For small epsilon, intervals
I_l,I_y,I_z of radius epsilon about these points are disjoint from all
other atoms, and I_y and I_z contain none. On this fixed interval the
background density has positive lower bound c and finite upper bound C.
Then

    nu(I_l)>=c_2,
    nu(I_y)>=2c epsilon,
    nu(I_z)<=2C epsilon.

Log-concavity would require nu(I_z)>=sqrt(nu(I_l)nu(I_y)), since I_z is
the midpoint Minkowski average. For epsilon<c_2*c/(2C²), the displayed
bounds contradict that inequality. This is an exact small-interval
argument, not a plot or a floating calculation.

It rejects a method requiring this jump measure to be log-concave. It does
NOT prove that every smoothed semigroup kernel, every projected kernel,
or every possible total-positivity construction fails.

## Result and change of strategy

The exact positive-jump representation is valid but its unproved Poincare
budget is the actual signed problem. Scalar positivity on the larger
pole-free domain and log-concavity of the actual jump measure are false.
The viable remaining calculation must retain the legal moment projection,
both parity channels, actual prime weights and the complete mixed block.
The new high-moment/endpoint machinery supplies those domains and analytic
tails; it has not supplied the global low/cross inequality.
