# λ_a lab, sprint S1/S2 (2026-11-01)

Numerical study of the lowest eigenvalue of the Weil quadratic form restricted to
test functions supported in `[-a, a]` (additive coordinates). This is research
evidence only: no Lean, no proof, no change to any admission gate.

## Object

`QW(v) = W(v * ṽ)` with Weil's functional in Suzuki's normalization
(arXiv 2606.09096, §1.1; equivalently Connes–Consani–Moscovici arXiv 2511.22755, (3.10)–(3.19)):

```
W(f) = ∫ f(x)(e^{x/2}+e^{-x/2}) dx − Σ_n Λ(n)/√n (f(log n)+f(−log n))
       − (log 4π + γ) f(0) − ∫_0^∞ {f(x)+f(−x)−2e^{−x/2} f(0)} e^{x/2}/(2 sinh x) dx
```

* `λ_a`  = inf of `QW(v)/‖v‖²` over `v ∈ L²(−a, a)`.
* `λ0_a` = the same infimum over the moment-zero subspace `∫ v e^{±x/2} = 0`
  (the packets used on this PR; by `exists_momentKiller_packet` this subspace is
  the image of `D0 = 1/4 − ∂²` on functions supported in `[−a, a]`).

Weil/Yoshida: RH ⇔ `λ_a ≥ 0` for every `a`. Suzuki (Thm 1.3) proves `λ_a` is continuous;
CCM (3.27) prove it is nonincreasing.

## Method

Legendre basis `P_k(x/a)`, `k < N`. The autocorrelations are polynomials with exact
rational coefficients (`qwhp.py`, independent of `a`); archimedean moments, the pole
term and the prime terms `n ≤ e^{2a}` are evaluated with mpmath at 200 digits.
`qw.py` is an independent double-precision implementation (numpy quadrature).

Every value below is a Rayleigh–Ritz value, i.e. an **upper bound** for `λ_a` / `λ0_a`.
A positive Ritz value says nothing about a lower bound.

## Validation

`validate.py`: for `v = (1 − (x/a)²)^k`, `QW(v)` from the matrix equals the sum of
`|v̂(γ)|²` over the first 300 zeta zeros (explicit formula):
relative agreement 2e-13 (a=0.5), 2e-10 (a=1.0), 1.5e-6 (a=1.7, limited by
zero truncation). `qwhp.py` reproduces `qw.py` (a=0.5, N=20: 9.5634e-7).

## Results

Double precision, converged in N (N = 12/20/28 agree):

| a | λ_a | λ0_a |
|---|---|---|
| 0.2 | 9.49e-2 | 1.10 |
| 0.3 | 7.57e-3 | 6.92e-1 |
| 0.4 | 1.82e-4 | 2.26e-1 |
| 0.5 | 9.42e-7 | 1.19e-2 |
| 0.6 | 1.67e-9 | 6.80e-5 |

200 digits (`S1_results.txt`), N = 32 / 48:

| a | 2a | λ_a N=32 | λ_a N=48 | λ0_a N=32 | λ0_a N=48 |
|---|---|---|---|---|---|
| 0.6875 | 1.375 | 1.39e-12 | 1.30e-12 | 1.69e-7 | 1.66e-7 |
| 0.75 | 1.5 | 5.81e-15 | 3.88e-15 | 9.52e-10 | 7.68e-10 |
| 0.85 | 1.7 | 3.40e-17 | 5.25e-20 | 3.06e-12 | 2.20e-14 |
| 1.0 | 2.0 | 1.62e-20 | 1.98e-25 | 8.79e-16 | 1.84e-20 |
| 1.25 | 2.5 | 1.56e-23 | 1.61e-31 | 3.09e-19 | 1.05e-25 |
| 1.5 | 3.0 | 9.24e-26 | 1.16e-34 | 2.09e-22 | 1.12e-29 |
| 2.0 | 4.0 | 2.49e-31 | 9.32e-42 | 1.93e-25 | 1.40e-36 |

For `a ≥ 0.85` the values are not converged in N; the true infima are smaller still.
Between converged points, `Δ log λ_a / Δ e^{2a}` = −7.7, −9.1, −10.7, −10.6, −11.3,
approaching `−4π`, the rate of `1 − χ(λ) ~ e^{−4πλ²}` (λ = e^a) against which CCM
compare their ε_λ (Fig. 4), i.e. `λ_a ≈ exp(−4π e^{2a})` up to lower-order factors.

S2 (`s2.py`, `s2_results.txt`, N = 32, 120 digits): for a = 0.3, 0.5, 0.6, 0.6875 the
lowest eigenvalue is simple (λ2/λ1 = 29, 207, 365, 606) and its eigenvector is even
(odd Legendre part ≤ 1e-113). The form commutes with `x ↦ −x`, so parity blocks
decouple exactly; the observation is that the minimum sits in the even block.
This matches CCM's "simple-even" hypothesis and Suzuki Thm 1.4 for these `a`.

## S1c: certified upper bounds (`certify.py`, `CERTIFIED.txt`)

`v = ψ/4 − ψ''` with `ψ(x) = (1 − (x/a)²)² p(x/a)`, `p` of degree 39 with rational
coefficients. ψ and ψ' vanish at `±a`, so both log moments of `v` are exactly zero (the
computed moment balls contain 0 with radius ~1e-233). Every term of `QW(v)` is evaluated in
arb ball arithmetic at 800 bits (exact rational Legendre data, `acb.integral` for the
archimedean, pole and moment integrals), so `QW(v)/‖v‖²` is an enclosure, not an estimate:

| a | primes in the form | certified `QW(v)/‖v‖²` ≤ |
|---|---|---|
| 3/4 | 2, 3, 4 | 7.67846e-10 |
| 1 | 2 … 7 | 1.93609e-18 |
| 5/4 | 2 … 11 | 4.98549e-23 |
| 3/2 | 2 … 19 | 4.22158e-26 |

These are rigorous upper bounds for `λ0_a` (rigorous up to arb and this script, not checked
by the Lean kernel). With the argument in point 2 below, a family bound
`QW(Σ g_i) ≥ c Σ ‖g_i‖²` for fine packets with bounded overlap spread over `[−3/2, 3/2]`
must have `c ≤ 8.45e-26`.

## Consequences for the budget route on this PR

1. The window `2r ≤ 11/8` (a = 11/16) proved in Lean sits where `λ0_a ≈ 1.7e-7`.
   The margin then falls doubly exponentially; a certificate at spread `a` needs
   roughly `4π e^{2a}/ln 10` correct digits (≈ 300 at a = 2, ≈ 800 at a = 2.5).
2. Fine packets of any shapes and centres in `[−a, a]` span the moment-zero subspace
   (each is `D0 ψ_i`, and a partition of unity splits any `ψ`). With `E_i = ‖g_i‖²`
   and every point in at most two supports, `‖Σ g_i‖² ≤ 2 Σ E_i`, so a family bound
   `QW(Σ g_i) ≥ c Σ E_i` with `c > 0`
   independent of the spread would force `λ0_a ≥ c/2` for all `a`, contradicting the
   table. Any producer of the total signed budget must have a constant that decays at
   least like `λ0_a` in the spread. Pairwise margins of order one (e.g. a two-packet
   bound at distance `log 5`) are compatible with this only locally.
3. The near-kernel is a smooth even function concentrated below frequency
   `≈ 2π e^{2a}`. High-frequency positivity (the archimedean `½ log|t|` growth) is
   the easy regime; tests that only probe high frequencies cannot see the obstruction.

## Files

`qw.py` (double), `qwhp.py` (exact rationals + mpmath), `validate.py`, `scan.py`,
`hpscan.py` (`python3 hpscan.py N full|mz a1,a2,... dps`), `s2.py`,
`S1_results.txt` (sha256 `bb2d2d24d7469cc51aaaf0b0f0bf6988cfdf1011a7da1435408c313ee4dd1575`),
`s2_results.txt`. Requires numpy, scipy, mpmath, python-flint.
