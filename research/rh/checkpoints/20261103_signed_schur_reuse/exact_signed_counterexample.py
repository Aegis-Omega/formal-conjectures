#!/usr/bin/env python3
"""Exact six-dimensional signed-Gram example: Schur absolute row failure != sign failure.

This is a method falsifier, not a construction of an actual Weil Gram or a proof of RH.
"""
from fractions import Fraction as Q
import json
from pathlib import Path

n=6
chi={0:0,1:1,2:-1,3:-1,4:1}
C=[[Q(0) for _ in range(n)] for _ in range(n)]
for j in range(1,n): C[0][j]=C[j][0]=Q(1)
for i in range(1,n):
    for j in range(1,n): C[i][j]=Q(chi[(i-j)%5])
def multiply(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
I=[[Q(i==j) for j in range(n)] for i in range(n)]
assert C==[list(r) for r in zip(*C)]
assert multiply(C,C)==[[5*I[i][j] for j in range(n)] for i in range(n)]
A=[[-I[i][j]+Q(1,4)*C[i][j] for j in range(n)] for i in range(n)]
G=[[-x for x in row] for row in A]
G2=multiply(G,G)
R=[[Q(1,2)*G2[i][j]+Q(11,32)*I[i][j] for j in range(n)] for i in range(n)]
assert R==G
assert all(A[i][i]==-1 for i in range(n))
rows=[sum(abs(A[i][j]) for j in range(n) if j!=i) for i in range(n)]
assert rows==[Q(5,4)]*n
# A source-exact UNIVERSAL weighted-row obstruction, not a single
# numerical choice of weights. K is the nonnegative absolute off-diagonal
# Schur matrix. Every column (and row) sum is exactly 5/4.
# For arbitrary w_i > 0:
#   sum_i (K w)_i = (5/4)*sum_i w_i > sum_i w_i.
# Thus it is impossible that (K w)_i <= w_i for all i.
# The checked rational column-sum identity is the finite certificate
# for the universal statement, with no search over weights.
K=[[abs(A[i][j]) if i!=j else Q(0) for j in range(n)] for i in range(n)]
assert all(sum(K[i][j] for i in range(n)) == Q(5,4) for j in range(n))
assert all(sum(K[i][j] for j in range(n)) == Q(5,4) for i in range(n))
# For *any* positive row weights w, at a minimal-weight index i the weighted
# row is >= 5/4. This is a universal no-go for weighted absolute Schur
# dominance for this fixed signed Gram, not merely for equal weights.
weights=[Q(9),Q(2),Q(15),Q(1),Q(3),Q(8)]
i=min(range(n),key=lambda k:weights[k])
weighted_min_row=sum(abs(A[i][j])*weights[j]/weights[i] for j in range(n) if j!=i)
assert weighted_min_row>=Q(5,4)>1
# For every v in C^6, -v* A v = (1/2) ||G v||² + (11/32)||v||².
# The exact matrix identity G = (1/2) G^2 + (11/32)I proves this, universally.
result={'source':'Exact standalone symmetric Paley conference matrix, not actual Weil B',
        'dimension':n,'matrix_C':[[int(v) for v in row] for row in C],
        'C_squared_equals_5I':True,'matrix_A':[[str(v) for v in row] for row in A],
        'all_absolute_offdiagonal_row_sums':[str(v) for v in rows],
        'negative_diagonal_magnitude':'1',
        'absolute_schur_column_sums':[str(sum(K[i][j] for i in range(n))) for j in range(n)],
        'universal_weighted_row_exact_certificate':'For any strictly positive w, sum_i (K w)_i = (5/4)*sum_i w_i > sum_i w_i; therefore K w <= w componentwise is impossible.',
        'universal_weighted_row_obstruction':'At an index of smallest positive w_i, sum_{j != i} |A_ij| w_j / w_i >= 5/4 > 1 for EVERY w>0',
        'strict_negative_definite_certificate':'-A = 1/2*(-A)^2 + 11/32*I',
        'certificate_verified_exactly':True,
        'conclusion':'Absolute Gershgorin/Schur row dominance is NOT necessary for negative definiteness',
        'does_not_imply':['AEGIS actual Weil Gram positivity','Riemann hypothesis','kernel-verified theorem']}
resultfile=Path(__file__).with_name('EXACT_CERTIFICATE.json')
resultfile.write_text(json.dumps(result,indent=2)+'\n')
print('PASS: C^2=5I, -A = 1/2*(-A)^2 + 11/32 I, all 6 absolute row ratios=5/4>1')
