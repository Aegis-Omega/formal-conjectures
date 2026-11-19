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
# A parameter FAMILY of exact positive signed Gram matrices outside EVERY
# absolute weighted Schur/Gershgorin cone.
# For any real alpha with 1/5 < alpha and 5*alpha^2 < 1,
#   G_alpha = I - alpha*C
#           = (G_alpha^2 + (1-5*alpha^2)*I)/2  > 0.
# The absolute off-diagonal matrix K_alpha has every column sum 5*alpha > 1.
# Summing K_alpha*w <= w would imply (5*alpha)*sum(w) <= sum(w),
# impossible for ANY strictly positive vector w.
# The identity is symbolic given C^2=5I; rational witnesses are checked below.
def certify_signed_family(alpha):
    assert Q(1,5) < alpha and 5*alpha*alpha < 1
    gram=[[I[i][j]-alpha*C[i][j] for j in range(n)] for i in range(n)]
    squared=multiply(gram,gram)
    margin=(1-5*alpha*alpha)/2
    assert margin > 0
    assert gram==[[squared[i][j]/2+margin*I[i][j] for j in range(n)] for i in range(n)]
    abs_off=[[abs(gram[i][j]) if i!=j else Q(0) for j in range(n)] for i in range(n)]
    assert all(sum(abs_off[i][j] for j in range(n))==5*alpha for i in range(n))
    assert all(sum(abs_off[i][j] for i in range(n))==5*alpha for j in range(n))
    return {'alpha':str(alpha),'strict_PSD_reserve':str(margin),
            'absolute_schur_weighted_obstruction_ratio':str(5*alpha)}

family=[certify_signed_family(a)
        for a in (Q(21,100), Q(1,4), Q(1,3), Q(2,5))]
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
# Gate-II unitary Schur short, checked with exact rational arithmetic.
# This is an algebraic interface/negative control, NOT an identification with
# Desogus's actual localized Weil operator. The source Schur debit is taken ONCE.
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def mv(M,v): return [dot(row,v) for row in M]
def matmul(A,B):
    return [[dot(A[i],[B[k][j] for k in range(len(B))])
             for j in range(len(B[0]))] for i in range(len(A))]
def trans(A): return [list(r) for r in zip(*A)]
def inv2(M):
    det=M[0][0]*M[1][1]-M[0][1]*M[1][0]
    assert det>0
    return [[M[1][1]/det,-M[0][1]/det],[-M[1][0]/det,M[0][0]/det]]

def certify_gate2_one_debit(alpha):
    gram=[[I[i][j]-alpha*C[i][j] for j in range(n)] for i in range(n)]
    source=[row[:2] for row in gram[:2]]
    cross=[row[2:] for row in gram[:2]]
    target=[row[2:] for row in gram[2:]]
    source_inv=inv2(source)
    debit=matmul(matmul(trans(cross),source_inv),cross)
    short=[[target[i][j]-debit[i][j] for j in range(4)] for i in range(4)]
    # Exact whole-matrix congruence: proves the Schur square completion
    # for ALL rational/real target vectors, not a sample of five vectors.
    # H^T G H = Schur and T^T G T = diag(source, Schur).
    h_top=[[-v for v in row] for row in matmul(source_inv,cross)]
    H=h_top+[[Q(i==j) for j in range(4)] for i in range(4)]
    assert matmul(matmul(trans(H),gram),H)==short
    T=[([Q(i==j) for j in range(2)]+h_top[i]) for i in range(2)]
    T += [([Q(0),Q(0)]+[Q(i==j) for j in range(4)]) for i in range(4)]
    diagonal=[source[i]+[Q(0)]*4 for i in range(2)]
    diagonal += [[Q(0)]*2+short[i] for i in range(4)]
    assert matmul(matmul(trans(T),gram),T)==diagonal
    # Under ANY invertible source-coordinate change U, the exact source
    # cost and Schur complement are invariant. Check orthogonal AND
    # genuinely nonorthogonal rational basis changes.
    source_changes=[[[Q(0),Q(1)],[-Q(1),Q(0)]],
                    [[Q(1),Q(2)],[Q(1),Q(3)]],
                    [[Q(2),Q(1)],[Q(1),Q(1)]]]
    for U in source_changes:
        changed_source=matmul(matmul(trans(U),source),U)
        changed_cross=matmul(trans(U),cross)
        changed_inv=inv2(changed_source)
        changed_debit=matmul(matmul(trans(changed_cross),changed_inv),changed_cross)
        assert changed_debit==debit
        assert [[target[i][j]-changed_debit[i][j] for j in range(4)]
                for i in range(4)]==short
    # Positivity of Schur for ALL y follows from exact source coercivity
    # G = 0.5 G^2 + margin I: ||H y||^2 >= ||y||^2.
    margin=(Q(1)-Q(5)*alpha*alpha)/Q(2)
    assert margin>0
    squared=matmul(gram,gram)
    assert gram==[[squared[i][j]/Q(2)+margin*I[i][j]
                   for j in range(n)] for i in range(n)]
    # An accidental second subtraction of the source cost is detected.
    y=[Q(1),Q(-1),Q(2),Q(0)]
    force=mv(cross,y)
    cost=dot(force,mv(source_inv,force))
    assert cost>0
    assert dot(y,mv(short,y))==dot(y,mv(target,y))-cost
    assert dot(y,mv(short,y))!=dot(y,mv(target,y))-2*cost
    assert short==trans(short)
    return {'alpha':str(alpha), 'whole_matrix_Schur_congruence':'PASS',
            'one_source_debit':'PASS', 'source_rotation_covariance':'PASS',
            'invertible_source_changes_checked':len(source_changes),
            'full_dimension':6, 'source_dimension':2, 'target_dimension':4,
            'strict_Schur_lower_bound':str(margin),
            'double_debit_regression':'PASS'}

gate2_certificates=[certify_gate2_one_debit(a)
                    for a in (Q(21,100),Q(1,4),Q(1,3),Q(2,5))]
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
        'parametric_full_signed_gram_family':family,
        'gate2_one_debit_exact_rational_certificates':gate2_certificates,
        'parametric_proof':'For 1/5<alpha and 5*alpha^2<1, G=I-alpha*C=(G^2+(1-5*alpha^2)*I)/2 is strictly positive, while every absolute Schur row and column sum is 5*alpha>1.',
        'conclusion':'Absolute Gershgorin/Schur row dominance is NOT necessary for negative definiteness',
        'does_not_imply':['AEGIS actual Weil Gram positivity','Riemann hypothesis','kernel-verified theorem']}
resultfile=Path(__file__).with_name('EXACT_CERTIFICATE.json')
resultfile.write_text(json.dumps(result,indent=2)+'\n')
print('PASS: C^2=5I, -A = 1/2*(-A)^2 + 11/32 I, all 6 absolute row ratios=5/4>1')
