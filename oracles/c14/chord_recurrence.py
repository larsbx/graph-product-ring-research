#!/usr/bin/env python3
"""Independent literature oracle for maximal-coordinate C_(2k) symbols.

OEIS A000699 / connected chord diagrams:
  a(0) = a(1) = 1
  a(k) = (k-1) * sum(a(i)*a(k-i), i=1..k-1)

The correspondence between maximal-support simple 2k-cube cycles and
connected chord diagrams is a mathematical bridge, not presumed as an
independent empirical count without proving the pairing/avoidance bijection.
"""
from fractions import Fraction
from math import comb, factorial

# Independent lower-coordinate pattern counts for length 14 from oracle B.
P = {4: 392, 5: 33530, 6: 89782, 7: 38232}
a = [1, 1]
for k in range(2, 11):
    a.append((k-1) * sum(a[i]*a[k-i] for i in range(1, k)))
assert [a[k] for k in range(2, 8)] == [1, 4, 27, 248, 2830, 38232]
assert a[7] == P[7], (a[7], P[7])

cycles = {}
for n in range(4, 8):
    s_n = sum(comb(n,k) * factorial(k) * p for k,p in P.items() if k<=n)
    count=Fraction((1<<n)*s_n, 28)
    assert count.denominator==1
    cycles[n]=int(count)

sigma=sum((-1)**(7-j)*comb(7,j)*Fraction(cycles.get(j,0),2**j) for j in range(8))*128
assert sigma == Fraction(2**7*factorial(7)*a[7],28)
assert sigma>0
assert cycles[7]==3337213440
legacy=406517760
legacy_sigma=sigma+legacy-cycles[7]
assert legacy_sigma==-2049830400
beta_primitive=2036229120 # from the historical manuscript, not independently recomputed
corrected_deficit=beta_primitive-2*sigma
print('connected_chord_a_2_to_10:', [a[k] for k in range(2,11)])
print('pattern_counts:', P)
print('cycle_counts_Q4_to_Q7:',cycles)
print('corrected_sigma7:',int(sigma))
print('legacy_sigma7:',int(legacy_sigma))
print('corrected_deficit7_if_primitive_symbol_valid:',int(corrected_deficit))
print('PASS: exact rational / recurrence / historical contradiction')
