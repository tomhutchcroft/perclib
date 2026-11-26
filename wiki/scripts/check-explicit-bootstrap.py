#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Exact arithmetic for NOTF, 66SP and 7GNW; the analytic estimates are in the wiki."""
from fractions import Fraction as F
from math import comb
import json

# LKS9: certify I_(40,6) from returns through length 128 and an upper tail.
M = 64
counts = [1] + [0] * M
weights = [[comb(2*m, 2*k) * comb(2*k, k) for k in range(m+1)]
           for m in range(M+1)]
for d in range(1, 41):
    counts = [sum(weights[m][k] * counts[m-k] for k in range(m+1))
              for m in range(M+1)]
    assert F(counts[2], (2*d)**4) == F(3*(2*d-1), 8*d**3)
    if d in (1, 2):
        assert all(counts[m] == comb(2*m, m)**d for m in range(M+1))
partial = sum(F(comb(2*m+5, 5) * counts[m], 80**(2*m))
              for m in range(M+1))
tail = (F(8, 15) * F(22*40, 7*16)**20
        * (1 + F(5, 2*(M+1)))**5 * F(M)**(-14) / 14)
I = F(669, 500)
assert partial + tail < I
assert I < F(6, 5)**2 and I < F(6, 5)**3
assert F(3, 4)*I < F(11, 10)**2

# NOTF: retain the constants in the triangle, pair and H estimates.
assert 1 + 4*(2+4+8)*F(11, 10) < 63
assert 2 + 16*F(11, 10) + 300*16*F(11, 10) < 5300
assert 16*301*F(6, 5) < 5800
assert 300*2**10*F(6, 5)**2*F(11, 10) < 487000

# 66SP: each bound is monotone in 1/d, so check d=14000.
d = 14000
assert F(63, d) <= F(1, 100)
assert 1 + F(189, 2*d) <= F(11, 10)
assert 2*63*F(11, 10) <= 140
r = F(1, 100)
assert (10-9*r+3*r*r)/(1-r)**3 <= 11
assert (5-r)/(1-r)**3 <= 6
assert 63 + F(154)/(1-r) < 220
low = 2*5300 + 16*63*F(11, 10)*5800
total = low + 25520*11*140 + 6*F(121, 100)*(3654+487000)
assert low == 6441640
assert total == F(1232614701, 25) < 50000000

# 7GNW: the rational majorant replaces 2 sqrt(vs) by v+s.
dimension = 10**11
epsilon = F(50000000, dimension)
assert dimension >= 14000 and epsilon == F(1, 2000)
s = (1+2*epsilon)**2
v = (1+2*epsilon)*(1+epsilon)
t = (1+84*epsilon)/(1-epsilon)
f3 = (2*epsilon*t + epsilon*(v+s)*t**2
      + 16*(1+epsilon)*s*s*t**3)/200
assert f3 < F(1, 10)
assert 1+84*epsilon == F(521, 500) < F(21, 20) < 2
assert 1+2*epsilon == F(1001, 1000) < F(21, 20)
assert (1-epsilon)/(1+84*epsilon) == F(1999, 2084)
print(json.dumps({"result": "passed", "arithmetic": "exact rational",
                  "dimension_at_least": dimension, "epsilon_at_most": str(epsilon),
                  "coefficient_weight_constant": str(total),
                  "infrared_amplitude_at_most": "521/500",
                  "j_c_at_most": "1001/1000", "f3_upper": "1/10",
                  "critical_gap_at_least": "1999/2084"}, indent=2))
