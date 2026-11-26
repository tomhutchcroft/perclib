#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Rational comparisons in YT0O, E5ZR and 9TAI; analytic inputs are proved in the wiki."""
from fractions import Fraction as F
from math import factorial
import json

d = 10**11
q = 2*d
j = F(1001, 1000)
u = F(1, 10**6)
assert F(189, d) < u
assert j/q < u and F(1, q) < u
assert j/(1-u) < F(501, 500)

# e: retain the terms through 1/5!, then dominate the tail from 1/6!.
e_upper = sum(F(1, factorial(k)) for k in range(6))
e_upper += F(1, factorial(6))/(1-F(1, 7))
assert e_upper < F(87, 32)
assert F(87, 32)*F(500, 499) < F(30, 11)

# The coefficient bracket is positive before multiplying by j_c>=1.
kappa_lower = F(11, 60)*(1-u)*((1-u)**2-u)-2*u
assert kappa_lower > F(2, 11)
assert 1+j/(1-u) < 3
assert sum(F(1, factorial(k)) for k in range(5)) > F(8, 3)
assert 12 < F(7, 2)**2
assert 36*F(87, 32)*F(7, 2) < 360
assert F(7, 2)/(1-F(3, 8)) < 6
assert (j+1)/q < F(1, 2) and j+1 < 3

# Uniform subcritical moment and cutoff constants.
assert F(2)/(1-u) < 3
assert F(1, 2)*(1-u)**2 > F(1, 3)
alpha = F(1, 3)
assert 24/alpha**2 == 216
assert alpha**4/576 == F(1, 46656)
assert F(1, 46656)/3 == F(1, 139968)
assert 6/(1-F(1, 4)) == 8
print(json.dumps({"result": "passed", "arithmetic": "exact rational",
                  "dimension_at_least": d, "triangle_upper": str(F(189, d)),
                  "kappa_lower_above": "2/11",
                  "critical_tail_constants": ["1/360", "6"],
                  "density_constants": ["1/3", "24"],
                  "second_moment_lower": "1/3",
                  "subcritical_tail_constants": ["1/139968", "8"],
                  "lower_tail_cutoff_multiple": "1/6"}, indent=2))
