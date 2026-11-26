#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Exact rational certificates for LKS9 and NI0W; no floating-point arithmetic."""
from fractions import Fraction as F
from math import comb
import json

M = 64
rows = {
    40: (F(21, 20), F(669, 500), F(13589, 100000000), F(407, 500)),
    64: (F(11, 10), F(1191, 1000), F(387, 20000000), F(37, 50)),
    100: (F(23, 20), F(279, 250), F(363, 100000000), F(181, 250)),
}
weights = [
    [comb(2*m, 2*k) * comb(2*k, k) for k in range(m+1)]
    for m in range(M+4)
]
counts = [1] + [0] * (M+3)
certificates = []
for d in range(1, max(rows)+1):
    counts = [
        sum(weights[m][k] * counts[m-k] for k in range(m+1))
        for m in range(M+4)
    ]
    if d in (1, 2):
        assert all(counts[m] == comb(2*m, m)**d for m in range(M+4))
    if d not in rows:
        continue
    p = [F(counts[m], (2*d)**(2*m)) for m in range(M+4)]
    partial_I = sum(F(comb(2*m+5, 5)) * p[m] for m in range(M+1))
    partial_J = sum(F(comb(2*m+5, 5)) * p[m+3] for m in range(M+1))
    # LKS9, with the strict rational upper bound pi < 22/7.
    tail = (F(8, 15) * F(22*d, 7*16)**(d//2)
            * (1 + F(5, 2*(M+1)))**5
            * F(M)**(6-d//2) / F(d//2-6))
    c, upper_I, upper_J, upper_rho = rows[d]
    assert d % 2 == 0 and d > 12
    assert partial_I + tail < upper_I
    assert partial_J + tail < upper_J
    assert 64 * c**42 * upper_I**5 * upper_J < upper_rho**6 < 1
    certificates.append({
        "dimension_at_least": d, "amplitude_and_j_at_most": str(c),
        "I_upper": str(upper_I), "J_upper": str(upper_J),
        "rho_upper": str(upper_rho), "result": "passed",
    })
print(json.dumps({"cutoff": M, "arithmetic": "exact rational",
                  "certificates": certificates}, indent=2))
