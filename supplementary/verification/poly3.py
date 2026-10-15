"""Homogeneous polynomials over GF(2^e) in 3 or 4 variables.

A homogeneous polynomial of degree d is stored as a dict mapping exponent
tuples (summing to d) to nonzero field elements.  The dict form keeps the
code short and transparent; the sizes in our experiments are small enough.
"""
from itertools import combinations_with_replacement
from math import comb


def monomials(nvars, d):
    """All exponent tuples of total degree d in nvars variables (fixed order)."""
    if d < 0:
        return []
    out = []
    for c in combinations_with_replacement(range(nvars), d):
        e = [0] * nvars
        for i in c:
            e[i] += 1
        out.append(tuple(e))
    out.sort(reverse=True)
    assert len(out) == comb(d + nvars - 1, nvars - 1)
    return out


def add(P, Q):
    R = dict(P)
    for m, c in Q.items():
        v = R.get(m, 0) ^ c
        if v:
            R[m] = v
        else:
            R.pop(m, None)
    return R


def scale(F, P, c):
    if c == 0:
        return {}
    return {m: F.mul(v, c) for m, v in P.items()}


def mul(F, P, Q):
    R = {}
    for m1, c1 in P.items():
        for m2, c2 in Q.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            v = R.get(m, 0) ^ F.mul(c1, c2)
            if v:
                R[m] = v
            else:
                R.pop(m, None)
    return R


def linear(vec):
    """The linear form vec . X."""
    n = len(vec)
    P = {}
    for i, c in enumerate(vec):
        if c:
            e = [0] * n
            e[i] = 1
            P[tuple(e)] = c
    return P


def product(F, polys, nvars):
    R = {tuple([0] * nvars): 1}
    for P in polys:
        R = mul(F, R, P)
    return R


def evaluate(F, P, x):
    total = 0
    for m, c in P.items():
        v = c
        for xi, ei in zip(x, m):
            v = F.mul(v, F.pow(xi, ei))
        total ^= v
    return total


def deriv(P, i):
    """Partial derivative with respect to variable i (characteristic two)."""
    R = {}
    for m, c in P.items():
        if m[i] % 2 == 1:  # m[i] * X^(m[i]-1); the integer m[i] is odd
            e = list(m)
            e[i] -= 1
            R[tuple(e)] = R.get(tuple(e), 0) ^ c
    return {m: c for m, c in R.items() if c}


def restrict_last(P, value_zero=True):
    """P with the last variable set to 0, as a polynomial in the others."""
    return {m[:-1]: c for m, c in P.items() if m[-1] == 0}


def is_square(P):
    """In characteristic two a polynomial is a square iff all exponents are even."""
    return all(all(e % 2 == 0 for e in m) for m in P)


def degree_of(P):
    if not P:
        return None
    return sum(next(iter(P)))
