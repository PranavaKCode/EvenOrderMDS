"""Arithmetic in the finite field GF(2^e).

Elements are the integers 0..q-1, read as polynomials over GF(2) in a
primitive element; addition is XOR.  Multiplication uses exponent/log
tables, and a full q-by-q multiplication table (a NumPy array) is kept so
that whole vectors can be multiplied at once.
"""
import numpy as np

# Primitive polynomials over GF(2), written as bit masks (x^e + ... + 1).
PRIMITIVE = {
    1: 0b11,
    2: 0b111,
    3: 0b1011,
    4: 0b10011,
    5: 0b100101,
    6: 0b1000011,
    7: 0b10000011,
    8: 0b100011101,
}


class GF:
    def __init__(self, e):
        self.e = e
        self.q = q = 1 << e
        exp = [0] * (2 * q)
        log = [0] * q
        x = 1
        for i in range(q - 1):
            exp[i] = x
            log[x] = i
            x <<= 1
            if x & q:
                x ^= PRIMITIVE[e]
        for i in range(q - 1, 2 * q):
            exp[i] = exp[i - (q - 1)]
        self.exp, self.log = exp, log
        mul = np.zeros((q, q), dtype=np.int64)
        for a in range(1, q):
            for b in range(1, q):
                mul[a, b] = exp[log[a] + log[b]]
        self.MUL = mul
        self.INV = np.array([0] + [exp[(q - 1 - log[a]) % (q - 1)]
                                   for a in range(1, q)], dtype=np.int64)
        # In characteristic two every element has exactly one square root,
        # namely a^(q/2).
        self.SQRT = np.array([self.pow(a, q // 2) for a in range(q)],
                             dtype=np.int64)

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        if a == 0:
            raise ZeroDivisionError("0 has no inverse")
        return int(self.INV[a])

    def pow(self, a, k):
        if k == 0:
            return 1
        if a == 0:
            return 0
        return self.exp[(self.log[a] * k) % (self.q - 1)]

    def elements(self):
        return range(self.q)

    def nonzero(self):
        return range(1, self.q)


def det(F, rows):
    """Determinant of a square matrix (list of lists) over GF(2^e).

    Gaussian elimination; in characteristic two row swaps do not change the
    sign, so no sign bookkeeping is needed.
    """
    A = [list(r) for r in rows]
    n = len(A)
    d = 1
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c]), None)
        if p is None:
            return 0
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        d = F.mul(d, piv)
        inv = F.inv(piv)
        for r in range(c + 1, n):
            if A[r][c]:
                f = F.mul(A[r][c], inv)
                A[r] = [x ^ F.mul(f, y) for x, y in zip(A[r], A[c])]
    return d
