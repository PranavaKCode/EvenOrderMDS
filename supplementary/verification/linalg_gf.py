"""Exact linear algebra over GF(2^e): row reduction, rank, null space, solve."""
import numpy as np


def rref(F, A):
    """Return (R, pivots): the reduced row echelon form of A and its pivots.

    A is an integer array with entries in 0..q-1.  All arithmetic is exact.
    """
    A = np.array(A, dtype=np.int64, copy=True)
    if A.ndim != 2 or A.size == 0:
        return A, []
    r, c = A.shape
    MUL, INV = F.MUL, F.INV
    pivots = []
    row = 0
    for col in range(c):
        if row >= r:
            break
        nz = np.nonzero(A[row:, col])[0]
        if len(nz) == 0:
            continue
        p = row + nz[0]
        if p != row:
            A[[row, p]] = A[[p, row]]
        A[row] = MUL[INV[A[row, col]]][A[row]]
        colvals = A[:, col].copy()
        colvals[row] = 0
        nzr = np.nonzero(colvals)[0]
        if len(nzr):
            A[nzr] ^= MUL[colvals[nzr][:, None], A[row][None, :]]
        pivots.append(col)
        row += 1
    return A[:row], pivots


def rank(F, A):
    A = np.asarray(A)
    if A.size == 0:
        return 0
    return len(rref(F, A)[1])


def nullspace(F, A, ncols=None):
    """Basis (as rows of an array) of {x : A x = 0}."""
    A = np.asarray(A, dtype=np.int64)
    if ncols is None:
        ncols = A.shape[1]
    if A.size == 0:
        return np.eye(ncols, dtype=np.int64)
    R, piv = rref(F, A)
    free = [j for j in range(ncols) if j not in set(piv)]
    basis = []
    for f in free:
        x = np.zeros(ncols, dtype=np.int64)
        x[f] = 1
        for i, p in enumerate(piv):
            # Row i says x_p + sum_{free} R[i,j] x_j = 0  (char 2: minus = plus)
            x[p] = R[i, f]
        basis.append(x)
    if not basis:
        return np.zeros((0, ncols), dtype=np.int64)
    return np.array(basis, dtype=np.int64)


def solve(F, A, b):
    """Return (x, unique) with A x = b, or (None, False) if inconsistent."""
    A = np.asarray(A, dtype=np.int64)
    b = np.asarray(b, dtype=np.int64).reshape(-1, 1)
    n = A.shape[1]
    R, piv = rref(F, np.hstack([A, b]))
    if n in piv:
        return None, False
    x = np.zeros(n, dtype=np.int64)
    for i, p in enumerate(piv):
        x[p] = R[i, n]
    return x, len(piv) == n
