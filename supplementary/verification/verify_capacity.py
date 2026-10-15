"""Computer check of each step of the common-height argument.

For a plane arc a_1..a_M in GF(q)^3 with M + t = q + 2 (q = 2n), the
programme computes, by exact linear algebra over GF(q):

  1. the normalized envelope F (solving C_ij(p_ij) F(p_ij) = 1 for all pairs)
     and whether it exists and is unique;
  2. whether CF + H_q is a perfect square (the "highest identity");
  3. the space V of compatible pairs (h, Q), the height space H, and whether
     dim H <= t + 2; whether the three coordinate rows lie in H;
  4. the obstruction Phi = sqrt(D P), whether C divides Phi, and the
     dimensions of the image and kernel of the obstruction map;
  5. the rank sequence h_j of the "top-coefficient pairing" for C, and
     whether it is symmetric, rises up to the middle, vanishes below degree
     d = t - 2, and gives dim J_d <= d + 1;
  6. for arcs with a known lift: that the lift really is a 4-dimensional arc,
     that its height vector lies in H, and (for q <= 16) the space envelope
     G, its restriction G(X,0) = F, and the identities prod_{j!=i} d_j (P4)
     = X_i^q.

Usage:  python verify_capacity.py [max_e] [seed]
"""
import json
import os
import random
import sys
import time
from itertools import combinations
from math import comb, gcd

import numpy as np

import poly3 as P
from arcs import (apply, is_arc, random_matrix, random_plane_arc,
                  regular_hyperoval, space_curve_lift, translation_hyperoval)
from gf2m import GF, det
from linalg_gf import nullspace, rank, solve

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(os.path.dirname(HERE), "results")


def dot(F, a, b):
    s = 0
    for x, y in zip(a, b):
        s ^= F.mul(x, y)
    return s


def cross(F, a, b):
    # In characteristic two the signs in the cross product disappear.
    return (F.mul(a[1], b[2]) ^ F.mul(a[2], b[1]),
            F.mul(a[2], b[0]) ^ F.mul(a[0], b[2]),
            F.mul(a[0], b[1]) ^ F.mul(a[1], b[0]))


def mono_value(F, m, x):
    v = 1
    for xi, ei in zip(x, m):
        if ei:
            v = F.mul(v, F.pow(xi, ei))
    return v


def line_points(F, a):
    """All q+1 projective points on the line {x : a.x = 0} in PG(2,q)."""
    pts = []
    for x in [(1, u, v) for u in F.elements() for v in F.elements()] + \
             [(0, 1, v) for v in F.elements()] + [(0, 0, 1)]:
        if dot(F, a, x) == 0:
            pts.append(x)
    assert len(pts) == F.q + 1
    return pts


def check_plane_instance(F, arc, t, lift=None, full_hilbert=True,
                         space_check=True, divisibility=True):
    q = F.q
    n = q // 2
    M = len(arc)
    assert M + t == q + 2
    out = {"q": q, "t": t, "M": M}
    out["is_arc"] = is_arc(F, arc, 3)
    ells = [P.linear(a) for a in arc]
    C = P.product(F, ells, 3)
    Ci = [P.product(F, [ells[j] for j in range(M) if j != i], 3)
          for i in range(M)]

    # ---- 1. normalized envelope -------------------------------------
    mons_t = P.monomials(3, t)
    rows, rhs = [], []
    nodes = {}
    for i, j in combinations(range(M), 2):
        p = cross(F, arc[i], arc[j])
        nodes[(i, j)] = p
        c = 1
        for k in range(M):
            if k != i and k != j:
                c = F.mul(c, dot(F, arc[k], p))
        rows.append([F.mul(c, mono_value(F, m, p)) for m in mons_t])
        rhs.append(1)
    x, unique = solve(F, rows, rhs)
    out["envelope_exists"] = x is not None
    out["envelope_unique"] = bool(unique)
    if x is None:
        return out
    Fenv = {m: int(c) for m, c in zip(mons_t, x) if c}

    # ---- 2. highest identity CF = H_q + S^2 --------------------------
    CF = P.mul(F, C, Fenv)
    Hq = {(q, 1, 1): 1, (1, q, 1): 1, (1, 1, q): 1}
    out["highest_identity"] = P.is_square(P.add(CF, Hq))

    # ---- 3. compatible pairs V and heights H -------------------------
    odd = [m for m in P.monomials(3, q + 1) if all(e % 2 for e in m)]
    oidx = {m: r for r, m in enumerate(odd)}
    mons_q = P.monomials(3, t - 1)
    cols = []
    col_polys = []
    for i in range(M):
        poly = P.mul(F, Fenv, Ci[i])
        col_polys.append(poly)
    for m in mons_q:
        col_polys.append({tuple(a + b for a, b in zip(mc, m)): c
                          for mc, c in C.items()})
    A = np.zeros((len(odd), len(col_polys)), dtype=np.int64)
    for cidx, poly in enumerate(col_polys):
        for m, c in poly.items():
            r = oidx.get(m)
            if r is not None:
                A[r, cidx] ^= c
    Vb = nullspace(F, A, len(col_polys))
    dimV = Vb.shape[0]
    dimH = rank(F, Vb[:, :M]) if dimV else 0
    out["dimV"], out["dimH"], out["bound"] = dimV, dimH, t + 2
    out["capacity_ok"] = dimH <= t + 2
    shears_in = True
    base_rank = dimH
    for coord in range(3):
        h = np.array([a[coord] for a in arc], dtype=np.int64)
        if rank(F, np.vstack([Vb[:, :M], h])) != base_rank:
            shears_in = False
    out["coordinate_rows_in_H"] = shears_in

    # ---- 4. obstruction map ------------------------------------------
    mons_2n = P.monomials(3, 2 * n)
    midx = {m: r for r, m in enumerate(mons_2n)}
    # points on all old lines, for the divisibility test (deg 2n < q+1 points)
    MV = None
    if divisibility:
        pts = []
        for a in arc:
            pts.extend(line_points(F, a))
        MV = np.array([[mono_value(F, m, p) for m in mons_2n] for p in pts],
                      dtype=np.int64)
    phis = []
    all_one_odd = True
    all_divisible = True
    for v in Vb:
        poly = {}
        for cidx, coef in enumerate(v):
            if coef:
                poly = P.add(poly, P.scale(F, col_polys[cidx], int(coef)))
        # every monomial of a compatible P has exactly one odd exponent
        if any(sum(e % 2 for e in m) != 1 for m in poly):
            all_one_odd = False
        DP = {}
        for j in range(3):
            dj = P.deriv(poly, j)
            sh = [0, 0, 0]
            sh[j] = q
            DP = P.add(DP, {tuple(a + b for a, b in zip(m, sh)): c
                            for m, c in dj.items()})
        if not P.is_square(DP):
            all_one_odd = False
        phi = {tuple(e // 2 for e in m): int(F.SQRT[c]) for m, c in DP.items()}
        vec = np.zeros(len(mons_2n), dtype=np.int64)
        for m, c in phi.items():
            vec[midx[m]] = c
        if MV is not None:
            vals = np.bitwise_xor.reduce(F.MUL[vec[None, :], MV], axis=1)
            if np.any(vals):
                all_divisible = False
        phis.append(vec)
    out["parity_form_ok"] = all_one_odd
    out["C_divides_Phi"] = all_divisible if divisibility else "not run"
    imL = rank(F, np.array(phis)) if phis else 0
    out["image_dim"], out["kernel_dim"] = imL, dimV - imL

    # ---- 5. top-coefficient pairing / colon dimensions ---------------
    d = t - 2
    if d >= 0:
        s = n + d - 3
        out["d"], out["s"] = d, s
        js = range(0, s + 1) if full_hilbert else sorted({max(d - 1, 0), d})
        hvals = {}
        for j in js:
            colm = P.monomials(3, j)
            rowm = [m for m in P.monomials(3, M + j) if max(m) < n]
            ridx = {m: r for r, m in enumerate(rowm)}
            B = np.zeros((len(rowm), len(colm)), dtype=np.int64)
            for cidx, u in enumerate(colm):
                for mc, c in C.items():
                    r = ridx.get((mc[0] + u[0], mc[1] + u[1], mc[2] + u[2]))
                    if r is not None:
                        B[r, cidx] ^= c
            hvals[j] = rank(F, B) if len(rowm) else 0
        dimJd = comb(d + 2, 2) - hvals[d]
        out["dimJd"] = dimJd
        out["colon_ok"] = dimJd <= d + 1
        out["image_le_colon"] = imL <= dimJd
        out["no_early"] = all(hvals[j] == comb(j + 2, 2)
                              for j in hvals if j < d)
        if full_hilbert:
            h = [hvals[j] for j in range(s + 1)]
            out["hilbert"] = h
            out["symmetric"] = all(h[j] == h[s - j] for j in range(s + 1))
            out["rises_to_middle"] = all(h[j - 1] <= h[j]
                                         for j in range(1, s // 2 + 1))
    else:
        out["image_le_colon"] = imL == 0

    # ---- 6. actual lifts -----------------------------------------------
    if lift is not None:
        heights = lift
        lifted = [(0, 0, 0, 1)] + [tuple(a) + (hh,) for a, hh in zip(arc, heights)]
        out["lift_is_arc"] = is_arc(F, lifted, 4)
        hv = np.array(heights, dtype=np.int64)
        out["lift_in_H"] = rank(F, np.vstack([Vb[:, :M], hv])) == dimH
        if space_check:
            out.update(check_space(F, arc, heights, t, Fenv, C))
    return out


def check_space(F, arc, heights, t, Fenv, C):
    q = F.q
    pts = [(0, 0, 0, 1)] + [tuple(a) + (hh,) for a, hh in zip(arc, heights)]
    A = len(pts)
    mons = P.monomials(4, t)
    rows, rhs = [], []
    for S in combinations(range(A), 3):
        b = [pts[i] for i in S]
        p = tuple(det(F, [[r[c] for c in range(4) if c != i] for r in b])
                  for i in range(4))
        c = 1
        for l in range(A):
            if l not in S:
                c = F.mul(c, dot(F, pts[l], p))
        rows.append([F.mul(c, mono_value(F, m, p)) for m in mons])
        rhs.append(1)
    x, unique = solve(F, rows, rhs)
    res = {"space_envelope_exists": x is not None,
           "space_envelope_unique": bool(unique)}
    if x is None:
        return res
    G = {m: int(c) for m, c in zip(mons, x) if c}
    res["restriction_equals_F"] = P.restrict_last(G) == Fenv
    P4 = P.product(F, [P.linear(b) for b in pts], 4)
    P4 = P.mul(F, P4, G)
    ok = True
    for i in range(4):
        D = P4
        for j in range(4):
            if j != i:
                D = P.deriv(D, j)
        target = [0, 0, 0, 0]
        target[i] = q
        if D != {tuple(target): 1}:
            ok = False
    res["space_highest_identity"] = ok
    return res


def instances(F, rng, per_family):
    """Yield (family, arc, t, lift) test cases for the field F."""
    q = F.q
    n = q // 2
    hyper = {"regular": regular_hyperoval(F)}
    for h in range(2, F.e // 2 + 1):
        if gcd(h, F.e) == 1:
            hyper["translation(2^%d)" % h] = translation_hyperoval(F, h)
    lift_exps = [h for h in range(1, F.e) if gcd(h, F.e) == 1]
    for t in range(1, n + 1):
        M = q + 2 - t
        for name, H in hyper.items():
            for _ in range(per_family):
                sub = rng.sample(H, M)
                Amat = random_matrix(F, 3, rng)
                yield name, [apply(F, Amat, v) for v in sub], t, None
        for _ in range(per_family):
            arc = random_plane_arc(F, M, rng, tries=30)
            if arc is not None:
                yield "random", arc, t, None
        if t >= 2:
            for h in lift_exps:
                for _ in range(per_family):
                    params = rng.sample(list(F.elements()), M)
                    plane, hts = space_curve_lift(F, h, params)
                    Amat = random_matrix(F, 3, rng)
                    plane = [apply(F, Amat, v) for v in plane]
                    yield "lift(2^%d)" % h, plane, t, hts


def main():
    max_e = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 2026
    per = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    rng = random.Random(seed)
    os.makedirs(RESULTS, exist_ok=True)
    allres = []
    for e in range(3, max_e + 1):
        F = GF(e)
        t0 = time.time()
        for fam, arc, t, lift in instances(F, rng, per if e < 5 else 1):
            r = check_plane_instance(F, arc, t, lift,
                                     full_hilbert=(e <= 5),
                                     space_check=(e <= 4))
            r["family"] = fam
            allres.append(r)
            flags = [k for k, v in r.items() if v is False]
            print("q=%2d t=%2d M=%2d %-18s dimH=%s bound=%d dimJd=%s %s" % (
                F.q, t, r["M"], fam, r.get("dimH"), t + 2, r.get("dimJd"),
                "FAIL:" + ",".join(flags) if flags else "ok"), flush=True)
        print("q=%d done in %.1fs" % (F.q, time.time() - t0), flush=True)
    path = os.path.join(RESULTS, "capacity_checks_seed%d.json" % seed)
    with open(path, "w") as fh:
        json.dump(allres, fh, indent=1)
    nfail = sum(1 for r in allres if any(v is False for v in r.values()))
    print("instances:", len(allres), "with a failed check:", nfail)


if __name__ == "__main__":
    main()
