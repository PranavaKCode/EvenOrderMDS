"""Constructions and checks for arcs (sets of vectors, every k independent)."""
import random
from itertools import combinations
from math import gcd

from gf2m import det


def is_arc(F, vecs, k=None):
    """True if every k of the vectors are linearly independent."""
    if k is None:
        k = len(vecs[0])
    if len(vecs) < k:
        return all(any(v) for v in vecs)
    return all(det(F, [vecs[i] for i in S]) != 0
               for S in combinations(range(len(vecs)), k))


def regular_hyperoval(F):
    """Conic {(1,s,s^2)} plus its two points at infinity: q+2 points."""
    pts = [(1, s, F.mul(s, s)) for s in F.elements()]
    return pts + [(0, 0, 1), (0, 1, 0)]


def translation_hyperoval(F, h):
    """{(1,s,s^(2^h))} plus (0,0,1),(0,1,0); a hyperoval when gcd(h,e)=1."""
    assert gcd(h, F.e) == 1
    sig = 1 << h
    pts = [(1, s, F.pow(s, sig)) for s in F.elements()]
    return pts + [(0, 0, 1), (0, 1, 0)]


def random_matrix(F, n, rng):
    while True:
        A = [[rng.randrange(F.q) for _ in range(n)] for _ in range(n)]
        if det(F, A):
            return A


def apply(F, A, v):
    out = []
    for row in A:
        s = 0
        for a, x in zip(row, v):
            s ^= F.mul(a, x)
        out.append(s)
    return tuple(out)


def normalize(F, v):
    """Scale a nonzero vector so that its first nonzero entry is 1."""
    for x in v:
        if x:
            inv = F.inv(x)
            return tuple(F.mul(inv, y) for y in v)
    raise ValueError("zero vector")


def plane_points(F):
    pts = [(1, x, y) for x in F.elements() for y in F.elements()]
    pts += [(0, 1, y) for y in F.elements()] + [(0, 0, 1)]
    return pts


def random_plane_arc(F, size, rng, tries=20):
    """Random greedy arc in PG(2,q): add random points off all secant lines.

    Returns None if no arc of the requested size was reached.
    """
    pts = plane_points(F)
    index = {p: i for i, p in enumerate(pts)}

    def line(a, b):
        nrm = (F.mul(a[1], b[2]) ^ F.mul(a[2], b[1]),
               F.mul(a[2], b[0]) ^ F.mul(a[0], b[2]),
               F.mul(a[0], b[1]) ^ F.mul(a[1], b[0]))
        return [i for i, p in enumerate(pts)
                if (F.mul(nrm[0], p[0]) ^ F.mul(nrm[1], p[1])
                    ^ F.mul(nrm[2], p[2])) == 0]

    for _ in range(tries):
        covered = set()
        arc = []
        while len(arc) < size:
            free = [i for i in range(len(pts)) if i not in covered]
            if not free:
                break
            i = rng.choice(free)
            p = pts[i]
            for a in arc:
                covered.update(line(a, p))
            covered.add(i)
            arc.append(p)
        if len(arc) == size:
            return arc
    return None


def space_curve_lift(F, h, params):
    """Points (1,s,s^sigma) with heights s^(sigma+1), sigma = 2^h.

    Together with e4 = (0,0,0,1) the lifted points (1,s,s^sigma,s^(sigma+1))
    lie on a (q+1)-arc of PG(3,q) when gcd(h,e) = 1 (Casse--Glynn); the
    programme re-checks the arc property directly.
    """
    sig = 1 << h
    plane = [(1, s, F.pow(s, sig)) for s in params]
    heights = [F.pow(s, sig + 1) for s in params]
    return plane, heights
