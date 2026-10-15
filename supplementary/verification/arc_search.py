"""Exhaustive search for the largest arc in PG(k-1, q), q = 2, 4, 8.

An arc of rank k is a set of vectors in GF(q)^k, every k of which are
linearly independent; by the generator-matrix criterion its size is the
length of a k-dimensional MDS code.

Frame reduction.  If an arc has at least k+1 points, a change of
coordinates (an invertible matrix, then rescaling the coordinates) moves k
of its points to e_1..e_k and one more to the all-ones vector.  Any further
point p must then have
  * no zero coordinate (else p and k-1 of the e_i are dependent), and
  * pairwise distinct coordinates after scaling p_1 = 1 (if p_i = p_j, then
    p, the all-ones vector and the k-2 vectors e_l, l != i,j are dependent).
So the candidates are (1, x_2, ..., x_k) with distinct x_i outside {0, 1}.
The search adds candidates in increasing order and keeps only candidates
that remain compatible with every point chosen so far.

Usage:  python arc_search.py
"""
import json
import os
import sys
import time
from itertools import combinations, permutations

from gf2m import GF, det

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(os.path.dirname(HERE), "results")


def predicted(q, k):
    """The value B(q,k) of the main theorem (2 <= k <= q, q even)."""
    return q + 2 if k in (3, q - 1) else q + 1


def max_arc(F, k):
    q = F.q
    frame = [tuple(1 if i == j else 0 for j in range(k)) for i in range(k)]
    frame.append(tuple([1] * k))
    others = [x for x in F.elements() if x not in (0, 1)]
    cands = [(1,) + p for p in permutations(others, k - 1)]
    best = [list(frame)]
    nodes = [0]

    def compatible(arc, p, c):
        # every k-subset containing both p and c must be independent
        for S in combinations(arc, k - 2):
            if det(F, list(S) + [p, c]) == 0:
                return False
        return True

    def extend(arc, cands):
        nodes[0] += 1
        if len(arc) > len(best[0]):
            best[0] = list(arc)
        for idx, p in enumerate(cands):
            if len(arc) + (len(cands) - idx) <= len(best[0]):
                return  # cannot beat the best arc found so far
            rest = [c for c in cands[idx + 1:] if compatible(arc, p, c)]
            extend(arc + [p], rest)

    extend(frame, cands)
    return best[0], len(cands), nodes[0]


def main():
    fields = [int(a) for a in sys.argv[1:]] or [1, 2, 3]
    os.makedirs(RESULTS, exist_ok=True)
    rows = []
    for e in fields:
        F = GF(e)
        q = F.q
        for k in range(2, q + 1):
            t0 = time.time()
            arc, ncand, nodes = max_arc(F, k)
            dt = time.time() - t0
            # independent re-check of the arc found
            ok = all(det(F, [arc[i] for i in S]) != 0
                     for S in combinations(range(len(arc)), k))
            row = {"q": q, "k": k, "max_length": len(arc),
                   "predicted": predicted(q, k), "candidates": ncand,
                   "search_nodes": nodes, "seconds": round(dt, 2),
                   "example_rechecked": ok,
                   "example": [list(v) for v in arc]}
            rows.append(row)
            print("q=%d k=%d max=%d predicted=%d candidates=%d nodes=%d "
                  "time=%.2fs recheck=%s" % (q, k, len(arc), row["predicted"],
                                             ncand, nodes, dt, ok), flush=True)
    with open(os.path.join(RESULTS, "arc_search.json"), "w") as fh:
        json.dump(rows, fh, indent=1)
    print("all match:", all(r["max_length"] == r["predicted"] for r in rows))


if __name__ == "__main__":
    main()
