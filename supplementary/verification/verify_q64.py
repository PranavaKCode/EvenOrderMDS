"""Lighter run of verify_capacity over GF(64) for selected values of t.

The Hilbert function is computed only in the two critical degrees d-1, d,
the space-envelope check is omitted, and the divisibility test C | Phi
(which needs ~10^7 point evaluations here) is skipped.
"""
import json
import os
import random
import sys
import time

from arcs import apply, random_matrix, regular_hyperoval, space_curve_lift
from gf2m import GF
from verify_capacity import RESULTS, check_plane_instance


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    rng = random.Random(seed)
    F = GF(6)
    q = F.q
    out = []
    for t in [1, 2, 3, 4, 8, 12, 16, 24, 30]:
        M = q + 2 - t
        cases = [("regular", rng.sample(regular_hyperoval(F), M), None)]
        if t >= 2:
            for h in (1, 5):
                plane, hts = space_curve_lift(F, h, rng.sample(list(F.elements()), M))
                cases.append(("lift(2^%d)" % h, plane, hts))
        for fam, arc, hts in cases:
            A = random_matrix(F, 3, rng)
            arc = [apply(F, A, v) for v in arc]
            t0 = time.time()
            r = check_plane_instance(F, arc, t, hts, full_hilbert=False,
                                     space_check=False, divisibility=False)
            r["family"] = fam
            out.append(r)
            flags = [k for k, v in r.items() if v is False]
            print("q=64 t=%2d M=%2d %-12s dimH=%s bound=%d dimJd=%s %.0fs %s" % (
                t, M, fam, r.get("dimH"), t + 2, r.get("dimJd"),
                time.time() - t0, "FAIL:" + ",".join(flags) if flags else "ok"),
                flush=True)
    with open(os.path.join(RESULTS, "capacity_checks_q64_seed%d.json" % seed), "w") as fh:
        json.dump(out, fh, indent=1)
    print("instances:", len(out), "failed:",
          sum(1 for r in out if any(v is False for v in r.values())))


if __name__ == "__main__":
    main()
