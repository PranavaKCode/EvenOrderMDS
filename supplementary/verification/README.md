# Supplementary computer checks (Python)

These programs back up the informal argument in `docs/report.pdf` (Section 8).
They are not part of the Lean proof. They use exact arithmetic in GF(2^e)
(log tables and Gaussian elimination), with no floating point.

| Program | What it does |
|---|---|
| `arc_search.py` | Exhaustive search for the largest arc in GF(q)^k, q = 2, 4, 8, all 2 ≤ k ≤ q |
| `verify_capacity.py` | Follows the proof step by step on explicit plane arcs over GF(8), GF(16) and GF(32): normalized envelope, the identity CF = H_q + S², compatible heights, the obstruction, the colon-ideal rank sequence, and lifts |
| `verify_q64.py` | A lighter version of the same checks over GF(64) |

`arc_search.json` and `capacity_checks.json` are the recorded outputs: 11 exhaustive
searches and 250 plane arcs, with no failed check. They need Python 3 and NumPy, for
example `python verify_capacity.py 5 2026 3`.

These programs were written by an AI agent (Claude Opus 5.5) and are recorded under
`automation` in `formalization.yaml`.
