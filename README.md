# The MDS conjecture over finite fields of even order

This repository contains a Lean 4 proof, checked against Mathlib, of the
linear MDS conjecture for every finite field of even order:

> Let `K` be a finite field with an even number `q` of elements and let
> `2 ≤ k ≤ q`. The maximum length of a `k`-dimensional linear maximum distance
> separable (MDS) code over `K` is `q + 2` if `k = 3` or `k = q − 1`, and
> `q + 1` otherwise.

The advertised statement is `EvenOrderMDS.maximum_length_of_MDS_code` in
[`Challenge.lean`](Challenge.lean). [`Solution.lean`](Solution.lean) proves the
same declaration, and [`comparator.json`](comparator.json) tells
[Comparator](https://github.com/leanprover/comparator) to check that the two
agree and that the proof uses only `propext`, `Quot.sound` and
`Classical.choice`. Running `scripts/verify-comparator.sh` locally, the proof is
accepted by Lean's kernel and by the two independent kernels bundled with the
toolchain, NanoDa and con-ron.

## The statement

A linear code of length `N` over `K` is a subspace `C ⊆ K^N`, and its dimension
is `Module.finrank K C`. The Hamming weight of a word is its number of nonzero
coordinates (Mathlib's `hammingNorm`). `C` has minimum distance `d` if every
nonzero codeword has weight at least `d` and some nonzero codeword has weight
exactly `d`. Every `k`-dimensional code satisfies the Singleton bound
`d ≤ N − k + 1`, and `C` is MDS when equality holds. Equivalently, every `k`
coordinates of a codeword determine it, which is why MDS codes give optimal
protection against erasures.

`maximum_length_of_MDS_code` asserts that the set of lengths `N` for which some
`k`-dimensional subspace of `K^N` is an MDS code has greatest element
`q + 2` (when `k ∈ {3, q − 1}`) or `q + 1` (otherwise). It uses Mathlib's
`IsGreatest`, so the single theorem contains both halves of the claim:

* **attainment:** a `k`-dimensional MDS code of that length exists;
* **upper bound:** every `k`-dimensional MDS code is no longer.

The only definitions in the Challenge are `HasMinimumDistance` and `IsMDS`.
Each has a docstring and the meaning just described.

### Comparison with the standard conjecture

The MDS conjecture goes back to a 1955 question of B. Segre about the largest
size of an arc in a finite projective space. S. Ball states it as follows
(*J. Eur. Math. Soc.* 14 (2012), Conjecture 1.4, citing Segre and
MacWilliams–Sloane): a set of vectors of `F_q^k` in which every subset of size
`k ≤ q` is a basis has at most `q + 1` elements, unless `q` is even and
`k ∈ {3, q − 1}`, in which case it has at most `q + 2`. The columns of a
generator matrix of a linear `[N, k]` code form such a set exactly when the
code is MDS, so this is the same as the coding formulation in MacWilliams and
Sloane, *The Theory of Error-Correcting Codes*, Ch. 11.

The Lean statement covers the even-`q` case of this conjecture in the coding
formulation. It adds no hypotheses and keeps the full range `2 ≤ k ≤ q`.
Because it states the exact maximum, it also includes the two exceptional
dimensions, where length `q + 2` is attained.

* **Codes:** they are literal subspaces of `Fin N → K`. Length and dimension are
  the natural numbers `N` and `Module.finrank K C`, and minimum distance is an
  attained minimum, so the zero code is never MDS.
* **Field order:** "even order" is stated as `Even (Fintype.card K)`, which is
  equivalent to characteristic two.
* **Scope:** dimensions outside `2 ≤ k ≤ q` are elementary. For `k > q` the
  maximum length is `k + 1` (Bush 1952), and for `k = 1` lengths are unbounded.
  These cases are not part of the conjecture and are not stated here.
* **Not claimed:** nothing about fields of odd order, nonlinear codes, or a
  classification of the codes of maximum length.

## Literature

The constructions attaining the bound are classical. Extended Reed–Solomon
codes have length `q + 1` (Reed–Solomon 1960), and for even `q` a conic
together with its nucleus is a plane arc of `q + 2` points (Bose 1947). The
dual of that arc gives length `q + 2` in dimension `q − 1`.

Known results on the upper bound, according to the survey of Ball and Lavrauw
(*Arcs in finite projective spaces*, EMS Surv. Math. Sci. 6 (2019)) and Ball
(2012):

* **Prime fields:** Ball proved the conjecture for every prime `q`, and Ball and
  De Beule extended it to `q = p^h` with `k ≤ 2p − 2`. For `p = 2` these ranges
  contain no new cases.
* **Even `q`:**
  * `k = 4, 5`: Casse 1969;
  * `k = 6`: Casse–Glynn 1984;
  * `k = 7` for `q ≥ 16`: Maruta–Kaneta 1991;
  * `k < ½√q + 15/4`: Storme–Thas 1993, improving Bruen–Thas–Blokhuis 1988;
  * the dual values `q + 2 − k` of all of these.
* **Small fields:** the conjecture was known for all `q ≤ 27` (Hirschfeld–Storme
  2001), and Kéri (2006) classified all arcs for `4 ≤ q ≤ 19`.

In the survey, the even case outside these ranges was open. We are not aware
of a published proof of the full even case. However, we have not done an
exhaustive search of the literature after 2019, so novelty has not been
independently established.

## How the proof works

The Lean proof follows the argument in the accompanying report
([`docs/report.pdf`](docs/report.pdf)). Section 8 of the report lists the
computer checks of the individual lemmas. The report's exposition differs in
places from the formal proof: in particular, it presents the dimension count
for the colon ideal through an elementary rank induction. The architecture of
the Lean development is:

1. **Codes and arcs** (`CodeWeights`, `LinearMDSCode`,
   `CodeGeneratorEquivalence`, `Arc`, `ArcFamilies`, `ArcDuality`): a code is MDS
   exactly when the columns of a generator matrix form an arc. Puncturing and
   duality reduce the upper bound to excluding arcs of `q + 2` vectors in `K^r`
   for `4 ≤ r ≤ q/2 + 1` (`SmallRankArcBounds`, `EndpointReduction`).
2. **Common heights** (`ParentNormalization`, `ParentCoordinateContractions`,
   `ParentCoordinateRank`): choosing `t = r − 3` vectors of such an arc as
   coordinate centres yields one plane arc of `M = q + 2 − t` vectors. Each
   centre gives a lift of that arc to a four-dimensional arc. The three
   coordinate rows and the `t` lift-height rows are `t + 3` linearly
   independent vectors.
3. **Normalized envelope** (`NormalizedPlaneEnvelope`, `NormalizedSpaceEnvelope`
   and their dependencies): the plane arc has a unique exactly normalized
   envelope `F` of degree `t`, a precise form of Segre's envelope of the
   tangents. Moreover `C·F = H_q + S²`, where `C` is the product of the arc's
   linear forms and `H_q = X₀^q X₁ X₂ + X₀ X₁^q X₂ + X₀ X₁ X₂^q`.
4. **Compatibility** (`ActualLiftCompatibility`, `CompatibleSpace`): every lift
   satisfies one fixed linear compatibility system, derived from the envelope of
   the lifted space arc. Its solutions form a space `H` that contains every lift
   height and the three coordinate rows.
5. **Obstruction** (`PolynomialObstruction`, `ColonDivisionMap`,
   `ConcreteShearInjection`): in characteristic two a compatible polynomial has
   the form `Σ X_j B_j²`. Writing `n = q/2`, the polynomial
   `Φ = Σ X_j^n B_j` is divisible by `C`. Dividing by `C` maps `H` modulo a
   three-dimensional space of shears injectively into the degree-`(t − 2)` part
   of the colon ideal `(X₀^n, X₁^n, X₂^n) : C`.
6. **Colon bound** (`StarChartColon`, `PlaneArcColon`, `CriticalColon`,
   `GorensteinUnimodality` and related modules): restricting to the lines of the
   arc shows that the colon ideal has no elements of degree below `t − 2`. The
   symmetry and growth of an Artinian Gorenstein Hilbert function then bound the
   critical component by `t − 1`.
7. **Contradiction and attainment** (`ConcreteHeightBound`,
   `CommonHeightCapacity`, `AllEvenArcUpperBound`, `ExtendedReedSolomon`,
   `HyperovalConstruction`, `AllEvenArcSharp`, `AllEvenLinearMDS`): `H` has
   dimension at most `t + 2`, which contradicts step 2. The classical
   constructions show the bound is attained.

`EndpointReduction.ArcBoundInputs` is an intermediate conditional interface.
The final proof does not assume it: `AllEvenArcUpperBound.actual_arc_inputs`
supplies every field from proved theorems.

## Authorship and production

The mathematical argument was devised by Pranava Kumar, who is the author and
responsible maintainer of this formalization. Claude (Anthropic) assisted him
in translating the proof into Lean 4, producing the original development for
Lean v4.24.0.

The present repository was assembled with the help of an AI agent (Claude
Opus 5.5, in Claude Code). The agent:

* ported the Lean development from Lean v4.24.0 and an October 2025 Mathlib to
  Lean v4.35.0-rc2 and Lean's module system, renaming the package to
  `EvenOrderMDS`;
* wrote `Challenge.lean` and `Solution.lean`;
* drafted this README, `formalization.yaml` and the accompanying report;
* wrote the supplementary Python verification programs.

`formalization.yaml` records these contributions under `automation`. No
independent human expert has yet reviewed the mathematics. The Challenge
statement was audited against the standard formulations of the conjecture, and
Comparator checks that the Lean proof establishes it.

## Building and checking

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # Linux with bubblewrap
(cd docbuild && lake build EvenOrderMDS:docs)
```

The toolchain is `leanprover/lean4:v4.35.0-rc2`, and Mathlib is pinned in
`lake-manifest.json`. The repository is laid out according to the
[Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Palomar submissions are made through <https://submit.palomar-registry.org/>.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE). Cited works and dependencies keep
their own licences.
