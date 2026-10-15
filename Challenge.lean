module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Algebra.Group.Even

public section

/-!
# The MDS conjecture over finite fields of even order

A *linear code* of length `N` over a field `K` is a `K`-subspace `C ⊆ K^N`; its
*dimension* is `Module.finrank K C`. The *Hamming weight* of a word is the number
of its nonzero coordinates (Mathlib's `hammingNorm`), and the *minimum distance*
of a nonzero code is the least weight of a nonzero codeword. Every
`k`-dimensional code of length `N` satisfies the Singleton bound
`d ≤ N - k + 1`; the code is *maximum distance separable* (MDS) when equality
holds, i.e. when every `k` coordinates determine a codeword.

The MDS conjecture, which goes back to a 1955 question of B. Segre (see
MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 11, and the
survey of S. Ball and M. Lavrauw, *Arcs in finite projective spaces*, EMS Surv.
Math. Sci. 6 (2019)), predicts that for `2 ≤ k ≤ q` the maximum length of a
`k`-dimensional linear MDS code over the field with `q` elements is `q + 1`,
except that it is `q + 2` when `q` is even and `k ∈ {3, q - 1}`. S. Ball proved
the conjecture for prime fields (J. Eur. Math. Soc. 14 (2012)).

`EvenOrderMDS.maximum_length_of_MDS_code` states the conjecture, in exactly this
form, for every finite field of even order: for `2 ≤ k ≤ q`, the set of lengths
`N` of `k`-dimensional linear MDS codes `C ⊆ K^N` has greatest element `q + 2`
if `k = 3` or `k = q - 1`, and `q + 1` otherwise. In particular the maximum is
attained, and no longer `k`-dimensional linear MDS code exists.
-/

namespace EvenOrderMDS

/-- The linear code `C ⊆ K^N` has minimum distance `d`: every nonzero codeword has
Hamming weight (number of nonzero coordinates, Mathlib's `hammingNorm`) at least
`d`, and some nonzero codeword has weight exactly `d`. In particular the zero code
has no minimum distance. -/
def HasMinimumDistance {K : Type*} [Field K] {N : ℕ} (C : Submodule K (Fin N → K))
    (d : ℕ) : Prop :=
  open Classical in
  (∀ v ∈ C, v ≠ 0 → d ≤ hammingNorm v) ∧ ∃ v ∈ C, v ≠ 0 ∧ hammingNorm v = d

/-- The linear code `C ⊆ K^N` is *maximum distance separable* (MDS): its minimum
distance is `N - dim C + 1`, the largest value allowed by the Singleton bound. -/
def IsMDS {K : Type*} [Field K] {N : ℕ} (C : Submodule K (Fin N → K)) : Prop :=
  HasMinimumDistance C (N - Module.finrank K C + 1)

/-- **The MDS conjecture over finite fields of even order.** Let `K` be a finite
field with an even number `q` of elements, and let `2 ≤ k ≤ q`. The largest `N`
for which some `k`-dimensional subspace `C ⊆ K^N` is an MDS code is `q + 2` when
`k = 3` or `k = q - 1`, and `q + 1` otherwise. -/
theorem maximum_length_of_MDS_code (K : Type*) [Field K] [Fintype K]
    (hq : Even (Fintype.card K)) (k : ℕ) (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    IsGreatest {N : ℕ | ∃ C : Submodule K (Fin N → K), Module.finrank K C = k ∧ IsMDS C}
      (if k = 3 ∨ k = Fintype.card K - 1 then Fintype.card K + 2
        else Fintype.card K + 1) := by
  sorry

end EvenOrderMDS
