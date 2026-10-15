module

public import EvenOrderMDS
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Algebra.Group.Even

public section

/-!
# Proof of the advertised statement

The definitions below are copied verbatim from `Challenge.lean`. The main
theorem is deduced from `EvenOrderMDS.AllEvenLinearMDS.maximum_length_of_even_card`,
the endpoint of the proof development, after identifying the Challenge notions
of minimum distance and MDS code with the ones used in the development.
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

/-- Mathlib's Hamming weight agrees with the literal weight of the development. -/
theorem hammingNorm_eq_weight {K : Type*} [Field K] {N : ℕ} (v : Fin N → K) :
    (open Classical in hammingNorm v) = CodeWeights.weight v := by
  classical
  simp only [hammingNorm, CodeWeights.weight, CodeWeights.support]

theorem hasMinimumDistance_iff {K : Type*} [Field K] {N : ℕ} (C : Submodule K (Fin N → K))
    (d : ℕ) : HasMinimumDistance C d ↔ LinearMDSCode.HasMinimumDistance C d := by
  simp only [HasMinimumDistance, LinearMDSCode.HasMinimumDistance, hammingNorm_eq_weight]

theorem isMDS_iff {K : Type*} [Field K] {N : ℕ} (C : Submodule K (Fin N → K)) :
    IsMDS C ↔ LinearMDSCode.IsMDS C :=
  hasMinimumDistance_iff C _

/-- **The MDS conjecture over finite fields of even order.** Let `K` be a finite
field with an even number `q` of elements, and let `2 ≤ k ≤ q`. The largest `N`
for which some `k`-dimensional subspace `C ⊆ K^N` is an MDS code is `q + 2` when
`k = 3` or `k = q - 1`, and `q + 1` otherwise. -/
theorem maximum_length_of_MDS_code (K : Type*) [Field K] [Fintype K]
    (hq : Even (Fintype.card K)) (k : ℕ) (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    IsGreatest {N : ℕ | ∃ C : Submodule K (Fin N → K), Module.finrank K C = k ∧ IsMDS C}
      (if k = 3 ∨ k = Fintype.card K - 1 then Fintype.card K + 2
        else Fintype.card K + 1) := by
  have heven : Fintype.card K % 2 = 0 := Nat.even_iff.mp hq
  obtain ⟨⟨C, hdim, hmds⟩, hbound⟩ :=
    AllEvenLinearMDS.maximum_length_of_even_card (K := K) heven hk hkq
  refine ⟨⟨C, hdim, (isMDS_iff C).mpr hmds⟩, ?_⟩
  rintro N ⟨C', hdim', hmds'⟩
  exact hbound N C' hdim' ((isMDS_iff C').mp hmds')

end EvenOrderMDS
