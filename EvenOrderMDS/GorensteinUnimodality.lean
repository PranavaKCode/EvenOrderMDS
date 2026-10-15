module

public import EvenOrderMDS.TernaryUnimodality
public import EvenOrderMDS.EmbeddingDimension

@[expose] public noncomputable section

/-!
# The concrete codimension-at-most-three Hilbert-function input

This packages the proved algebraic induction in embedding-dimension language.
`StandardGenerated` is the explicit standard-grading condition A_j=(A_1)^j;
`positiveSocle` is the actual annihilator of all positive homogeneous pieces.
Finite dimensionality, exact top degree, and a nonzero top are explicit.

This is the Hilbert-function input of manuscript Theorem 6.5. It does not yet
instantiate the manuscript's particular truncated ternary colon algebra, and
does not prove the MDS theorem.
-/

namespace EvenOrderMDS.GorensteinUnimodality

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] [FiniteDimensional K R]

theorem first_half_monotone_of_embedding_dimension_le_three
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (standard : StandardGeneration.StandardGenerated A)
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (GradedSocle.positiveSocle A) = 1)
    (embeddingDimension : Module.finrank K (A 1) ≤ 3) :
    HilbertSequence.FirstHalfMonotone s (fun j => Module.finrank K (A j)) := by
  exact TernaryUnimodality.first_half_monotone K s R A standard aboveTop topNonzero
    socleDimension (EmbeddingDimension.exists_three_generators (A 1) embeddingDimension)

theorem symmetric_unimodal_of_embedding_dimension_le_three
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (standard : StandardGeneration.StandardGenerated A)
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (GradedSocle.positiveSocle A) = 1)
    (embeddingDimension : Module.finrank K (A 1) ≤ 3) :
    HilbertSequence.Symmetric s (fun j => Module.finrank K (A j)) ∧
      HilbertSequence.FirstHalfMonotone s (fun j => Module.finrank K (A j)) := by
  constructor
  · intro j hj
    exact GradedPairing.complementary_finrank_eq A aboveTop topNonzero socleDimension hj
  · exact first_half_monotone_of_embedding_dimension_le_three A standard aboveTop
      topNonzero socleDimension embeddingDimension

end EvenOrderMDS.GorensteinUnimodality
