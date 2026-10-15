module

public import EvenOrderMDS.ParityDerivation

@[expose] public noncomputable section

/-! The actual inverse Frobenius automorphism of a finite characteristic-two field. -/

namespace EvenOrderMDS.SquareRootCoefficients

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

noncomputable def squareRoot : K ≃+* K :=
  (RingEquiv.ofBijective (frobenius K 2)
    ⟨frobenius_inj K 2, Finite.surjective_of_injective (frobenius_inj K 2)⟩).symm

theorem squareRoot_sq (x : K) : squareRoot K x ^ 2 = x :=
  (squareRoot K).symm_apply_apply x

theorem squareRoot_square (x : K) : squareRoot K (x ^ 2) = x :=
  RingEquiv.symm_apply_apply _ x

theorem squareRoot_add (x y : K) : squareRoot K (x + y) = squareRoot K x + squareRoot K y :=
  map_add _ _ _

theorem squareRoot_mul (x y : K) : squareRoot K (x * y) = squareRoot K x * squareRoot K y :=
  map_mul _ _ _

end EvenOrderMDS.SquareRootCoefficients
