module

public import EvenOrderMDS.ParityDecomposition

@[expose] public noncomputable section

/-!
# The actual parity roots are inverse-Frobenius semilinear

The bundled map uses the coefficient automorphism and a literal linear
exponent-filtering map. Additivity and semilinearity are proved, not assumed.
-/

namespace EvenOrderMDS.RootSemilinearity

open ExponentParity SquareRootCoefficients ParityDecomposition
open scoped BigOperators

variable {K ι : Type*} [Field K] [CharP K 2] [Finite K] [Fintype ι]

noncomputable def coefficientRootMap : K →ₛₗ[(squareRoot K).toRingHom] K where
  toFun := squareRoot K
  map_add' := map_add _
  map_smul' := by intro a b; exact map_mul _ a b

noncomputable def rootMap (b : ι → Fin 2) :
    MvPolynomial ι K →ₛₗ[(squareRoot K).toRingHom] MvPolynomial ι K :=
  (Finsupp.lsum K (fun d => if bits d = b then
    (MvPolynomial.monomial (half d)).comp (coefficientRootMap (K := K)) else 0)).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

theorem rootMap_apply (b : ι → Fin 2) (p : MvPolynomial ι K) :
    rootMap b p = rootComponent b p := by
  classical
  simp only [rootMap, rootComponent, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lsum_apply, Finsupp.sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : bits d = b
  · simp only [if_pos hd, LinearMap.comp_apply]
    rfl
  · simp only [if_neg hd, LinearMap.zero_apply]

theorem rootComponent_add (b : ι → Fin 2) (p q : MvPolynomial ι K) :
    rootComponent b (p + q) = rootComponent b p + rootComponent b q := by
  simp only [← rootMap_apply, map_add]

theorem rootComponent_smul (b : ι → Fin 2) (a : K) (p : MvPolynomial ι K) :
    rootComponent b (a • p) = squareRoot K a • rootComponent b p := by
  simp only [← rootMap_apply]
  exact (rootMap b).map_smulₛₗ a p

end EvenOrderMDS.RootSemilinearity
