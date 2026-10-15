module

public import EvenOrderMDS.RestrictionPoints
public import EvenOrderMDS.ArcPolynomialFactors
public import EvenOrderMDS.PlaneStarBound
public import EvenOrderMDS.PlaneCofactorGeometry

@[expose] public noncomputable section

/-!
# The rank-four star-point degree bound in intrinsic intersection form

Star vanishing means vanishing at every nonzero vector on every intersection
of three distinct old hyperplanes. The contraction, polynomial restriction,
point embedding, and final product divisibility are all constructed.
-/

namespace EvenOrderMDS.RankFourStar

open LinearCoordinates CoordinateRestriction RestrictionPoints StandardArcProjection
open ArcPolynomialFactors PlaneCofactorDerivatives

variable {K : Type*} [Field K] [CharP K 2]

def StarVanishes {M : ℕ} (a : Fin M → Fin 4 → K) (p : MvPolynomial (Fin 4) K) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x : Fin 4 → K, x ≠ 0 →
    MvPolynomial.eval x (linearForm (a i)) = 0 →
    MvPolynomial.eval x (linearForm (a j)) = 0 →
    MvPolynomial.eval x (linearForm (a k)) = 0 → MvPolynomial.eval x p = 0

theorem zero_of_rank_four_star_vanishing {M : ℕ} (hM : 4 ≤ M)
    (a : Fin M → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    {p : MvPolynomial (Fin 4) K} {j : ℕ} (hp : p.IsHomogeneous j)
    (hdegree : j < M - 2) (hstar : StarVanishes a p) : p = 0 := by
  cases M with
  | zero => omega
  | succ m =>
    have hdiv (i : Fin (m + 1)) : linearForm (a i) ∣ p := by
      have hne := ArcContraction.column_ne_zero_of_enough_columns (by decide : 1 ≤ 4) hM ha i
      obtain ⟨c, hc⟩ : ∃ c, a i c ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      let R := restrictAlong (a i) c hc
      let b : Fin m → Fin 3 → K := fun k => projection (a i) c hc (a (i.succAbove k))
      have hb : Arc.IsArc (K := K) 3 b := projected_columns_are_arc a ha i c hc
      apply (restrictAlong_zero_iff (a i) c hc p).mp
      apply PlaneStarBound.zero_of_plane_arc_cofactor_values (by omega) b hb
        (restrictAlong_homogeneous (a i) c hc hp) (by omega)
      intro u v huv
      let y := crossProduct (b u) (b v)
      have hy : y ≠ 0 := PlaneCofactorGeometry.cofactor_ne_zero (by omega) hb u v huv
      have hx := restrictionPoint_ne_zero (a i) c hc hy
      rw [← eval_pullbackPoint]
      apply hstar i (i.succAbove u) (i.succAbove v) (Fin.ne_succAbove i u)
        (Fin.ne_succAbove i v) (fun heq => huv (Fin.succAbove_right_injective heq))
        _ hx (restrictionPoint_on_center (a i) c hc y)
      · rw [restrictionPoint_evaluation]
        exact cofactor_on_left (b u) (b v)
      · rw [restrictionPoint_evaluation]
        exact cofactor_on_right (b u) (b v)
    have hwhole := allFactors_dvd_of_each (by decide : 1 ≤ 3) hM a ha p hdiv
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 4) K) := MvPolynomial.gradedAlgebra
    exact PowerIdealDecomposition.homogeneous_zero_of_higher_degree_divisor
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (by omega) (allFactors_homogeneous a) hp hwhole

end EvenOrderMDS.RankFourStar
