module

public import EvenOrderMDS.LiftGeometry
public import EvenOrderMDS.DerivationProducts

@[expose] public noncomputable section

/-!
# Every actual lift obeys the same literal first-order compatibility condition

The plane envelope is fixed. The space envelope restricts to it by exact
cofactor normalization and uniqueness. The normal coefficient argument uses
q >= 4 and separately records the zero-degree correction as zero.
-/

namespace EvenOrderMDS.ActualLiftCompatibility

open LinearCoordinates LiftGeometry
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def complement {M : ℕ} (a : Fin M → Fin 3 → K) (i : Fin M) : MvPolynomial (Fin 3) K :=
  ∏ j ∈ Finset.univ.erase i, linearForm (a j)

noncomputable def heightTerm {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) : MvPolynomial (Fin 3) K :=
  ∑ i, h i • complement a i

noncomputable def oldProduct {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) : MvPolynomial (Fin 4) K :=
  ∏ i, linearForm (column (a i) (h i))

theorem allFactors_columns {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) :
    ArcPolynomialFactors.allFactors (columns a h) = MvPolynomial.X 3 * oldProduct a h := by
  simp [ArcPolynomialFactors.allFactors, columns, Fin.prod_univ_succ, linearForm_vertical, oldProduct]

theorem restriction_oldProduct {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) :
    NormalRestriction.restriction (oldProduct a h) = PlaneArcColon.lineProduct a := by
  simp [oldProduct, PlaneArcColon.lineProduct, restriction_column]

theorem normal_derivative_oldProduct {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) :
    NormalRestriction.restriction (MvPolynomial.pderiv 3 (oldProduct a h)) = heightTerm a h := by
  classical
  rw [oldProduct, DerivationProducts.product_rule, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [normal_derivative_column, map_mul, map_prod]
  have hC : NormalRestriction.restriction (MvPolynomial.C (h i) : MvPolynomial (Fin 4) K) = MvPolynomial.C (h i) := by
    simp [NormalRestriction.restriction]
  rw [hC]
  simp only [MvPolynomial.smul_eq_C_mul, restriction_column, complement]

theorem normal_derivative_product {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K)
    (G : MvPolynomial (Fin 4) K) :
    NormalRestriction.restriction (MvPolynomial.pderiv 3 (oldProduct a h * G)) =
      PlaneArcColon.lineProduct a * NormalRestriction.restriction (MvPolynomial.pderiv 3 G) +
        heightTerm a h * NormalRestriction.restriction G := by
  rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
    normal_derivative_oldProduct, restriction_oldProduct]
  exact add_comm _ _

theorem every_actual_lift_compatible [CharP K 2] [Fintype K]
    {n t M : ℕ} (hn : 2 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (hFv : NormalizedPlaneHighest.HasNormalizedValues a F)
    (h : Fin M → K) (hlift : Arc.IsArc (K := K) 4 (columns a h)) :
    ∃ Q : MvPolynomial (Fin 3) K, Q.IsHomogeneous (t - 1) ∧ (t = 0 → Q = 0) ∧
      MixedParity.mixedThird (PlaneArcColon.lineProduct a * Q + heightTerm a h * F) = 0 := by
  obtain ⟨G, hG, hGv⟩ := NormalizedSpaceEnvelope.exists_space_envelope (by omega) ht
    (show (M + 1) + t = 2 * n + 3 by omega) hcard (columns a h) hlift
  have hrest : NormalRestriction.restriction G = F :=
    normalized_restriction_eq (by omega) (by omega) a ha h F hF hFv G hG hGv
  let Q := NormalRestriction.restriction (MvPolynomial.pderiv 3 G)
  refine ⟨Q, NormalRestriction.normal_derivative_homogeneous hG, ?_, ?_⟩
  · intro ht0
    subst t
    exact NormalRestriction.normal_derivative_zero_degree hG
  · have hhighest := NormalizedSpaceHighest.literal_third_derivatives_of_normalized_space_envelope
      n t (M + 1) (by omega) ht (by omega) hcard (columns a h) hlift G hG hGv 3
    rw [allFactors_columns, mul_assoc, ← NormalRestriction.mixed_eq_thirdDerivative] at hhighest
    have hnormal := NormalRestriction.first_normal_mixed_zero hn (oldProduct a h * G) hhighest
    rw [normal_derivative_product, hrest] at hnormal
    exact hnormal

theorem exists_common_envelope_for_all_lifts [CharP K 2] [Fintype K]
    {n t M : ℕ} (hn : 2 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous t ∧ NormalizedPlaneHighest.HasNormalizedValues a F ∧
      ∀ h : Fin M → K, Arc.IsArc (K := K) 4 (columns a h) →
        ∃ Q : MvPolynomial (Fin 3) K, Q.IsHomogeneous (t - 1) ∧ (t = 0 → Q = 0) ∧
          MixedParity.mixedThird (PlaneArcColon.lineProduct a * Q + heightTerm a h * F) = 0 := by
  obtain ⟨F, hF, hv⟩ := NormalizedPlaneEnvelope.exists_plane_envelope (by omega) ht hsize hcard a ha
  exact ⟨F, hF, hv, fun h hlift => every_actual_lift_compatible hn ht hsize hcard a ha F hF hv h hlift⟩

end EvenOrderMDS.ActualLiftCompatibility
