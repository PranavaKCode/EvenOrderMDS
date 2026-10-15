module

public import EvenOrderMDS.NormalRestriction
public import EvenOrderMDS.NormalizedPlaneEnvelope
public import EvenOrderMDS.NormalizedSpaceEnvelope

@[expose] public noncomputable section

/-! Literal coordinates, cofactors and normalization for a lift with its vertical column. -/

namespace EvenOrderMDS.LiftGeometry

open LinearCoordinates FourCofactor FourCofactorDerivatives PlaneCofactorDerivatives
open scoped BigOperators

variable {K : Type*} [Field K]

def column (a : Fin 3 → K) (h : K) : Fin 4 → K := ![a 0, a 1, a 2, h]

def vertical : Fin 4 → K := ![0, 0, 0, 1]

def columns {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) : Fin (M + 1) → Fin 4 → K :=
  Fin.cons vertical (fun i => column (a i) (h i))

theorem linearForm_vertical : linearForm (vertical (K := K)) = MvPolynomial.X 3 := by
  simp [linearForm_apply, vertical, Fin.sum_univ_four]

theorem restriction_column (a : Fin 3 → K) (h : K) :
    NormalRestriction.restriction (linearForm (column a h)) = linearForm a := by
  simp [linearForm_apply, column, NormalRestriction.restriction,
    Fin.sum_univ_four, Fin.sum_univ_three]

theorem normal_derivative_column (a : Fin 3 → K) (h : K) :
    MvPolynomial.pderiv 3 (linearForm (column a h)) = MvPolynomial.C h := by
  rw [LocalProductDerivatives.pderiv_linearForm]
  rfl

theorem eval_column (a v : Fin 3 → K) (h : K) :
    MvPolynomial.eval (NormalRestriction.point v) (linearForm (column a h)) =
      MvPolynomial.eval v (linearForm a) := by
  rw [← NormalRestriction.eval_restriction, restriction_column]

theorem cofactor_vertical [CharP K 2] (a b : Fin 3 → K) (h k : K) :
    cofactor vertical (column a h) (column b k) = NormalRestriction.point (crossProduct a b) := by
  funext i
  fin_cases i <;> rw [cofactor_coordinate]
  all_goals erw [Matrix.det_fin_three]
  all_goals simp [vertical, column, NormalRestriction.point,
    cross_apply, CharTwo.sub_eq_add, Fin.succAbove]
  all_goals ring

theorem complementary_product {R : Type*} [CommMonoid R] {M : ℕ}
    (f : Fin (M + 1) → R) (i j : Fin M) :
    (∏ k ∈ (Finset.univ.erase i).erase j, f k.succ) =
      ∏ k ∈ ((Finset.univ.erase 0).erase i.succ).erase j.succ, f k := by
  classical
  apply Finset.prod_bij (fun k _ => k.succ)
  · intro k hk
    simpa using hk
  · intro k _ l _ h
    exact Fin.succ_injective _ h
  · intro k hk
    cases k using Fin.cases with
    | zero => simp at hk
    | succ k => exact ⟨k, by simpa using hk, rfl⟩
  · intro k _
    rfl

theorem eval_complement {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K)
    (i j : Fin M) (v : Fin 3 → K) :
    MvPolynomial.eval (NormalRestriction.point v) (tripleComplement (columns a h) 0 i.succ j.succ) =
      MvPolynomial.eval v (pairComplement a i j) := by
  classical
  simp only [tripleComplement, pairComplement, map_prod]
  rw [← complementary_product]
  apply Finset.prod_congr rfl
  intro k _
  exact eval_column (a k) v (h k)

theorem normalized_restriction [CharP K 2] {M : ℕ}
    (a : Fin M → Fin 3 → K) (h : Fin M → K) (F : MvPolynomial (Fin 4) K)
    (hvalues : NormalizedSpaceHighest.HasNormalizedValues (columns a h) F) :
    NormalizedPlaneHighest.HasNormalizedValues a (NormalRestriction.restriction F) := by
  intro i j hij
  have hval := hvalues 0 i.succ j.succ (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm
    (fun heq => hij (Fin.succ_injective _ heq))
  change MvPolynomial.eval (cofactor vertical (column (a i) (h i)) (column (a j) (h j)))
    (tripleComplement (columns a h) 0 i.succ j.succ * F) = 1 at hval
  rw [cofactor_vertical, map_mul, eval_complement, ← NormalRestriction.eval_restriction] at hval
  simpa only [map_mul] using hval

theorem normalized_restriction_eq [CharP K 2] {M t : ℕ} (hM : 3 ≤ M) (ht : t < M - 1)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) (h : Fin M → K)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t) (hv : NormalizedPlaneHighest.HasNormalizedValues a F)
    (G : MvPolynomial (Fin 4) K) (hG : G.IsHomogeneous t)
    (hGv : NormalizedSpaceHighest.HasNormalizedValues (columns a h) G) :
    NormalRestriction.restriction G = F := by
  exact NormalizedEnvelopeUniqueness.plane_envelope_unique hM a ha ht
    (NormalRestriction.restriction G) F (NormalRestriction.restriction_homogeneous hG) hF
    (normalized_restriction a h G hGv) hv

end EvenOrderMDS.LiftGeometry
