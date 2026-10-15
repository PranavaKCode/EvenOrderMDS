module

public import EvenOrderMDS.CoordinateRestriction
public import EvenOrderMDS.RestrictionPoints

@[expose] public noncomputable section

/-! Literal parametrization of a two-dimensional dual subspace and its polynomial restriction. -/

namespace EvenOrderMDS.BinaryParameterization

open LinearCoordinates
open scoped BigOperators Matrix

variable {K : Type*} [Field K]

def rowMap {r : ℕ} (x y : Fin r → K) : (Fin r → K) →ₗ[K] (Fin 2 → K) where
  toFun a := ![a ⬝ᵥ x, a ⬝ᵥ y]
  map_add' := by intro a b; funext i; fin_cases i <;> simp [add_dotProduct]
  map_smul' := by intro c a; funext i; fin_cases i <;> simp [smul_dotProduct]

def point {r : ℕ} (x y : Fin r → K) (v : Fin 2 → K) : Fin r → K := v 0 • x + v 1 • y

theorem rowMap_apply {r : ℕ} (x y a : Fin r → K) : rowMap x y a = ![a ⬝ᵥ x, a ⬝ᵥ y] := rfl

theorem point_zero {r : ℕ} (x y : Fin r → K) : point x y 0 = 0 := by simp [point]

theorem point_smul {r : ℕ} (x y : Fin r → K) (c : K) (v : Fin 2 → K) :
    point x y (c • v) = c • point x y v := by
  simp [point, smul_add, smul_smul]

theorem pairing_identity {r : ℕ} (x y a : Fin r → K) (v : Fin 2 → K) :
    a ⬝ᵥ point x y v = rowMap x y a ⬝ᵥ v := by
  simp [point, rowMap, dotProduct, Fin.sum_univ_two, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

noncomputable def restriction {r : ℕ} (x y : Fin r → K) :
    MvPolynomial (Fin r) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval (fun i => x i • MvPolynomial.X 0 + y i • MvPolynomial.X 1)

theorem restriction_X {r : ℕ} (x y : Fin r → K) (i : Fin r) :
    restriction x y (MvPolynomial.X i) = x i • MvPolynomial.X 0 + y i • MvPolynomial.X 1 := by
  simp [restriction]

theorem restriction_linearForm {r : ℕ} (x y a : Fin r → K) :
    restriction x y (linearForm a) = linearForm (rowMap x y a) := by
  simp [restriction, linearForm_apply, rowMap, Fin.sum_univ_two, smul_add, smul_smul,
    Finset.sum_add_distrib, Finset.sum_smul, dotProduct]

theorem eval_restriction {r : ℕ} (x y : Fin r → K) (v : Fin 2 → K) (p : MvPolynomial (Fin r) K) :
    MvPolynomial.eval v (restriction x y p) = MvPolynomial.eval (point x y v) p := by
  change ((MvPolynomial.aeval v).comp (restriction x y)) p = (MvPolynomial.aeval (point x y v)) p
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp [restriction, point, mul_comm]

theorem restriction_homogeneous {r : ℕ} (x y : Fin r → K)
    {p : MvPolynomial (Fin r) K} {d : ℕ} (hp : p.IsHomogeneous d) :
    (restriction x y p).IsHomogeneous d := by
  apply CoordinateRestriction.algHom_homogeneous (restriction x y) _ hp
  intro i
  rw [restriction_X]
  exact (MvPolynomial.homogeneousSubmodule (Fin 2) K 1).add_mem
    ((MvPolynomial.homogeneousSubmodule (Fin 2) K 1).smul_mem _ (MvPolynomial.isHomogeneous_X K 0))
    ((MvPolynomial.homogeneousSubmodule (Fin 2) K 1).smul_mem _ (MvPolynomial.isHomogeneous_X K 1))

end EvenOrderMDS.BinaryParameterization
