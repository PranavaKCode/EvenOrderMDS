module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Pi

@[expose] public noncomputable section

/-!
# Literal linear forms and invertible polynomial coordinate changes

The variables remain formal polynomial variables. A vector-space automorphism
of coefficient rows induces an actual polynomial-algebra automorphism.
-/

namespace EvenOrderMDS.LinearCoordinates

open scoped BigOperators

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def linearForm : (ι → K) →ₗ[K] MvPolynomial ι K where
  toFun a := ∑ i, a i • MvPolynomial.X i
  map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c a; simp [Finset.smul_sum, mul_smul]

omit [DecidableEq ι] in
theorem linearForm_apply (a : ι → K) :
    linearForm a = ∑ i, a i • (MvPolynomial.X i : MvPolynomial ι K) := by
  rfl

theorem linearForm_single (i : ι) :
    linearForm (Pi.single i (1 : K)) = (MvPolynomial.X i : MvPolynomial ι K) := by
  simp [linearForm]

theorem linearForm_coefficient (a : ι → K) (i : ι) :
    (linearForm a).coeff (Finsupp.single i 1) = a i := by
  simp only [linearForm_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_X', Finsupp.single_eq_single_iff, one_ne_zero,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem linearForm_injective : Function.Injective (linearForm (K := K) (ι := ι)) := by
  intro a b hab
  funext i
  have h := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i 1)) hab
  simpa only [linearForm_coefficient] using h

omit [DecidableEq ι] in
theorem linearForm_homogeneous (a : ι → K) : (linearForm a).IsHomogeneous 1 := by
  change linearForm a ∈ MvPolynomial.homogeneousSubmodule ι K 1
  rw [linearForm_apply]
  apply Submodule.sum_mem
  intro i hi
  exact (MvPolynomial.homogeneousSubmodule ι K 1).smul_mem _ (MvPolynomial.isHomogeneous_X K i)

noncomputable def substitute (e : (ι → K) ≃ₗ[K] (ι → K)) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  MvPolynomial.aeval (fun i => linearForm (e (Pi.single i 1)))

theorem substitute_X (e : (ι → K) ≃ₗ[K] (ι → K)) (i : ι) :
    substitute e (MvPolynomial.X i) = linearForm (e (Pi.single i 1)) := by
  simp [substitute]

theorem substitute_linearForm (e : (ι → K) ≃ₗ[K] (ι → K)) (a : ι → K) :
    substitute e (linearForm a) = linearForm (e a) := by
  have ha : (∑ i, a i • (Pi.single i (1 : K) : ι → K)) = a := by
    funext j
    simp [Pi.single_apply]
  calc
    substitute e (linearForm a) = ∑ i, a i • linearForm (e (Pi.single i 1)) := by
      rw [linearForm_apply]
      simp only [map_sum, map_smul, substitute_X]
    _ = linearForm (∑ i, a i • e (Pi.single i 1)) := by simp
    _ = linearForm (e (∑ i, a i • (Pi.single i (1 : K) : ι → K))) := by simp
    _ = linearForm (e a) := by rw [ha]

theorem substitute_comp_inverse (e : (ι → K) ≃ₗ[K] (ι → K)) :
    (substitute e).comp (substitute e.symm) = AlgHom.id K (MvPolynomial ι K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substitute_X, substitute_linearForm,
    LinearEquiv.apply_symm_apply, linearForm_single, AlgHom.id_apply]

noncomputable def changeCoordinates (e : (ι → K) ≃ₗ[K] (ι → K)) : MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (substitute e) (substitute e.symm)
    (substitute_comp_inverse e) (by simpa using substitute_comp_inverse e.symm)

theorem changeCoordinates_linearForm (e : (ι → K) ≃ₗ[K] (ι → K)) (a : ι → K) :
    changeCoordinates e (linearForm a) = linearForm (e a) :=
  substitute_linearForm e a

end EvenOrderMDS.LinearCoordinates
