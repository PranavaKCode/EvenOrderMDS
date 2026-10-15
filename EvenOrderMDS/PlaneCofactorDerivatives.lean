module

public import EvenOrderMDS.LocalProductDerivatives
public import EvenOrderMDS.PlaneArcColon
public import EvenOrderMDS.EvenTernaryParity

@[expose] public noncomputable section

/-! Literal second derivatives of the old line product at actual cofactor vectors. -/

namespace EvenOrderMDS.PlaneCofactorDerivatives

open LinearCoordinates PlaneArcColon
open scoped BigOperators Matrix

variable {K : Type*} [Field K]

noncomputable def pairComplement {M : ℕ} (a : Fin M → Fin 3 → K) (i j : Fin M) :
    MvPolynomial (Fin 3) K :=
  ∏ k ∈ (Finset.univ.erase i).erase j, linearForm (a k)

theorem lineProduct_eq_pair {M : ℕ} (a : Fin M → Fin 3 → K) (i j : Fin M) (hij : i ≠ j) :
    lineProduct a = linearForm (a i) * linearForm (a j) * pairComplement a i j := by
  classical
  have hi := Finset.mul_prod_erase Finset.univ (fun k => linearForm (a k)) (Finset.mem_univ i)
  have hj := Finset.mul_prod_erase (Finset.univ.erase i) (fun k => linearForm (a k))
    (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
  change (∏ k, linearForm (a k)) = _
  rw [← hi, ← hj]
  exact (mul_assoc _ _ _).symm

theorem product_with_envelope_eq_pair {M : ℕ} (a : Fin M → Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) (i j : Fin M) (hij : i ≠ j) :
    lineProduct a * F = linearForm (a i) * linearForm (a j) * (pairComplement a i j * F) := by
  rw [lineProduct_eq_pair a i j hij, mul_assoc]

theorem eval_linearForm_eq_dot (a x : Fin 3 → K) : MvPolynomial.eval x (linearForm a) = a ⬝ᵥ x := by
  simp [linearForm_apply, dotProduct]

theorem cofactor_on_left (a b : Fin 3 → K) :
    MvPolynomial.eval (crossProduct a b) (linearForm a) = 0 := by
  rw [eval_linearForm_eq_dot]
  exact dot_self_cross _ _

theorem cofactor_on_right (a b : Fin 3 → K) :
    MvPolynomial.eval (crossProduct a b) (linearForm b) = 0 := by
  rw [eval_linearForm_eq_dot]
  exact dot_cross_self _ _

noncomputable def secondDerivative (p : MvPolynomial (Fin 3) K) : Fin 3 → MvPolynomial (Fin 3) K :=
  ![MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p),
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p),
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p)]

variable [CharP K 2]

theorem secondDerivative_evenForm (A : Fin 3 → MvPolynomial (Fin 3) K)
    (S : MvPolynomial (Fin 3) K) (k : Fin 3) :
    secondDerivative (EvenTernaryParity.evenForm A S) k = A k ^ 2 := by
  fin_cases k <;> simp [secondDerivative, EvenTernaryParity.pderiv12_evenForm,
    EvenTernaryParity.pderiv02_evenForm, EvenTernaryParity.pderiv01_evenForm]

omit [CharP K 2] in
theorem highest_plus_square_eq_evenForm (n : ℕ) (S : MvPolynomial (Fin 3) K) :
    HighestPlaneForm.highest n + S ^ 2 =
      EvenTernaryParity.evenForm (fun i => MvPolynomial.X i ^ n) S := by
  simp only [HighestPlaneForm.highest, EvenTernaryParity.evenForm, ← pow_mul, Nat.mul_comm]
  ac_rfl

theorem secondDerivative_highest_plus_square (n : ℕ) (S : MvPolynomial (Fin 3) K) (i : Fin 3) :
    secondDerivative (HighestPlaneForm.highest n + S ^ 2) i = MvPolynomial.X i ^ (2 * n) := by
  rw [highest_plus_square_eq_evenForm, secondDerivative_evenForm, ← pow_mul, mul_comm n 2]

theorem cofactor_second_derivative_value {M : ℕ} (a : Fin M → Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) (i j : Fin M) (hij : i ≠ j) (k : Fin 3) :
    MvPolynomial.eval (crossProduct (a i) (a j)) (secondDerivative (lineProduct a * F) k) =
      crossProduct (a i) (a j) k *
        MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F) := by
  rw [product_with_envelope_eq_pair a F i j hij]
  fin_cases k
  · change MvPolynomial.eval (crossProduct (a i) (a j))
      (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2
        (linearForm (a i) * linearForm (a j) * (pairComplement a i j * F)))) =
      crossProduct (a i) (a j) 0 *
        MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F)
    rw [LocalProductDerivatives.two_linear_factors _ _ _ _ _ _
      (cofactor_on_left (a i) (a j)) (cofactor_on_right (a i) (a j))]
    simp [cross_apply, CharTwo.sub_eq_add, add_comm]
  · change MvPolynomial.eval (crossProduct (a i) (a j))
      (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2
        (linearForm (a i) * linearForm (a j) * (pairComplement a i j * F)))) =
      crossProduct (a i) (a j) 1 *
        MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F)
    rw [LocalProductDerivatives.two_linear_factors _ _ _ _ _ _
      (cofactor_on_left (a i) (a j)) (cofactor_on_right (a i) (a j))]
    simp [cross_apply, CharTwo.sub_eq_add, add_comm]
  · change MvPolynomial.eval (crossProduct (a i) (a j))
      (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1
        (linearForm (a i) * linearForm (a j) * (pairComplement a i j * F)))) =
      crossProduct (a i) (a j) 2 *
        MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F)
    rw [LocalProductDerivatives.two_linear_factors _ _ _ _ _ _
      (cofactor_on_left (a i) (a j)) (cofactor_on_right (a i) (a j))]
    simp [cross_apply, CharTwo.sub_eq_add, add_comm]

end EvenOrderMDS.PlaneCofactorDerivatives
