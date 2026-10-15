module

public import EvenOrderMDS.FourCofactor
public import EvenOrderMDS.LocalProductDerivatives
public import EvenOrderMDS.QuaternaryParity

@[expose] public noncomputable section

/-! Literal third derivatives of an actual four-dimensional line product at its cofactors. -/

namespace EvenOrderMDS.FourCofactorDerivatives

open LinearCoordinates ArcPolynomialFactors FourCofactor
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def tripleComplement {M : ℕ} (a : Fin M → Fin 4 → K) (i j k : Fin M) :
    MvPolynomial (Fin 4) K :=
  ∏ l ∈ ((Finset.univ.erase i).erase j).erase k, linearForm (a l)

theorem allFactors_eq_triple {M : ℕ} (a : Fin M → Fin 4 → K) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    allFactors a = linearForm (a i) * linearForm (a j) * linearForm (a k) * tripleComplement a i j k := by
  classical
  have hi := Finset.mul_prod_erase Finset.univ (fun l => linearForm (a l)) (Finset.mem_univ i)
  have hj := Finset.mul_prod_erase (Finset.univ.erase i) (fun l => linearForm (a l))
    (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
  have hk := Finset.mul_prod_erase ((Finset.univ.erase i).erase j) (fun l => linearForm (a l))
    (show k ∈ (Finset.univ.erase i).erase j by simp [Ne.symm hik, Ne.symm hjk])
  change (∏ l, linearForm (a l)) = _
  rw [← hi, ← hj, ← hk]
  simp only [tripleComplement, mul_assoc]

theorem product_with_envelope_eq_triple {M : ℕ} (a : Fin M → Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    allFactors a * F = linearForm (a i) * linearForm (a j) * linearForm (a k) *
      (tripleComplement a i j k * F) := by
  rw [allFactors_eq_triple a i j k hij hik hjk, mul_assoc]

noncomputable def thirdDerivative (f : MvPolynomial (Fin 4) K) (i : Fin 4) : MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv (i.succAbove 0) (MvPolynomial.pderiv (i.succAbove 1)
    (MvPolynomial.pderiv (i.succAbove 2) f))

variable [CharP K 2]

theorem thirdDerivative_oddForm (A B : Fin 4 → MvPolynomial (Fin 4) K) (i : Fin 4) :
    thirdDerivative (QuaternaryParity.oddForm A B) i = A i ^ 2 := by
  fin_cases i
  · exact QuaternaryParity.pderiv123_oddForm A B
  · exact QuaternaryParity.pderiv023_oddForm A B
  · exact QuaternaryParity.pderiv013_oddForm A B
  · exact QuaternaryParity.pderiv012_oddForm A B

omit [CharP K 2] in
theorem highest_plus_parity_eq_oddForm (n : ℕ) (B : Fin 4 → MvPolynomial (Fin 4) K) :
    QuaternaryParity.highest n + ParityDerivation.parityForm B =
      QuaternaryParity.oddForm (fun i => MvPolynomial.X i ^ n) B := by
  simp only [QuaternaryParity.highest, QuaternaryParity.oddForm, ← pow_mul, Nat.mul_comm]
  ac_rfl

theorem thirdDerivative_highest_plus_parity (n : ℕ) (B : Fin 4 → MvPolynomial (Fin 4) K) (i : Fin 4) :
    thirdDerivative (QuaternaryParity.highest n + ParityDerivation.parityForm B) i = MvPolynomial.X i ^ (2 * n) := by
  rw [highest_plus_parity_eq_oddForm, thirdDerivative_oddForm, ← pow_mul, mul_comm n 2]

theorem local_cofactor_third_derivative (a b c : Fin 4 → K) (H : MvPolynomial (Fin 4) K) (i : Fin 4) :
    MvPolynomial.eval (cofactor a b c)
      (thirdDerivative (linearForm a * linearForm b * linearForm c * H) i) =
      cofactor a b c i * MvPolynomial.eval (cofactor a b c) H := by
  have ha : MvPolynomial.eval (cofactor a b c) (linearForm a) = 0 := by
    rw [eval_linearForm_eq_dot, cofactor_on_first]
  have hb : MvPolynomial.eval (cofactor a b c) (linearForm b) = 0 := by
    rw [eval_linearForm_eq_dot, cofactor_on_second]
  have hc : MvPolynomial.eval (cofactor a b c) (linearForm c) = 0 := by
    rw [eval_linearForm_eq_dot, cofactor_on_third]
  rw [thirdDerivative, LocalProductDerivatives.three_vanishing_factors _ _ _ _ _ _ _ _ ha hb hc]
  simp only [LocalProductDerivatives.eval_pderiv_linearForm]
  congr 1
  rw [cofactor_coordinate]
  erw [Matrix.det_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, CharTwo.sub_eq_add]
  ac_rfl

theorem cofactor_third_derivative_value {M : ℕ} (a : Fin M → Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) (u v w : Fin M)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (i : Fin 4) :
    MvPolynomial.eval (cofactor (a u) (a v) (a w)) (thirdDerivative (allFactors a * F) i) =
      cofactor (a u) (a v) (a w) i *
        MvPolynomial.eval (cofactor (a u) (a v) (a w)) (tripleComplement a u v w * F) := by
  rw [product_with_envelope_eq_triple a F u v w huv huw hvw]
  exact local_cofactor_third_derivative _ _ _ _ _

end EvenOrderMDS.FourCofactorDerivatives
