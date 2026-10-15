module

public import EvenOrderMDS.FourCofactorDerivatives
public import EvenOrderMDS.NormalizedPlaneHighest

@[expose] public noncomputable section

/-!
# The actual space highest identity from normalized cofactor values

Envelope existence is not assumed as an axiom: the caller supplies an actual
homogeneous F and its exact normalized values. Its highest identity is derived
using literal product derivatives, finite-field Frobenius and the cofactor bound.
-/

namespace EvenOrderMDS.NormalizedSpaceHighest

open ArcPolynomialFactors FourCofactor FourCofactorDerivatives

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

def HasNormalizedValues {M : ℕ} (a : Fin M → Fin 4 → K) (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ u v w, u ≠ v → u ≠ w → v ≠ w →
    MvPolynomial.eval (cofactor (a u) (a v) (a w)) (tripleComplement a u v w * F) = 1

theorem highest_form_of_normalized_space_envelope
    (n t M : ℕ) (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 3)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous t) (hvalues : HasNormalizedValues a F) :
    ∃ B : Fin 4 → MvPolynomial (Fin 4) K,
      (∀ i, (B i).IsHomogeneous (n + 1)) ∧
      allFactors a * F = QuaternaryParity.highest n + ParityDerivation.parityForm B := by
  have hCF : (allFactors a * F).IsHomogeneous (2 * n + 3) := by
    simpa only [hsize] using (allFactors_homogeneous a).mul hF
  obtain ⟨A, B, hA, hB, heq⟩ := QuaternaryParity.exists_odd_parity_decomposition n hCF
  have hroot (i : Fin 4) : A i = MvPolynomial.X i ^ n := by
    apply sub_eq_zero.mp
    apply FourCofactor.zero_of_cofactor_values (by omega) a ha
      ((hA i).sub (MvPolynomial.isHomogeneous_X_pow i n)) (by omega)
    intro u v w huv huw hvw
    have hv := cofactor_third_derivative_value a F u v w huv huw hvw i
    rw [heq, thirdDerivative_oddForm, map_pow, hvalues u v w huv huw hvw, mul_one] at hv
    rw [map_sub, map_pow, MvPolynomial.eval_X, sub_eq_zero]
    apply frobenius_inj K 2
    change MvPolynomial.eval (cofactor (a u) (a v) (a w)) (A i) ^ 2 =
      (cofactor (a u) (a v) (a w) i ^ n) ^ 2
    rw [← pow_mul, mul_comm n 2, ← hcard, FiniteField.pow_card]
    exact hv
  refine ⟨B, hB, ?_⟩
  rw [heq]
  simp only [QuaternaryParity.oddForm, QuaternaryParity.highest, hroot, ← pow_mul, Nat.mul_comm]
  ac_rfl

theorem literal_third_derivatives_of_normalized_space_envelope
    (n t M : ℕ) (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 3)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous t) (hvalues : HasNormalizedValues a F) :
    ∀ i : Fin 4, thirdDerivative (allFactors a * F) i = MvPolynomial.X i ^ (2 * n) := by
  obtain ⟨B, _, heq⟩ := highest_form_of_normalized_space_envelope n t M hn ht hsize hcard a ha F hF hvalues
  intro i
  rw [heq, thirdDerivative_highest_plus_parity]

end EvenOrderMDS.NormalizedSpaceHighest
