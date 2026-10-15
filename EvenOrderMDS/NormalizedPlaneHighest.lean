module

public import EvenOrderMDS.PlaneCofactorDerivatives
public import EvenOrderMDS.PlaneStarBound
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public noncomputable section

/-!
# The actual plane highest identity from normalized cofactor values

The polynomial F is required to have the exact homogeneous degree and literal
reciprocal normalization. Its existence is the remaining envelope obligation.
The highest identity itself is proved from those data and the actual arc.
-/

namespace EvenOrderMDS.NormalizedPlaneHighest

open PlaneArcColon PlaneCofactorDerivatives EvenTernaryParity

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

def HasNormalizedValues {M : ℕ} (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) : Prop :=
  ∀ i j, i ≠ j → MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F) = 1

theorem highest_form_of_normalized_plane_envelope
    (n t M : ℕ) (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t) (hvalues : HasNormalizedValues a F) :
    ∃ S : MvPolynomial (Fin 3) K, S.IsHomogeneous (n + 1) ∧
      lineProduct a * F = HighestPlaneForm.highest n + S ^ 2 := by
  have hCF : (lineProduct a * F).IsHomogeneous (2 * n + 2) := by
    simpa only [hsize] using (lineProduct_homogeneous a).mul hF
  obtain ⟨A, S, hA, hS, heq⟩ := exists_even_parity_decomposition n hCF
  have hroot (k : Fin 3) : A k = MvPolynomial.X k ^ n := by
    apply sub_eq_zero.mp
    apply PlaneStarBound.zero_of_plane_arc_cofactor_values (by omega) a ha
      ((hA k).sub (MvPolynomial.isHomogeneous_X_pow k n)) (by omega)
    intro i j hij
    have hv := cofactor_second_derivative_value a F i j hij k
    rw [heq, secondDerivative_evenForm, map_pow, hvalues i j hij, mul_one] at hv
    rw [map_sub, map_pow, MvPolynomial.eval_X, sub_eq_zero]
    apply frobenius_inj K 2
    change MvPolynomial.eval (crossProduct (a i) (a j)) (A k) ^ 2 =
      (crossProduct (a i) (a j) k ^ n) ^ 2
    rw [← pow_mul, mul_comm n 2, ← hcard, FiniteField.pow_card]
    exact hv
  refine ⟨S, hS, ?_⟩
  rw [heq]
  simp only [evenForm, HighestPlaneForm.highest, hroot, ← pow_mul, Nat.mul_comm]
  ac_rfl

theorem literal_second_derivatives_of_normalized_plane_envelope
    (n t M : ℕ) (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t) (hvalues : HasNormalizedValues a F) :
    ∀ i : Fin 3, secondDerivative (lineProduct a * F) i = MvPolynomial.X i ^ (2 * n) := by
  obtain ⟨S, _, heq⟩ := highest_form_of_normalized_plane_envelope n t M hn ht hsize hcard a ha F hF hvalues
  intro i
  rw [heq, secondDerivative_highest_plus_square]

end EvenOrderMDS.NormalizedPlaneHighest
