module

public import EvenOrderMDS.ParityDecomposition

@[expose] public noncomputable section

/-! Four-variable odd parity and its literal highest-third-derivative identity. -/

namespace EvenOrderMDS.QuaternaryParity

open ExponentParity ParityDecomposition ParityDerivation
open scoped BigOperators

theorem quaternary_bits_univ : (Finset.univ : Finset (Fin 4 → Fin 2)) =
    {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1],
      ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 1, 1],
      ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1],
      ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1]} := by decide

theorem sum_quaternary_bits {R : Type*} [AddCommMonoid R] (f : (Fin 4 → Fin 2) → R) :
    (∑ b, f b) =
      f ![0, 0, 0, 0] + f ![0, 0, 0, 1] + f ![0, 0, 1, 0] + f ![0, 0, 1, 1] +
      f ![0, 1, 0, 0] + f ![0, 1, 0, 1] + f ![0, 1, 1, 0] + f ![0, 1, 1, 1] +
      f ![1, 0, 0, 0] + f ![1, 0, 0, 1] + f ![1, 0, 1, 0] + f ![1, 0, 1, 1] +
      f ![1, 1, 0, 0] + f ![1, 1, 0, 1] + f ![1, 1, 1, 0] + f ![1, 1, 1, 1] := by
  rw [quaternary_bits_univ]
  simp [add_assoc]

variable {K : Type*} [Field K] [CharP K 2]

noncomputable def oddForm (A B : Fin 4 → MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 * A 0 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 * A 1 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 * A 2 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * A 3 ^ 2 + parityForm B

noncomputable def highest (n : ℕ) : MvPolynomial (Fin 4) K :=
  MvPolynomial.X 0 ^ (2 * n) * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 1 ^ (2 * n) * MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 2 ^ (2 * n) * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
    MvPolynomial.X 3 ^ (2 * n) * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2

theorem pderiv123_oddForm (A B : Fin 4 → MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 3 (oddForm A B))) = A 0 ^ 2 := by
  simp only [oddForm, map_add, MvPolynomial.pderiv_mul, pderiv_parityForm,
    pderiv_square_zero, MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem pderiv023_oddForm (A B : Fin 4 → MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 3 (oddForm A B))) = A 1 ^ 2 := by
  simp only [oddForm, map_add, MvPolynomial.pderiv_mul, pderiv_parityForm,
    pderiv_square_zero, MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem pderiv013_oddForm (A B : Fin 4 → MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 3 (oddForm A B))) = A 2 ^ 2 := by
  simp only [oddForm, map_add, MvPolynomial.pderiv_mul, pderiv_parityForm,
    pderiv_square_zero, MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem pderiv012_oddForm (A B : Fin 4 → MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (oddForm A B))) = A 3 ^ 2 := by
  simp only [oddForm, map_add, MvPolynomial.pderiv_mul, pderiv_parityForm,
    pderiv_square_zero, MvPolynomial.pderiv_X, Pi.single_apply]
  simp

variable [Finite K]

theorem three_root_homogeneous (n : ℕ) {p : MvPolynomial (Fin 4) K}
    (hp : p.IsHomogeneous (2 * n + 3)) (b : Fin 4 → Fin 2)
    (hb : (bitExponent b).degree = 3) : (rootComponent b p).IsHomogeneous n := by
  have hi : (2 * n + 3 - (bitExponent b).degree) / 2 = n := by rw [hb]; omega
  simpa only [hi] using rootComponent_homogeneous hp b

theorem one_root_homogeneous (n : ℕ) {p : MvPolynomial (Fin 4) K}
    (hp : p.IsHomogeneous (2 * n + 3)) (b : Fin 4 → Fin 2)
    (hb : (bitExponent b).degree = 1) : (rootComponent b p).IsHomogeneous (n + 1) := by
  have hi : (2 * n + 3 - (bitExponent b).degree) / 2 = n + 1 := by rw [hb]; omega
  simpa only [hi] using rootComponent_homogeneous hp b

theorem exists_odd_parity_decomposition (n : ℕ) {p : MvPolynomial (Fin 4) K}
    (hp : p.IsHomogeneous (2 * n + 3)) :
    ∃ A B : Fin 4 → MvPolynomial (Fin 4) K,
      (∀ i, (A i).IsHomogeneous n) ∧ (∀ i, (B i).IsHomogeneous (n + 1)) ∧ p = oddForm A B := by
  let A : Fin 4 → MvPolynomial (Fin 4) K :=
    ![rootComponent ![0, 1, 1, 1] p, rootComponent ![1, 0, 1, 1] p,
      rootComponent ![1, 1, 0, 1] p, rootComponent ![1, 1, 1, 0] p]
  let B : Fin 4 → MvPolynomial (Fin 4) K :=
    ![rootComponent ![1, 0, 0, 0] p, rootComponent ![0, 1, 0, 0] p,
      rootComponent ![0, 0, 1, 0] p, rootComponent ![0, 0, 0, 1] p]
  refine ⟨A, B, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> apply three_root_homogeneous n hp <;>
      simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four]
  · intro i
    fin_cases i <;> apply one_root_homogeneous n hp <;>
      simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four]
  · have hz (b : Fin 4 → Fin 2) (hb : (bitExponent b).degree % 2 = 0) : rootComponent b p = 0 := by
      apply rootComponent_eq_zero_of_wrong_parity hp b
      omega
    have hz0000 := hz ![0, 0, 0, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have hz0011 := hz ![0, 0, 1, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have hz0101 := hz ![0, 1, 0, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have hz0110 := hz ![0, 1, 1, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have hz1001 := hz ![1, 0, 0, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have hz1010 := hz ![1, 0, 1, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have hz1100 := hz ![1, 1, 0, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have hz1111 := hz ![1, 1, 1, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_four])
    have h := sum_parityComponents p
    rw [sum_quaternary_bits] at h
    simp only [parityComponent, hz0000, hz0011, hz0101, hz0110, hz1001, hz1010, hz1100, hz1111,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero] at h
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype, bitExponent_apply, Fin.prod_univ_four] at h
    rw [← h]
    simp only [A, B, oddForm, parityForm, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    ac_rfl

theorem highest_form_of_literal_third_derivatives (n : ℕ)
    {p : MvPolynomial (Fin 4) K} (hp : p.IsHomogeneous (2 * n + 3))
    (h0 : MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 3 p)) = MvPolynomial.X 0 ^ (2 * n))
    (h1 : MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 3 p)) = MvPolynomial.X 1 ^ (2 * n))
    (h2 : MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 3 p)) = MvPolynomial.X 2 ^ (2 * n))
    (h3 : MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)) = MvPolynomial.X 3 ^ (2 * n)) :
    ∃ B : Fin 4 → MvPolynomial (Fin 4) K,
      (∀ i, (B i).IsHomogeneous (n + 1)) ∧ p = highest n + parityForm B := by
  obtain ⟨A, B, _, hB, heq⟩ := exists_odd_parity_decomposition n hp
  rw [heq, pderiv123_oddForm, mul_comm 2 n, pow_mul] at h0
  rw [heq, pderiv023_oddForm, mul_comm 2 n, pow_mul] at h1
  rw [heq, pderiv013_oddForm, mul_comm 2 n, pow_mul] at h2
  rw [heq, pderiv012_oddForm, mul_comm 2 n, pow_mul] at h3
  have hA0 := frobenius_inj (MvPolynomial (Fin 4) K) 2 h0
  have hA1 := frobenius_inj (MvPolynomial (Fin 4) K) 2 h1
  have hA2 := frobenius_inj (MvPolynomial (Fin 4) K) 2 h2
  have hA3 := frobenius_inj (MvPolynomial (Fin 4) K) 2 h3
  refine ⟨B, hB, ?_⟩
  rw [heq]
  simp only [oddForm, highest, hA0, hA1, hA2, hA3, ← pow_mul, Nat.mul_comm]
  ac_rfl

end EvenOrderMDS.QuaternaryParity
