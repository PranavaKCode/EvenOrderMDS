module

public import EvenOrderMDS.TernaryParity
public import EvenOrderMDS.HighestPlaneForm

@[expose] public noncomputable section

/-! The planar highest polynomial is forced by its three literal second derivatives. -/

namespace EvenOrderMDS.EvenTernaryParity

open ExponentParity ParityDecomposition ParityDerivation

variable {K : Type*} [Field K] [CharP K 2]

noncomputable def evenForm (A : Fin 3 → MvPolynomial (Fin 3) K)
    (S : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 1 * MvPolynomial.X 2 * A 0 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 2 * A 1 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * A 2 ^ 2 + S ^ 2

theorem pderiv12_evenForm (A : Fin 3 → MvPolynomial (Fin 3) K)
    (S : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (evenForm A S)) = A 0 ^ 2 := by
  simp only [evenForm, map_add, MvPolynomial.pderiv_mul, pderiv_square_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem pderiv02_evenForm (A : Fin 3 → MvPolynomial (Fin 3) K)
    (S : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (evenForm A S)) = A 1 ^ 2 := by
  simp only [evenForm, map_add, MvPolynomial.pderiv_mul, pderiv_square_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem pderiv01_evenForm (A : Fin 3 → MvPolynomial (Fin 3) K)
    (S : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (evenForm A S)) = A 2 ^ 2 := by
  simp only [evenForm, map_add, MvPolynomial.pderiv_mul, pderiv_square_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp

variable [Finite K]

theorem pair_root_homogeneous (n : ℕ) {p : MvPolynomial (Fin 3) K}
    (hp : p.IsHomogeneous (2 * n + 2)) (b : Fin 3 → Fin 2)
    (hb : (bitExponent b).degree = 2) : (rootComponent b p).IsHomogeneous n := by
  have hi : (2 * n + 2 - (bitExponent b).degree) / 2 = n := by rw [hb]; omega
  simpa only [hi] using rootComponent_homogeneous hp b

theorem exists_even_parity_decomposition (n : ℕ) {p : MvPolynomial (Fin 3) K}
    (hp : p.IsHomogeneous (2 * n + 2)) :
    ∃ A : Fin 3 → MvPolynomial (Fin 3) K, ∃ S : MvPolynomial (Fin 3) K,
      (∀ i, (A i).IsHomogeneous n) ∧ S.IsHomogeneous (n + 1) ∧ p = evenForm A S := by
  let A : Fin 3 → MvPolynomial (Fin 3) K :=
    ![rootComponent ![0, 1, 1] p, rootComponent ![1, 0, 1] p, rootComponent ![1, 1, 0] p]
  let S := rootComponent (![0, 0, 0] : Fin 3 → Fin 2) p
  refine ⟨A, S, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> apply pair_root_homogeneous n hp <;>
      simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three]
  · have hi : (2 * n + 2 - (bitExponent (![0, 0, 0] : Fin 3 → Fin 2)).degree) / 2 = n + 1 := by
      simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three]
    simpa only [hi] using rootComponent_homogeneous hp (![0, 0, 0] : Fin 3 → Fin 2)
  · have hz (b : Fin 3 → Fin 2) (hb : (bitExponent b).degree % 2 = 1) : rootComponent b p = 0 := by
      apply rootComponent_eq_zero_of_wrong_parity hp b
      omega
    have hz001 := hz ![0, 0, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have hz010 := hz ![0, 1, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have hz100 := hz ![1, 0, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have hz111 := hz ![1, 1, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have h := sum_parityComponents p
    rw [TernaryParity.sum_ternary_bits] at h
    simp only [parityComponent, hz001, hz010, hz100, hz111, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] at h
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype, bitExponent_apply,
      Fin.prod_univ_three] at h
    rw [← h]
    simp only [A, S, evenForm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    ac_rfl

theorem highest_form_of_literal_second_derivatives (n : ℕ)
    {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous (2 * n + 2))
    (h0 : MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p) = MvPolynomial.X 0 ^ (2 * n))
    (h1 : MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p) = MvPolynomial.X 1 ^ (2 * n))
    (h2 : MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p) = MvPolynomial.X 2 ^ (2 * n)) :
    ∃ S : MvPolynomial (Fin 3) K, S.IsHomogeneous (n + 1) ∧
      p = HighestPlaneForm.highest n + S ^ 2 := by
  obtain ⟨A, S, _, hS, heq⟩ := exists_even_parity_decomposition n hp
  rw [heq, pderiv12_evenForm, mul_comm 2 n, pow_mul] at h0
  rw [heq, pderiv02_evenForm, mul_comm 2 n, pow_mul] at h1
  rw [heq, pderiv01_evenForm, mul_comm 2 n, pow_mul] at h2
  have hA0 := frobenius_inj (MvPolynomial (Fin 3) K) 2 h0
  have hA1 := frobenius_inj (MvPolynomial (Fin 3) K) 2 h1
  have hA2 := frobenius_inj (MvPolynomial (Fin 3) K) 2 h2
  refine ⟨S, hS, ?_⟩
  rw [heq]
  simp only [evenForm, HighestPlaneForm.highest, hA0, hA1, hA2, ← pow_mul, Nat.mul_comm]
  ac_rfl

end EvenOrderMDS.EvenTernaryParity
