module

public import EvenOrderMDS.ParityDecomposition

@[expose] public noncomputable section

/-! The four odd squarefree parity components in three variables. -/

namespace EvenOrderMDS.TernaryParity

open ExponentParity ParityDecomposition ParityDerivation
open scoped BigOperators

theorem ternary_bits_univ : (Finset.univ : Finset (Fin 3 → Fin 2)) =
    {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1],
      ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]} := by decide

theorem sum_ternary_bits {R : Type*} [AddCommMonoid R] (f : (Fin 3 → Fin 2) → R) :
    (∑ b, f b) = f ![0, 0, 0] + f ![0, 0, 1] + f ![0, 1, 0] + f ![0, 1, 1] +
      f ![1, 0, 0] + f ![1, 0, 1] + f ![1, 1, 0] + f ![1, 1, 1] := by
  rw [ternary_bits_univ]
  simp [add_assoc]

variable {K : Type*} [Field K] [CharP K 2] [Finite K]

theorem unit_root_homogeneous (n : ℕ) {p : MvPolynomial (Fin 3) K}
    (hp : p.IsHomogeneous (2 * n + 1)) (b : Fin 3 → Fin 2)
    (hb : (bitExponent b).degree = 1) : (rootComponent b p).IsHomogeneous n := by
  have hindex : (2 * n + 1 - (bitExponent b).degree) / 2 = n := by rw [hb]; omega
  simpa only [hindex] using rootComponent_homogeneous hp b

theorem top_odd_root_homogeneous (n : ℕ) {p : MvPolynomial (Fin 3) K}
    (hp : p.IsHomogeneous (2 * n + 1)) :
    (rootComponent ![1, 1, 1] p).IsHomogeneous (n - 1) := by
  have hweight : (bitExponent (![1, 1, 1] : Fin 3 → Fin 2)).degree = 3 := by
    simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three]
  have hindex : (2 * n + 1 - (bitExponent (![1, 1, 1] : Fin 3 → Fin 2)).degree) / 2 = n - 1 := by
    rw [hweight]
    omega
  simpa only [hindex] using rootComponent_homogeneous hp (![1, 1, 1] : Fin 3 → Fin 2)

theorem exists_odd_parity_decomposition (n : ℕ) {p : MvPolynomial (Fin 3) K}
    (hp : p.IsHomogeneous (2 * n + 1)) :
    ∃ B : Fin 3 → MvPolynomial (Fin 3) K, ∃ S : MvPolynomial (Fin 3) K,
      (∀ i, (B i).IsHomogeneous n) ∧ S.IsHomogeneous (n - 1) ∧
      p = parityForm B + MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * S ^ 2 := by
  let B : Fin 3 → MvPolynomial (Fin 3) K :=
    ![rootComponent ![1, 0, 0] p, rootComponent ![0, 1, 0] p, rootComponent ![0, 0, 1] p]
  let S := rootComponent (![1, 1, 1] : Fin 3 → Fin 2) p
  refine ⟨B, S, ?_, top_odd_root_homogeneous n hp, ?_⟩
  · intro i
    fin_cases i <;> apply unit_root_homogeneous n hp <;>
      simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three]
  · have hz (b : Fin 3 → Fin 2) (hb : (bitExponent b).degree % 2 = 0) : rootComponent b p = 0 := by
      apply rootComponent_eq_zero_of_wrong_parity hp b
      omega
    have hz000 := hz ![0, 0, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have hz011 := hz ![0, 1, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have hz101 := hz ![1, 0, 1] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have hz110 := hz ![1, 1, 0] (by simp [Finsupp.degree_eq_sum, bitExponent_apply, Fin.sum_univ_three])
    have h := sum_parityComponents p
    rw [sum_ternary_bits] at h
    simp only [parityComponent, hz000, hz011, hz101, hz110, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add, add_zero] at h
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype, bitExponent_apply,
      Fin.prod_univ_three] at h
    rw [← h]
    simp only [B, S, parityForm, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]
    ac_rfl

end EvenOrderMDS.TernaryParity
