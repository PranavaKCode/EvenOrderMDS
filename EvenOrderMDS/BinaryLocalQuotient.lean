module

public import EvenOrderMDS.BinaryUniversal
public import EvenOrderMDS.ArcPolynomialFactors
public import EvenOrderMDS.HomogeneousDivision
public import EvenOrderMDS.LocalProductDerivatives

@[expose] public noncomputable section

/-!
# Literal local binary envelopes from cofactor-coordinate data

The quotient of the universal rational-direction polynomial is constructed
with its exact degree. Product differentiation proves its normalized values.
-/

namespace EvenOrderMDS.BinaryLocalQuotient

open LinearCoordinates ArcPolynomialFactors
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

noncomputable def complement {m : ℕ} (a : Fin m → Fin 2 → K) (i : Fin m) : MvPolynomial (Fin 2) K :=
  ∏ j ∈ Finset.univ.erase i, linearForm (a j)

omit [CharP K 2] [Fintype K] in
theorem allFactors_eq_single {m : ℕ} (a : Fin m → Fin 2 → K) (i : Fin m) :
    allFactors a = linearForm (a i) * complement a i :=
  (Finset.mul_prod_erase Finset.univ (fun j => linearForm (a j)) (Finset.mem_univ i)).symm

theorem allFactors_dvd_universal {m : ℕ} (hm : 2 ≤ m) (a : Fin m → Fin 2 → K)
    (ha : Arc.IsArc (K := K) 2 a) : allFactors a ∣ BinaryUniversal.polynomial (K := K) (Fintype.card K) := by
  cases m with
  | zero => omega
  | succ m =>
    apply allFactors_dvd_of_each (by decide : 1 ≤ 1) hm a ha
    intro i
    apply BinaryUniversal.every_nonzero_linearForm_divides
    exact ArcContraction.column_ne_zero_of_enough_columns (by decide : 1 ≤ 2) hm ha i

theorem exists_homogeneous_quotient {m t : ℕ} (hm : 2 ≤ m)
    (hsize : m + t = Fintype.card K + 1) (a : Fin m → Fin 2 → K)
    (ha : Arc.IsArc (K := K) 2 a) (c : K) :
    ∃ T : MvPolynomial (Fin 2) K, T.IsHomogeneous t ∧
      allFactors a * T = c • BinaryUniversal.polynomial (K := K) (Fintype.card K) := by
  have hdiv := allFactors_dvd_universal hm a ha
  have hscaled : allFactors a ∣ c • BinaryUniversal.polynomial (K := K) (Fintype.card K) := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hdiv _
  have hhom : (c • BinaryUniversal.polynomial (K := K) (Fintype.card K)).IsHomogeneous (m + t) := by
    rw [hsize]
    exact (MvPolynomial.homogeneousSubmodule (Fin 2) K (Fintype.card K + 1)).smul_mem c
      (BinaryUniversal.polynomial_homogeneous _)
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 2) K) := MvPolynomial.gradedAlgebra
  obtain ⟨T, hT, heq⟩ := HomogeneousDivision.exists_homogeneous_quotient
    (MvPolynomial.homogeneousSubmodule (Fin 2) K) (allFactors_homogeneous a) hhom hscaled
  exact ⟨T, hT, heq.symm⟩

omit [Fintype K] in
theorem cofactor_relation_root {m : ℕ} (a : Fin m → Fin 2 → K)
    (v : Fin m → Fin 2 → K) (c : K)
    (hrel : ∀ i, a i = c • ![v i 1, v i 0]) (i : Fin m) :
    MvPolynomial.eval (v i) (linearForm (a i)) = 0 := by
  simp [linearForm_apply, Fin.sum_univ_two, hrel, mul_assoc, mul_comm, mul_left_comm,
    CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem cofactor_relation_gradient {m : ℕ} (a : Fin m → Fin 2 → K)
    (v : Fin m → Fin 2 → K) (c : K)
    (hrel : ∀ i, a i = c • ![v i 1, v i 0]) (i : Fin m) (k : Fin 2) :
    MvPolynomial.eval (v i) (MvPolynomial.pderiv k
      (c • BinaryUniversal.polynomial (K := K) (Fintype.card K))) = a i k := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C]
  fin_cases k
  · change c * MvPolynomial.eval (v i) (MvPolynomial.pderiv 0 (BinaryUniversal.polynomial (K := K) (Fintype.card K))) = a i 0
    rw [BinaryUniversal.pderiv_polynomial_zero, map_pow, MvPolynomial.eval_X, FiniteField.pow_card]
    simpa [Pi.smul_apply, smul_eq_mul] using (congrFun (hrel i) 0).symm
  · change c * MvPolynomial.eval (v i) (MvPolynomial.pderiv 1 (BinaryUniversal.polynomial (K := K) (Fintype.card K))) = a i 1
    rw [BinaryUniversal.pderiv_polynomial_one, map_pow, MvPolynomial.eval_X, FiniteField.pow_card]
    simpa [Pi.smul_apply, smul_eq_mul] using (congrFun (hrel i) 1).symm

theorem exists_normalized_local_quotient {m t : ℕ} (hm : 2 ≤ m)
    (hsize : m + t = Fintype.card K + 1) (a : Fin m → Fin 2 → K)
    (ha : Arc.IsArc (K := K) 2 a) (v : Fin m → Fin 2 → K) (c : K)
    (hrel : ∀ i, a i = c • ![v i 1, v i 0]) :
    ∃ T : MvPolynomial (Fin 2) K, T.IsHomogeneous t ∧
      (allFactors a * T = c • BinaryUniversal.polynomial (K := K) (Fintype.card K)) ∧
      ∀ i, MvPolynomial.eval (v i) (complement a i * T) = 1 := by
  obtain ⟨T, hT, hquot⟩ := exists_homogeneous_quotient hm hsize a ha c
  refine ⟨T, hT, hquot, ?_⟩
  intro i
  have hne := ArcContraction.column_ne_zero_of_enough_columns (by decide : 1 ≤ 2) hm ha i
  obtain ⟨k, hk⟩ : ∃ k, a i k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have h := congrArg (fun f => MvPolynomial.eval (v i) (MvPolynomial.pderiv k f)) hquot
  rw [allFactors_eq_single a i, mul_assoc, MvPolynomial.pderiv_mul, map_add] at h
  simp only [map_mul] at h
  rw [LocalProductDerivatives.eval_pderiv_linearForm, cofactor_relation_root a v c hrel i,
    zero_mul, add_zero, cofactor_relation_gradient a v c hrel i k] at h
  apply mul_left_cancel₀ hk
  simpa only [mul_one, map_mul] using h

end EvenOrderMDS.BinaryLocalQuotient
