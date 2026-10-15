module

public import EvenOrderMDS.MixedParity
public import EvenOrderMDS.RootSemilinearity
public import EvenOrderMDS.TruncatedGrading

@[expose] public noncomputable section

/-! Unique compatible parity roots and their actual inverse-Frobenius semilinearity. -/

namespace EvenOrderMDS.CompatibleParityRoots

open ParityDerivation SquareRootCoefficients
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2] [Finite K]

noncomputable def forms (n : ℕ) : Submodule K (MvPolynomial (Fin 3) K) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) K (2 * n + 1) ⊓ LinearMap.ker MixedParity.mixedThird

noncomputable def roots (n : ℕ) (p : forms (K := K) n) : Fin 3 → MvPolynomial (Fin 3) K :=
  Classical.choose (MixedParity.exists_unique_parity_of_mixedThird_zero n p.property.1 p.property.2).exists

theorem roots_homogeneous (n : ℕ) (p : forms (K := K) n) (i : Fin 3) :
    (roots n p i).IsHomogeneous n :=
  (Classical.choose_spec (MixedParity.exists_unique_parity_of_mixedThird_zero n p.property.1 p.property.2).exists).1 i

theorem roots_parity (n : ℕ) (p : forms (K := K) n) :
    parityForm (roots n p) = p.val :=
  (Classical.choose_spec (MixedParity.exists_unique_parity_of_mixedThird_zero n p.property.1 p.property.2).exists).2.symm

omit [Finite K] in
theorem parityForm_add (B C : Fin 3 → MvPolynomial (Fin 3) K) :
    parityForm (B + C) = parityForm B + parityForm C := by
  simp [parityForm, CharTwo.add_sq, mul_add, Finset.sum_add_distrib]

theorem parityForm_sqrt_smul (c : K) (B : Fin 3 → MvPolynomial (Fin 3) K) :
    parityForm (squareRoot K c • B) = c • parityForm B := by
  simp [parityForm, smul_pow, squareRoot_sq, Finset.smul_sum]

theorem roots_add (n : ℕ) (p q : forms (K := K) n) : roots n (p + q) = roots n p + roots n q := by
  apply parityForm_injective
  rw [roots_parity, parityForm_add, roots_parity, roots_parity]
  rfl

theorem roots_smul (n : ℕ) (c : K) (p : forms (K := K) n) :
    roots n (c • p) = squareRoot K c • roots n p := by
  apply parityForm_injective
  rw [roots_parity, parityForm_sqrt_smul, roots_parity]
  rfl

noncomputable def rootsMap (n : ℕ) :
    forms (K := K) n →ₛₗ[(squareRoot K).toRingHom] (Fin 3 → MvPolynomial (Fin 3) K) where
  toFun := roots n
  map_add' := roots_add n
  map_smul' := roots_smul n

noncomputable def obstruction (n : ℕ) :
    forms (K := K) n →ₛₗ[(squareRoot K).toRingHom] MvPolynomial (Fin 3) K where
  toFun p := ∑ i, MvPolynomial.X i ^ n * roots n p i
  map_add' := by
    intro p q
    simp [roots_add, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c p
    simp [roots_smul, Finset.smul_sum]

theorem obstruction_apply (n : ℕ) (p : forms (K := K) n) :
    obstruction n p = ∑ i, MvPolynomial.X i ^ n * roots n p i := rfl

theorem obstruction_homogeneous (n : ℕ) (p : forms (K := K) n) :
    (obstruction n p).IsHomogeneous (2 * n) := by
  rw [obstruction_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  simpa only [two_mul] using (MvPolynomial.isHomogeneous_X_pow i n).mul (roots_homogeneous n p i)

theorem obstruction_mem_powerIdeal (n : ℕ) (p : forms (K := K) n) :
    obstruction n p ∈ PowerIdeal.powerIdeal (K := K) n := by
  rw [obstruction_apply, TruncatedGrading.powerIdeal_eq_span_variable_powers]
  apply Ideal.sum_mem
  intro i _
  apply Ideal.mul_mem_right
  exact Ideal.subset_span (Set.mem_range_self i)

theorem derivative_eq_obstruction_square (n : ℕ) (p : forms (K := K) n) :
    frobeniusDerivation (2 * n) p.val = obstruction n p ^ 2 := by
  rw [← roots_parity n p, frobeniusDerivation_parityForm]
  rfl

end EvenOrderMDS.CompatibleParityRoots
