module

public import EvenOrderMDS.ParityDerivation

@[expose] public noncomputable section

/-!
# Derivatives of the literal planar highest form

Its coefficients are exactly one. This file computes with that polynomial;
the envelope theorem supplying C*F = highest + S² remains upstream.
-/

namespace EvenOrderMDS.HighestPlaneForm

open scoped BigOperators
open KoszulParity ParityDerivation

variable {K : Type*} [Field K] [CharP K 2]

noncomputable def highest (n : ℕ) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0 ^ (2 * n) * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 1 ^ (2 * n) * MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.X 2 ^ (2 * n) * MvPolynomial.X 0 * MvPolynomial.X 1

noncomputable def directional (s : Fin 3 → K) :
    MvPolynomial (Fin 3) K →ₗ[K] MvPolynomial (Fin 3) K :=
  ∑ i, s i • (MvPolynomial.pderiv i).toLinearMap

omit [CharP K 2] in
theorem directional_apply (s : Fin 3 → K) (p : MvPolynomial (Fin 3) K) :
    directional s p = ∑ i, s i • MvPolynomial.pderiv i p := by
  simp [directional]

theorem pderiv_even_power_zero (i j : Fin 3) (n : ℕ) :
    MvPolynomial.pderiv i ((MvPolynomial.X j : MvPolynomial (Fin 3) K) ^ (2 * n)) = 0 := by
  rw [mul_comm 2 n, pow_mul, pderiv_square_zero]

omit [CharP K 2] in
theorem highest_eq_frobenius_derivative (n : ℕ) :
    highest (K := K) n = frobeniusDerivation (K := K) (2 * n)
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) := by
  rw [(frobeniusDerivation (K := K) (2 * n)).leibniz,
    (frobeniusDerivation (K := K) (2 * n)).leibniz]
  simp only [frobeniusDerivation_X, smul_eq_mul, highest, mul_add]
  ac_rfl

theorem pderiv_highest_zero (n : ℕ) :
    MvPolynomial.pderiv 0 (highest (K := K) n) = pairForm n 1 2 := by
  rw [pairForm_eq]
  simp only [highest, map_add, MvPolynomial.pderiv_mul, pderiv_even_power_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp
  ac_rfl

theorem pderiv_highest_one (n : ℕ) :
    MvPolynomial.pderiv 1 (highest (K := K) n) = pairForm n 0 2 := by
  rw [pairForm_eq]
  simp only [highest, map_add, MvPolynomial.pderiv_mul, pderiv_even_power_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp
  ac_rfl

theorem pderiv_highest_two (n : ℕ) :
    MvPolynomial.pderiv 2 (highest (K := K) n) = pairForm n 0 1 := by
  rw [pairForm_eq]
  simp only [highest, map_add, MvPolynomial.pderiv_mul, pderiv_even_power_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp
  ac_rfl

theorem directional_highest_plus_square (n : ℕ) (s : Fin 3 → K)
    (S : MvPolynomial (Fin 3) K) :
    directional s (highest n + S ^ 2) =
      s 0 • pairForm n 1 2 + s 1 • pairForm n 0 2 + s 2 • pairForm n 0 1 := by
  rw [directional_apply, Fin.sum_univ_three]
  simp only [map_add, pderiv_square_zero, add_zero, pderiv_highest_zero,
    pderiv_highest_one, pderiv_highest_two]

theorem boundary_parity_is_directional_derivative (n : ℕ) (hn : 0 < n)
    (B : Fin 3 → MvPolynomial (Fin 3) K) (hB : ∀ i, (B i).IsHomogeneous n)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0)
    (S : MvPolynomial (Fin 3) K) :
    ∃ s : Fin 3 → K, parityForm B = directional s (highest n + S ^ 2) := by
  obtain ⟨a, b, c, h⟩ := parity_form_of_boundary_syzygy n hn B hB hrel
  refine ⟨![c ^ 2, b ^ 2, a ^ 2], ?_⟩
  rw [directional_highest_plus_square]
  change parityForm B = c ^ 2 • pairForm n 1 2 + b ^ 2 • pairForm n 0 2 + a ^ 2 • pairForm n 0 1
  change (∑ i, MvPolynomial.X i * B i ^ 2) = _
  rw [h]
  ac_rfl

theorem frobeniusDerivation_highest_zero (n : ℕ) :
    frobeniusDerivation (K := K) (2 * n) (highest n) = 0 := by
  have hpow (i : Fin 3) :
      frobeniusDerivation (K := K) (2 * n)
        ((MvPolynomial.X i : MvPolynomial (Fin 3) K) ^ (2 * n)) = 0 := by
    rw [mul_comm 2 n, pow_mul, frobeniusDerivation_square_zero]
  simp only [highest, map_add, Derivation.leibniz, hpow, frobeniusDerivation_X,
    smul_eq_mul, mul_zero, add_zero]
  let T : MvPolynomial (Fin 3) K :=
    MvPolynomial.X 0 ^ (2 * n) * MvPolynomial.X 1 ^ (2 * n) * MvPolynomial.X 2 +
      MvPolynomial.X 0 ^ (2 * n) * MvPolynomial.X 2 ^ (2 * n) * MvPolynomial.X 1 +
      MvPolynomial.X 1 ^ (2 * n) * MvPolynomial.X 2 ^ (2 * n) * MvPolynomial.X 0
  calc
    _ = T + T := by dsimp [T]; ac_rfl
    _ = 0 := CharTwo.add_self_eq_zero T

theorem frobeniusDerivation_highest_plus_square_zero (n : ℕ)
    (S : MvPolynomial (Fin 3) K) :
    frobeniusDerivation (K := K) (2 * n) (highest n + S ^ 2) = 0 := by
  rw [map_add, frobeniusDerivation_highest_zero, frobeniusDerivation_square_zero, add_zero]

end EvenOrderMDS.HighestPlaneForm
