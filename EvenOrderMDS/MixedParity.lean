module

public import EvenOrderMDS.TernaryParity

@[expose] public noncomputable section

/-!
# The mixed-third-derivative condition gives the unique weight-one parity form

This is the literal polynomial equivalence needed for compatible height pairs,
with the exact degree guards and the finite-field square-root automorphism.
-/

namespace EvenOrderMDS.MixedParity

open ParityDerivation
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2]

noncomputable def mixedThird : MvPolynomial (Fin 3) K →ₗ[K] MvPolynomial (Fin 3) K :=
  (MvPolynomial.pderiv 0).toLinearMap.comp
    ((MvPolynomial.pderiv 1).toLinearMap.comp (MvPolynomial.pderiv 2).toLinearMap)

omit [CharP K 2] in
theorem mixedThird_apply (p : MvPolynomial (Fin 3) K) :
    mixedThird p = MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)) := rfl

theorem mixedThird_parityForm (B : Fin 3 → MvPolynomial (Fin 3) K) :
    mixedThird (parityForm B) = 0 := by
  rw [mixedThird_apply, pderiv_parityForm, pderiv_square_zero, map_zero]

theorem mixedThird_xyz_square (S : MvPolynomial (Fin 3) K) :
    mixedThird (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * S ^ 2) = S ^ 2 := by
  simp only [mixedThird_apply, map_add, MvPolynomial.pderiv_mul, pderiv_square_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem exists_unique_parity_of_mixedThird_zero [Finite K]
    (n : ℕ) {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous (2 * n + 1))
    (hzero : mixedThird p = 0) :
    ∃! B : Fin 3 → MvPolynomial (Fin 3) K,
      (∀ i, (B i).IsHomogeneous n) ∧ p = parityForm B := by
  obtain ⟨B, S, hB, _, hdecomp⟩ := TernaryParity.exists_odd_parity_decomposition n hp
  have h := congrArg mixedThird hdecomp
  rw [hzero, map_add, mixedThird_parityForm, mixedThird_xyz_square, zero_add] at h
  have hS : S = 0 := sq_eq_zero_iff.mp h.symm
  have hform : p = parityForm B := by simpa [hS] using hdecomp
  refine ⟨B, ⟨hB, hform⟩, ?_⟩
  intro C hC
  apply parityForm_injective
  exact hC.2.symm.trans hform

theorem mixedThird_zero_iff_parity [Finite K]
    (n : ℕ) {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous (2 * n + 1)) :
    mixedThird p = 0 ↔ ∃ B : Fin 3 → MvPolynomial (Fin 3) K,
      (∀ i, (B i).IsHomogeneous n) ∧ p = parityForm B := by
  constructor
  · intro h
    exact (exists_unique_parity_of_mixedThird_zero n hp h).exists
  · rintro ⟨B, _, rfl⟩
    exact mixedThird_parityForm B

end EvenOrderMDS.MixedParity
