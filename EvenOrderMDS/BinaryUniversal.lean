module

public import EvenOrderMDS.CoordinateRestriction
public import EvenOrderMDS.NormalizedPlaneHighest

@[expose] public noncomputable section

/-! The literal binary polynomial containing every rational projective direction. -/

namespace EvenOrderMDS.BinaryUniversal

open LinearCoordinates CoordinateRestriction StandardArcProjection

variable {K : Type*} [Field K]

noncomputable def polynomial (q : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ q * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 1 ^ q

theorem polynomial_homogeneous (q : ℕ) : (polynomial (K := K) q).IsHomogeneous (q + 1) := by
  have h0 : (MvPolynomial.X 0 ^ q * MvPolynomial.X 1 : MvPolynomial (Fin 2) K).IsHomogeneous (q + 1) :=
    (MvPolynomial.isHomogeneous_X_pow 0 q).mul (MvPolynomial.isHomogeneous_X K 1)
  have h1 : (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) K).IsHomogeneous (q + 1) := by
    simpa only [Nat.add_comm] using (MvPolynomial.isHomogeneous_X K 0).mul (MvPolynomial.isHomogeneous_X_pow 1 q)
  exact h0.add h1

theorem polynomial_coefficient (q : ℕ) (hq : 2 ≤ q) :
    (polynomial (K := K) q).coeff (Finsupp.single 0 q + Finsupp.single 1 1) = 1 := by
  have hne : (Finsupp.single (0 : Fin 2) q + Finsupp.single 1 1) ≠
      Finsupp.single 0 1 + Finsupp.single 1 q := by
    intro h
    have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    simp at h0
    omega
  have h0 : (MvPolynomial.X 0 ^ q * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) =
      MvPolynomial.monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one]
  have h1 : (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) K) =
      MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one]
  rw [polynomial, h0, h1, MvPolynomial.coeff_add]
  simp [Ne.symm hne]

theorem polynomial_ne_zero (q : ℕ) (hq : 2 ≤ q) : polynomial (K := K) q ≠ 0 := by
  intro hz
  have hc := polynomial_coefficient (K := K) q hq
  rw [hz, MvPolynomial.coeff_zero] at hc
  exact zero_ne_one hc

theorem card_polynomial_ne_zero [Fintype K] : polynomial (K := K) (Fintype.card K) ≠ 0 := by
  apply polynomial_ne_zero
  have h := Fintype.one_lt_card (α := K)
  omega

theorem polynomial_cast_card_zero [Fintype K] : (Fintype.card K : MvPolynomial (Fin 2) K) = 0 := by
  rw [← MvPolynomial.C_eq_coe_nat, Nat.cast_card_eq_zero K, MvPolynomial.C_0]

theorem pderiv_card_power_zero [Fintype K] (i j : Fin 2) :
    MvPolynomial.pderiv i ((MvPolynomial.X j : MvPolynomial (Fin 2) K) ^ Fintype.card K) = 0 := by
  rw [MvPolynomial.pderiv_pow, polynomial_cast_card_zero, zero_mul, zero_mul]

theorem pderiv_polynomial_zero [Fintype K] :
    MvPolynomial.pderiv 0 (polynomial (K := K) (Fintype.card K)) = MvPolynomial.X 1 ^ Fintype.card K := by
  simp only [polynomial, map_add, MvPolynomial.pderiv_mul, pderiv_card_power_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem pderiv_polynomial_one [Fintype K] :
    MvPolynomial.pderiv 1 (polynomial (K := K) (Fintype.card K)) = MvPolynomial.X 0 ^ Fintype.card K := by
  simp only [polynomial, map_add, MvPolynomial.pderiv_mul, pderiv_card_power_zero,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem every_nonzero_linearForm_divides [CharP K 2] [Fintype K]
    (a : Fin 2 → K) (ha : a ≠ 0) : linearForm a ∣ polynomial (K := K) (Fintype.card K) := by
  obtain ⟨p, hp⟩ : ∃ p, a p ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  apply (restrictAlong_zero_iff a p hp _).mp
  have hX (i : Fin 2) : restrictAlong a p hp (MvPolynomial.X i) =
      projection a p hp (Pi.single i 1) 0 • (MvPolynomial.X 0 : MvPolynomial (Fin 1) K) := by
    rw [← linearForm_single i, restrictAlong_linearForm, linearForm_apply, Fin.sum_univ_one]
  simp only [polynomial, map_add, map_mul, map_pow, hX, smul_pow,
    FiniteField.pow_card, smul_mul_smul_comm]
  rw [mul_comm ((MvPolynomial.X 0 : MvPolynomial (Fin 1) K) ^ Fintype.card K) (MvPolynomial.X 0)]
  exact CharTwo.add_self_eq_zero _

end EvenOrderMDS.BinaryUniversal
