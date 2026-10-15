module

public import EvenOrderMDS.CompatibleSpace
public import EvenOrderMDS.CompatibleParityRoots

@[expose] public noncomputable section

/-! Literal shear pairs and their compatibility polynomial. -/

namespace EvenOrderMDS.ShearPolynomials

open LinearCoordinates ActualLiftCompatibility CompatiblePolynomial HighestPlaneForm
open scoped BigOperators Matrix

variable {K : Type*} [Field K]

def heights {M : ℕ} (a : Fin M → Fin 3 → K) (s : Fin 3 → K) : Fin M → K :=
  fun i => a i ⬝ᵥ s

noncomputable def derivative (s : Fin 3 → K) :
    Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K) :=
  s 0 • MvPolynomial.pderiv 0 + s 1 • MvPolynomial.pderiv 1 + s 2 • MvPolynomial.pderiv 2

theorem derivative_eq_directional (s : Fin 3 → K) (p : MvPolynomial (Fin 3) K) :
    derivative s p = directional s p := by
  rw [directional_apply, Fin.sum_univ_three]
  rfl

theorem derivative_linearForm (s a : Fin 3 → K) : derivative s (linearForm a) = MvPolynomial.C (a ⬝ᵥ s) := by
  simp only [derivative, Derivation.add_apply, Derivation.smul_apply, LocalProductDerivatives.pderiv_linearForm]
  simp [MvPolynomial.smul_eq_C_mul, dotProduct, Fin.sum_univ_three, mul_comm]

theorem derivative_oldProduct {M : ℕ} (a : Fin M → Fin 3 → K) (s : Fin 3 → K) :
    derivative s (PlaneArcColon.lineProduct a) = heightTerm a (heights a s) := by
  classical
  rw [PlaneArcColon.lineProduct, DerivationProducts.product_rule]
  simp only [heightTerm, heights, derivative_linearForm, complement, MvPolynomial.smul_eq_C_mul]

theorem derivative_product {M : ℕ} (a : Fin M → Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) (s : Fin 3 → K) :
    derivative s (PlaneArcColon.lineProduct a * F) = polynomial a F (heights a s) (derivative s F) := by
  rw [(derivative s).leibniz, smul_eq_mul, smul_eq_mul, derivative_oldProduct, polynomial]
  rw [mul_comm F]

theorem derivative_homogeneous (s : Fin 3 → K) {p : MvPolynomial (Fin 3) K} {t : ℕ}
    (hp : p.IsHomogeneous t) : (derivative s p).IsHomogeneous (t - 1) := by
  rw [derivative_eq_directional, directional_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) K (t - 1)).smul_mem _ hp.pderiv

theorem derivative_zero_degree (s : Fin 3 → K) {p : MvPolynomial (Fin 3) K}
    (hp : p.IsHomogeneous 0) : derivative s p = 0 := by
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
  rw [hp]
  simp [derivative]

theorem mixedThird_derivative_highest [CharP K 2] (n : ℕ) (s : Fin 3 → K)
    (S : MvPolynomial (Fin 3) K) :
    MixedParity.mixedThird (derivative s (highest n + S ^ 2)) = 0 := by
  rw [derivative_eq_directional, directional_highest_plus_square]
  simp only [map_add, map_smul]
  have hp (i j : Fin 3) : MixedParity.mixedThird (KoszulParity.pairForm (K := K) n i j) = 0 := by
    fin_cases i <;> fin_cases j <;>
      simp only [MixedParity.mixedThird_apply, KoszulParity.pairForm_eq, map_add,
        MvPolynomial.pderiv_mul, pderiv_even_power_zero, MvPolynomial.pderiv_X, Pi.single_apply] <;> simp
  simp only [hp, smul_zero, add_zero]

theorem frobenius_derivative_directional_highest [CharP K 2] (n : ℕ) (s : Fin 3 → K)
    (S : MvPolynomial (Fin 3) K) :
    ParityDerivation.frobeniusDerivation (2 * n) (derivative s (highest n + S ^ 2)) = 0 := by
  have hpow (i : Fin 3) : ParityDerivation.frobeniusDerivation (K := K) (2 * n)
      (MvPolynomial.X i ^ (2 * n)) = 0 := by
    rw [mul_comm 2 n, pow_mul, ParityDerivation.frobeniusDerivation_square_zero]
  have hp (i j : Fin 3) : ParityDerivation.frobeniusDerivation (K := K) (2 * n)
      (KoszulParity.pairForm n i j) = 0 := by
    rw [KoszulParity.pairForm_eq]
    simp only [map_add, Derivation.leibniz, hpow, ParityDerivation.frobeniusDerivation_X,
      smul_eq_mul, mul_zero, add_zero, zero_add]
    rw [mul_comm (MvPolynomial.X i ^ (2 * n))]
    exact CharTwo.add_self_eq_zero _
  rw [derivative_eq_directional, directional_highest_plus_square]
  simp only [map_add, (ParityDerivation.frobeniusDerivation (2 * n)).map_smul,
    hp, smul_zero, add_zero]

theorem shear_mem_pairs [CharP K 2] {n t M : ℕ}
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (S : MvPolynomial (Fin 3) K) (hCF : PlaneArcColon.lineProduct a * F = highest n + S ^ 2)
    (s : Fin 3 → K) : (heights a s, derivative s F) ∈ CompatibleSpace.pairs t a F := by
  refine ⟨derivative_homogeneous s hF, ?_, ?_⟩
  · intro ht0
    subst t
    exact derivative_zero_degree s hF
  · change MixedParity.mixedThird (polynomial a F (heights a s) (derivative s F)) = 0
    rw [← derivative_product, hCF]
    exact mixedThird_derivative_highest n s S

theorem pair_eq_shear_of_obstruction_zero [CharP K 2] {n M : ℕ} (hn : 0 < n) (hM : 3 ≤ M)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hFv : NormalizedPlaneHighest.HasNormalizedValues a F)
    (S : MvPolynomial (Fin 3) K) (hCF : PlaneArcColon.lineProduct a * F = highest n + S ^ 2)
    (h : Fin M → K) (Q : MvPolynomial (Fin 3) K)
    (B : Fin 3 → MvPolynomial (Fin 3) K) (hB : ∀ i, (B i).IsHomogeneous n)
    (hP : polynomial a F h Q = ParityDerivation.parityForm B)
    (hzero : ∑ i, MvPolynomial.X i ^ n * B i = 0) :
    ∃ s : Fin 3 → K, h = heights a s ∧ Q = derivative s F := by
  obtain ⟨s, hs⟩ := boundary_parity_is_directional_derivative n hn B hB hzero S
  have heq : polynomial a F h Q = polynomial a F (heights a s) (derivative s F) := by
    rw [hP, hs, ← derivative_eq_directional, ← hCF, derivative_product]
  have hdiff : polynomial a F (h - heights a s) (Q - derivative s F) = 0 := by
    change CompatibleSpace.polynomialMap a F ((h, Q) - (heights a s, derivative s F)) = 0
    rw [map_sub]
    change polynomial a F h Q - polynomial a F (heights a s) (derivative s F) = 0
    exact sub_eq_zero.mpr heq
  obtain ⟨hh, hQ⟩ := zero_of_polynomial_zero hM a ha F hFv _ _ hdiff
  exact ⟨s, sub_eq_zero.mp hh, sub_eq_zero.mp hQ⟩

end EvenOrderMDS.ShearPolynomials
