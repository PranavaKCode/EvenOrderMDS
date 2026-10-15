module

public import EvenOrderMDS.CompatiblePolynomial

@[expose] public noncomputable section

/-! Heights determine the compatible correction polynomial uniquely. -/

namespace EvenOrderMDS.CompatibleCorrection

open PlaneCofactorDerivatives CompatiblePolynomial ParityDerivation

variable {K : Type*} [Field K]

theorem first_derivative_two_vanishing_factors {σ : Type*} (f g H : MvPolynomial σ K)
    (x : σ → K) (i : σ) (hf : MvPolynomial.eval x f = 0) (hg : MvPolynomial.eval x g = 0) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (f * g * H)) = 0 := by
  simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hf, hg,
    zero_mul, mul_zero, add_zero]

theorem pderiv_lineProduct_multiple_at_cofactor {M : ℕ} (a : Fin M → Fin 3 → K)
    (Q : MvPolynomial (Fin 3) K) (i j : Fin M) (hij : i ≠ j) (k : Fin 3) :
    MvPolynomial.eval (crossProduct (a i) (a j))
      (MvPolynomial.pderiv k (PlaneArcColon.lineProduct a * Q)) = 0 := by
  rw [lineProduct_eq_pair a i j hij, mul_assoc]
  exact first_derivative_two_vanishing_factors _ _ _ _ _ (cofactor_on_left _ _) (cofactor_on_right _ _)

theorem zero_height_correction_zero [CharP K 2] [Finite K] {n t M : ℕ}
    (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous (t - 1)) (hQ0 : t = 0 → Q = 0)
    (hzero : MixedParity.mixedThird (PlaneArcColon.lineProduct a * Q) = 0) : Q = 0 := by
  by_cases ht0 : t = 0
  · exact hQ0 ht0
  have hp : (PlaneArcColon.lineProduct a * Q).IsHomogeneous (2 * n + 1) := by
    convert (PlaneArcColon.lineProduct_homogeneous a).mul hQ using 1
    omega
  obtain ⟨B, hB, heq⟩ := (MixedParity.exists_unique_parity_of_mixedThird_zero n hp hzero).exists
  have hBzero (k : Fin 3) : B k = 0 := by
    apply PlaneStarBound.zero_of_plane_arc_cofactor_values (by omega) a ha (hB k) (by omega)
    intro i j hij
    have hd := pderiv_lineProduct_multiple_at_cofactor a Q i j hij k
    rw [heq, pderiv_parityForm, map_pow] at hd
    exact sq_eq_zero_iff.mp hd
  have hpzero : PlaneArcColon.lineProduct a * Q = 0 := by
    rw [heq]
    simp [parityForm, hBzero]
  exact (mul_eq_zero.mp hpzero).resolve_left (PlaneCofactorGeometry.lineProduct_ne_zero (by omega) ha)

theorem correction_unique [CharP K 2] [Finite K] {n t M : ℕ}
    (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (h : Fin M → K)
    (Q R : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous (t - 1)) (hR : R.IsHomogeneous (t - 1))
    (hQ0 : t = 0 → Q = 0) (hR0 : t = 0 → R = 0)
    (hQc : MixedParity.mixedThird (polynomial a F h Q) = 0)
    (hRc : MixedParity.mixedThird (polynomial a F h R) = 0) : Q = R := by
  apply sub_eq_zero.mp
  apply zero_height_correction_zero hn ht hsize a ha (Q - R) (hQ.sub hR)
    (fun ht0 => by rw [hQ0 ht0, hR0 ht0, sub_self])
  have heq : PlaneArcColon.lineProduct a * (Q - R) = polynomial a F h Q - polynomial a F h R := by
    unfold polynomial
    ring
  rw [heq, map_sub, hQc, hRc, sub_self]

end EvenOrderMDS.CompatibleCorrection
