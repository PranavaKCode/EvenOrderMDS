module

public import EvenOrderMDS.CompatibleSpace
public import EvenOrderMDS.CompatibleParityRoots
public import EvenOrderMDS.FrobeniusLineDivisibility
public import EvenOrderMDS.ShearPolynomials

@[expose] public noncomputable section

/-! The concrete inverse-Frobenius obstruction of a compatible pair. -/

namespace EvenOrderMDS.PolynomialObstruction

open CompatiblePolynomial CompatibleSpace CompatibleParityRoots SquareRootCoefficients
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2] [Finite K]

noncomputable def formMap {n t M : ℕ} (hM : 1 ≤ M) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t) :
    pairs t a F →ₗ[K] forms (K := K) n :=
  ((polynomialMap a F).comp (pairs t a F).subtype).codRestrict (forms n) (fun p =>
    ⟨polynomial_homogeneous hM hsize a F hF p.val.1 p.val.2 p.property.1 p.property.2.1,
      p.property.2.2⟩)

noncomputable def obstructionMap {n t M : ℕ} (hM : 1 ≤ M) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t) :
    pairs t a F →ₛₗ[(squareRoot K).toRingHom] MvPolynomial (Fin 3) K :=
  (obstruction n).comp (formMap hM hsize a F hF)

theorem obstructionMap_apply {n t M : ℕ} (hM : 1 ≤ M) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (p : pairs t a F) :
    obstructionMap hM hsize a F hF p = obstruction n (formMap hM hsize a F hF p) := rfl

theorem obstructionMap_homogeneous {n t M : ℕ} (hM : 1 ≤ M) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (p : pairs t a F) :
    (obstructionMap hM hsize a F hF p).IsHomogeneous (2 * n) :=
  obstruction_homogeneous n _

theorem obstructionMap_mem_powerIdeal {n t M : ℕ} (hM : 1 ≤ M) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (p : pairs t a F) :
    obstructionMap hM hsize a F hF p ∈ PowerIdeal.powerIdeal (K := K) n :=
  obstruction_mem_powerIdeal n _

theorem oldProduct_dvd_obstructionMap [Fintype K] {e n t M : ℕ}
    (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (hexp : 2 ^ e = 2 * n) (hcard : Fintype.card K = 2 ^ e)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (hFv : NormalizedPlaneHighest.HasNormalizedValues a F) (p : pairs t a F) :
    PlaneArcColon.lineProduct a ∣ obstructionMap (by omega) hsize a F hF p := by
  obtain ⟨S, _, hCF⟩ := NormalizedPlaneHighest.highest_form_of_normalized_plane_envelope
    n t M hn ht hsize (hcard.trans hexp) a ha F hF hFv
  have hD : ParityDerivation.frobeniusDerivation (2 ^ e) (PlaneArcColon.lineProduct a * F) = 0 := by
    rw [hexp, hCF]
    exact HighestPlaneForm.frobeniusDerivation_highest_plus_square_zero n S
  apply FrobeniusLineDivisibility.oldProduct_dvd_obstruction (by omega) e n hexp (by omega) hcard
    a ha F hD p.val.1 p.val.2 (roots n (formMap (by omega) hsize a F hF p))
  exact (roots_parity n (formMap (by omega) hsize a F hF p)).symm

theorem obstruction_zero_iff_shear [Fintype K] {n t M : ℕ}
    (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (hFv : NormalizedPlaneHighest.HasNormalizedValues a F) (p : pairs t a F) :
    obstructionMap (by omega) hsize a F hF p = 0 ↔
      ∃ s : Fin 3 → K, p.val.1 = ShearPolynomials.heights a s ∧ p.val.2 = ShearPolynomials.derivative s F := by
  obtain ⟨S, _, hCF⟩ := NormalizedPlaneHighest.highest_form_of_normalized_plane_envelope
    n t M hn ht hsize hcard a ha F hF hFv
  constructor
  · intro hz
    apply ShearPolynomials.pair_eq_shear_of_obstruction_zero (by omega) (by omega) a ha F hFv S hCF
      p.val.1 p.val.2 (roots n (formMap (by omega) hsize a F hF p))
      (roots_homogeneous n _)
      (roots_parity n (formMap (by omega) hsize a F hF p)).symm
    exact hz
  · rintro ⟨s, hs, hQ⟩
    have hd := derivative_eq_obstruction_square n (formMap (by omega) hsize a F hF p)
    change ParityDerivation.frobeniusDerivation (2 * n) (polynomial a F p.val.1 p.val.2) =
      obstructionMap (by omega) hsize a F hF p ^ 2 at hd
    rw [hs, hQ, ← ShearPolynomials.derivative_product, hCF,
      ShearPolynomials.frobenius_derivative_directional_highest] at hd
    exact sq_eq_zero_iff.mp hd.symm

theorem obstruction_zero_in_low_degree [Fintype K] {e n t M : ℕ}
    (hn : 1 ≤ n) (ht : t ≤ 1) (hsize : M + t = 2 * n + 2)
    (hexp : 2 ^ e = 2 * n) (hcard : Fintype.card K = 2 ^ e)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (hFv : NormalizedPlaneHighest.HasNormalizedValues a F) (p : pairs t a F) :
    obstructionMap (by omega) hsize a F hF p = 0 := by
  letI : GradedAlgebra (TruncatedGrading.polynomialPieces K) := MvPolynomial.gradedAlgebra
  exact PowerIdealDecomposition.homogeneous_zero_of_higher_degree_divisor
    (TruncatedGrading.polynomialPieces K) (by omega)
    (PlaneArcColon.lineProduct_homogeneous a) (obstructionMap_homogeneous (by omega) hsize a F hF p)
    (oldProduct_dvd_obstructionMap hn (by omega) hsize hexp hcard a ha F hF hFv p)


end EvenOrderMDS.PolynomialObstruction
