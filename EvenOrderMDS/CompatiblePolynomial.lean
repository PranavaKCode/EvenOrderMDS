module

public import EvenOrderMDS.ActualLiftCompatibility

@[expose] public noncomputable section

/-! The literal compatibility polynomial and its injectivity on pairs. -/

namespace EvenOrderMDS.CompatiblePolynomial

open LinearCoordinates ActualLiftCompatibility PlaneCofactorGeometry
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def polynomial {M : ℕ} (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (h : Fin M → K) (Q : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  PlaneArcColon.lineProduct a * Q + heightTerm a h * F

theorem complement_homogeneous {M : ℕ} (a : Fin M → Fin 3 → K) (i : Fin M) :
    (complement a i).IsHomogeneous (M - 1) := by
  classical
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ.erase i) (fun j => linearForm (a j))
    (fun _ => 1) (fun j _ => linearForm_homogeneous (a j))
  simpa [complement] using h

theorem heightTerm_homogeneous {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) :
    (heightTerm a h).IsHomogeneous (M - 1) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) K (M - 1)).smul_mem _ (complement_homogeneous a i)

theorem polynomial_homogeneous {M n t : ℕ} (hM : 1 ≤ M) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (h : Fin M → K) (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous (t - 1)) (hQ0 : t = 0 → Q = 0) :
    (polynomial a F h Q).IsHomogeneous (2 * n + 1) := by
  have hterm : (heightTerm a h * F).IsHomogeneous (2 * n + 1) := by
    convert (heightTerm_homogeneous a h).mul hF using 1; omega
  unfold polynomial
  by_cases ht : t = 0
  · rw [hQ0 ht, mul_zero, zero_add]
    exact hterm
  · apply MvPolynomial.IsHomogeneous.add _ hterm
    convert (PlaneArcColon.lineProduct_homogeneous a).mul hQ using 1; omega

theorem lineProduct_eq_single {M : ℕ} (a : Fin M → Fin 3 → K) (i : Fin M) :
    PlaneArcColon.lineProduct a = linearForm (a i) * complement a i :=
  (Finset.mul_prod_erase Finset.univ (fun j => linearForm (a j)) (Finset.mem_univ i)).symm

theorem old_line_dvd_complement {M : ℕ} (a : Fin M → Fin 3 → K) (i j : Fin M) (hij : i ≠ j) :
    linearForm (a i) ∣ complement a j := by
  classical
  apply Finset.dvd_prod_of_mem
  simpa using hij

theorem old_line_not_dvd_complement [CharP K 2] {M : ℕ} (hM : 3 ≤ M)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) (i : Fin M) :
    ¬ linearForm (a i) ∣ complement a i := by
  classical
  intro h
  obtain ⟨j, hj, hij⟩ := (old_line_prime hM ha i).dvd_finset_prod_iff _ |>.mp h
  exact old_lines_nondividing hM ha i j (Finset.ne_of_mem_erase hj).symm hij

theorem heightTerm_eq_single {M : ℕ} (a : Fin M → Fin 3 → K) (h : Fin M → K) (i : Fin M) :
    heightTerm a h = h i • complement a i + ∑ j ∈ Finset.univ.erase i, h j • complement a j :=
  (Finset.add_sum_erase Finset.univ (fun j => h j • complement a j) (Finset.mem_univ i)).symm

theorem zero_of_polynomial_zero [CharP K 2] {M : ℕ} (hM : 3 ≤ M)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hFv : NormalizedPlaneHighest.HasNormalizedValues a F)
    (h : Fin M → K) (Q : MvPolynomial (Fin 3) K) (hzero : polynomial a F h Q = 0) :
    h = 0 ∧ Q = 0 := by
  classical
  have hh (i : Fin M) : h i = 0 := by
    have hCQ : linearForm (a i) ∣ PlaneArcColon.lineProduct a * Q := by
      rw [lineProduct_eq_single a i]
      exact dvd_mul_right _ _ |>.trans (dvd_mul_right _ _)
    have hp : linearForm (a i) ∣ PlaneArcColon.lineProduct a * Q + heightTerm a h * F := by
      rw [← polynomial, hzero]
      exact dvd_zero _
    have hHF := (dvd_add_right hCQ).mp hp
    have hH : linearForm (a i) ∣ heightTerm a h :=
      ((old_line_prime hM ha i).dvd_or_dvd hHF).resolve_right
        (normalized_envelope_not_divisible_by_old_line hM a F hFv i)
    have hrest : linearForm (a i) ∣ ∑ j ∈ Finset.univ.erase i, h j • complement a j := by
      apply Finset.dvd_sum
      intro j hj
      rw [MvPolynomial.smul_eq_C_mul]
      exact dvd_mul_of_dvd_right (old_line_dvd_complement a i j (Finset.ne_of_mem_erase hj).symm) _
    rw [heightTerm_eq_single] at hH
    have hsingle := (dvd_add_left hrest).mp hH
    by_contra hne
    rw [MvPolynomial.smul_eq_C_mul] at hsingle
    have hu : IsUnit (MvPolynomial.C (h i) : MvPolynomial (Fin 3) K) :=
      (isUnit_iff_ne_zero.mpr hne).map MvPolynomial.C
    exact old_line_not_dvd_complement hM a ha i (hu.dvd_mul_left.mp hsingle)
  have heq : h = 0 := funext hh
  refine ⟨heq, ?_⟩
  have hCQ : PlaneArcColon.lineProduct a * Q = 0 := by
    simpa [polynomial, heq, heightTerm] using hzero
  exact (mul_eq_zero.mp hCQ).resolve_left (lineProduct_ne_zero hM ha)

end EvenOrderMDS.CompatiblePolynomial
