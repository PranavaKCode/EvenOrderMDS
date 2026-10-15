module

public import EvenOrderMDS.NormalizedPlaneHighest

@[expose] public noncomputable section

/-! Nonzero literal cofactor denominators and envelope restrictions. -/

namespace EvenOrderMDS.PlaneCofactorGeometry

open PlaneArcColon PlaneCofactorDerivatives PlaneArcNormalization LinearCoordinates
open NormalizedPlaneHighest
open scoped BigOperators Matrix

variable {K : Type*} [Field K]

theorem determinant_three_ne_zero {M : ℕ} {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Matrix.det ![a i, a j, a k] ≠ 0 := by
  have hlin := arc_three_independent ha i j k hij hik hjk
  exact ((Matrix.isUnit_iff_isUnit_det ![a i, a j, a k]).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hlin)).ne_zero

theorem cofactor_avoids_other {M : ℕ} {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MvPolynomial.eval (crossProduct (a i) (a j)) (linearForm (a k)) ≠ 0 := by
  rw [eval_linearForm_eq_dot, triple_product_eq_det]
  exact determinant_three_ne_zero ha k i j hik.symm hjk.symm hij

theorem cofactor_ne_zero {M : ℕ} (hM : 3 ≤ M) {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i j : Fin M) (hij : i ≠ j) :
    crossProduct (a i) (a j) ≠ 0 := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have hn := cofactor_avoids_other ha i j k hij hki.symm hkj.symm
  intro hz
  apply hn
  rw [hz, eval_linearForm_eq_dot]
  simp

theorem pairComplement_eval_ne_zero {M : ℕ} {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i j : Fin M) (hij : i ≠ j) :
    MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j) ≠ 0 := by
  classical
  rw [pairComplement, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  exact cofactor_avoids_other ha i j k hij hki.symm hkj.symm

theorem normalized_envelope_eval_ne_zero {M : ℕ} (a : Fin M → Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) (hvalues : HasNormalizedValues a F)
    (i j : Fin M) (hij : i ≠ j) : MvPolynomial.eval (crossProduct (a i) (a j)) F ≠ 0 := by
  have h := hvalues i j hij
  rw [map_mul] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem normalized_envelope_not_divisible_by_old_line {M : ℕ} (hM : 3 ≤ M)
    (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (hvalues : HasNormalizedValues a F) (i : Fin M) : ¬ linearForm (a i) ∣ F := by
  obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  have hn := normalized_envelope_eval_ne_zero a F hvalues i j hji.symm
  rintro ⟨r, hr⟩
  apply hn
  rw [hr, map_mul, cofactor_on_left, zero_mul]

theorem lineProduct_ne_zero {M : ℕ} (hM : 3 ≤ M) {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) : lineProduct a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hi
  apply arc_column_ne_zero hM ha i
  apply linearForm_injective
  simpa only [map_zero] using hi

theorem old_lines_nondividing {M : ℕ} (hM : 3 ≤ M) {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i j : Fin M) (hij : i ≠ j) :
    ¬ linearForm (a i) ∣ linearForm (a j) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have hn := cofactor_avoids_other ha i k j hki.symm hij hkj
  rintro ⟨r, hr⟩
  apply hn
  rw [hr, map_mul, cofactor_on_left, zero_mul]

theorem old_line_prime [CharP K 2] {M : ℕ} (hM : 3 ≤ M) {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i : Fin M) : Prime (linearForm (a i)) := by
  obtain ⟨c, u, hu, heq⟩ := exists_chart_normalization (a i) (arc_column_ne_zero hM ha i)
  rw [heq, map_smul, ← ChartFrobenius.polynomial_eq_linearForm_normal, MvPolynomial.smul_eq_C_mul]
  apply prime_mul_iff.mpr
  exact Or.inr ⟨(isUnit_iff_ne_zero.mpr hu).map MvPolynomial.C, PlaneLineChart.polynomial_prime c⟩

theorem lineProduct_dvd_of_each [CharP K 2] {M : ℕ} (hM : 3 ≤ M)
    {a : Fin M → Fin 3 → K} (ha : Arc.IsArc (K := K) 3 a)
    (p : MvPolynomial (Fin 3) K) (hdiv : ∀ i, linearForm (a i) ∣ p) : lineProduct a ∣ p := by
  classical
  have hdvd (s : Finset (Fin M)) : (∏ i ∈ s, linearForm (a i)) ∣ p := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      obtain ⟨r, hr⟩ := ih
      have hpi := hdiv i
      rw [hr] at hpi
      have hnot : ¬ linearForm (a i) ∣ ∏ k ∈ s, linearForm (a k) := by
        intro h
        obtain ⟨k, hk, hdiv'⟩ := (old_line_prime hM ha i).dvd_finset_prod_iff _ |>.mp h
        exact old_lines_nondividing hM ha i k (by intro heq; subst k; exact hi hk) hdiv'
      obtain ⟨t, ht⟩ := ((old_line_prime hM ha i).dvd_or_dvd hpi).resolve_left hnot
      refine ⟨t, ?_⟩
      rw [hr, ht]
      ac_rfl
  exact hdvd Finset.univ

end EvenOrderMDS.PlaneCofactorGeometry
