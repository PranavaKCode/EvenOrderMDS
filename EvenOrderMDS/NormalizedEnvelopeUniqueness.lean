module

public import EvenOrderMDS.NormalizedSpaceHighest
public import EvenOrderMDS.PlaneCofactorGeometry

@[expose] public noncomputable section

/-! Nonzero reciprocal denominators and uniqueness of normalized envelopes in both ranks. -/

namespace EvenOrderMDS.NormalizedEnvelopeUniqueness

variable {K : Type*} [Field K]

theorem tripleComplement_eval_ne_zero {M : ℕ} {a : Fin M → Fin 4 → K}
    (ha : Arc.IsArc (K := K) 4 a) (u v w : Fin M)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    MvPolynomial.eval (FourCofactor.cofactor (a u) (a v) (a w))
      (FourCofactorDerivatives.tripleComplement a u v w) ≠ 0 := by
  classical
  rw [FourCofactorDerivatives.tripleComplement, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hlw := (Finset.mem_erase.mp hl).1
  have hlv := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
  have hlu := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2).1
  exact FourCofactor.arc_cofactor_avoids_other ha u v w l huv huw hlu.symm hvw hlv.symm hlw.symm

theorem space_envelope_eval_ne_zero {M : ℕ} (a : Fin M → Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) (hvalues : NormalizedSpaceHighest.HasNormalizedValues a F)
    (u v w : Fin M) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    MvPolynomial.eval (FourCofactor.cofactor (a u) (a v) (a w)) F ≠ 0 := by
  have h := hvalues u v w huv huw hvw
  rw [map_mul] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem space_envelope_not_divisible_by_old_line {M : ℕ} (hM : 4 ≤ M)
    (a : Fin M → Fin 4 → K) (F : MvPolynomial (Fin 4) K)
    (hvalues : NormalizedSpaceHighest.HasNormalizedValues a F) (u : Fin M) :
    ¬ LinearCoordinates.linearForm (a u) ∣ F := by
  obtain ⟨v, hvu, _⟩ := Fin.exists_ne_and_ne_of_two_lt u u (by omega)
  obtain ⟨w, hwu, hwv⟩ := Fin.exists_ne_and_ne_of_two_lt u v (by omega)
  have hn := space_envelope_eval_ne_zero a F hvalues u v w hvu.symm hwu.symm hwv.symm
  rintro ⟨r, hr⟩
  apply hn
  rw [hr, map_mul, FourCofactor.eval_linearForm_eq_dot, FourCofactor.cofactor_on_first, zero_mul]

variable [CharP K 2]

theorem plane_envelope_unique {M d : ℕ} (hM : 3 ≤ M) (a : Fin M → Fin 3 → K)
    (ha : Arc.IsArc (K := K) 3 a) (hdegree : d < M - 1)
    (F G : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hFv : NormalizedPlaneHighest.HasNormalizedValues a F)
    (hGv : NormalizedPlaneHighest.HasNormalizedValues a G) : F = G := by
  apply sub_eq_zero.mp
  apply PlaneStarBound.zero_of_plane_arc_cofactor_values hM a ha (hF.sub hG) hdegree
  intro i j hij
  have hU := PlaneCofactorGeometry.pairComplement_eval_ne_zero ha i j hij
  have h1 := hFv i j hij
  have h2 := hGv i j hij
  rw [map_mul] at h1 h2
  rw [map_sub, sub_eq_zero]
  apply mul_left_cancel₀ hU
  exact h1.trans h2.symm

theorem space_envelope_unique {M d : ℕ} (hM : 4 ≤ M) (a : Fin M → Fin 4 → K)
    (ha : Arc.IsArc (K := K) 4 a) (hdegree : d < M - 2)
    (F G : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hFv : NormalizedSpaceHighest.HasNormalizedValues a F)
    (hGv : NormalizedSpaceHighest.HasNormalizedValues a G) : F = G := by
  apply sub_eq_zero.mp
  apply FourCofactor.zero_of_cofactor_values hM a ha (hF.sub hG) hdegree
  intro u v w huv huw hvw
  have hU := tripleComplement_eval_ne_zero ha u v w huv huw hvw
  have h1 := hFv u v w huv huw hvw
  have h2 := hGv u v w huv huw hvw
  rw [map_mul] at h1 h2
  rw [map_sub, sub_eq_zero]
  apply mul_left_cancel₀ hU
  exact h1.trans h2.symm

end EvenOrderMDS.NormalizedEnvelopeUniqueness
