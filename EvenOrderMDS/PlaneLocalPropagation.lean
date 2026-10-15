module

public import EvenOrderMDS.PlaneLocalEnvelope

@[expose] public noncomputable section

/-! Local binary root counts propagate normalized values on a plane arc. -/

namespace EvenOrderMDS.PlaneLocalPropagation

open BinaryParameterization PlaneCofactorDerivatives
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

omit [CharP K 2] [Fintype K] in
theorem coordinate_nonzero {N : ℕ} (hN : 2 ≤ N)
    (a : Fin (N + 1) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (i : Fin (N + 1)) (x y : Fin 3 → K) (v : Fin N → Fin 2 → K)
    (hv : ∀ j, point x y (v j) = crossProduct (a i) (a (i.succAbove j))) (j : Fin N) :
    v j 0 ≠ 0 ∨ v j 1 ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : v j = 0 := by funext k; fin_cases k <;> simp [h.1, h.2]
  have hpoint := hv j
  rw [hz, point_zero] at hpoint
  exact PlaneCofactorGeometry.cofactor_ne_zero (by omega) ha i _ (Fin.ne_succAbove i j) hpoint.symm

omit [CharP K 2] [Fintype K] in
theorem coordinate_separated {N : ℕ} (hN : 2 ≤ N)
    (a : Fin (N + 1) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (i : Fin (N + 1)) (x y : Fin 3 → K) (v : Fin N → Fin 2 → K)
    (hv : ∀ j, point x y (v j) = crossProduct (a i) (a (i.succAbove j)))
    (j k : Fin N) (hjk : j ≠ k) : v j 0 * v k 1 ≠ v k 0 * v j 1 := by
  intro hdet
  obtain ⟨s, hs⟩ := ChartGeometry.proportional_of_binary_det_zero (v j) (v k)
    (coordinate_nonzero hN a ha i x y v hv j) hdet
  have hp : crossProduct (a i) (a (i.succAbove k)) = s • crossProduct (a i) (a (i.succAbove j)) := by
    rw [← hv k, hs, point_smul, hv j]
  have hn := PlaneCofactorGeometry.cofactor_avoids_other ha i (i.succAbove k) (i.succAbove j)
    (Fin.ne_succAbove i k) (Fin.ne_succAbove i j)
    (fun h => hjk (Fin.succAbove_right_injective h).symm)
  apply hn
  rw [hp, HomogeneousEvaluation.eval_smul (LinearCoordinates.linearForm_homogeneous _),
    cofactor_on_right, mul_zero]

theorem propagate_from_subset {N t : ℕ} (hN : 2 ≤ N)
    (hsize : N + t = Fintype.card K + 1)
    (a : Fin (N + 1) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (i : Fin (N + 1)) (S : Finset (Fin (N + 1))) (hi : i ∉ S) (hcard : t < S.card)
    (hvalues : ∀ j ∈ S, MvPolynomial.eval (crossProduct (a i) (a j))
      (pairComplement a i j * F) = 1) :
    ∀ j, i ≠ j → MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F) = 1 := by
  classical
  obtain ⟨x, y, v, T, hT, _, hv, hlocal⟩ := PlaneLocalEnvelope.exists_local_envelope hN hsize a ha i
  have hex (j : S) : ∃ k, i.succAbove k = j.val :=
    Fin.exists_succAbove_eq (fun h => hi (h ▸ j.property))
  let f : S → Fin N := fun j => Classical.choose (hex j)
  have hf (j : S) : i.succAbove (f j) = j.val := Classical.choose_spec (hex j)
  have hinj : Function.Injective f := by
    intro j k h
    apply Subtype.ext
    rw [← hf j, ← hf k, h]
  have heq : restriction x y F = T := by
    apply sub_eq_zero.mp
    apply BinaryRootBound.zero_of_projective_roots
      ((restriction_homogeneous x y hF).sub hT) (fun j : S => v (f j))
    · intro j
      exact coordinate_nonzero hN a ha i x y v hv (f j)
    · intro j k hjk
      exact coordinate_separated hN a ha i x y v hv _ _ (fun h => hjk (hinj h))
    · intro j
      rw [map_sub, eval_restriction, hv, sub_eq_zero]
      have h1 := hvalues j.val j.property
      have h2 := hlocal (f j)
      rw [hf j] at h2 ⊢
      rw [map_mul] at h1
      apply mul_left_cancel₀ (PlaneCofactorGeometry.pairComplement_eval_ne_zero ha i j.val
        (fun h => hi (h ▸ j.property)))
      exact h1.trans h2.symm
    · simpa using hcard
  intro j hij
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij.symm
  rw [map_mul, ← hv k, ← eval_restriction x y (v k) F, heq, hv k]
  exact hlocal k

end EvenOrderMDS.PlaneLocalPropagation
