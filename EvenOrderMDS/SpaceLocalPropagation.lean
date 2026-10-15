module

public import EvenOrderMDS.SpaceLocalEnvelope
public import EvenOrderMDS.NormalizedEnvelopeUniqueness

@[expose] public noncomputable section

/-! Root-count propagation of literal normalized values on each old space-arc pair. -/

namespace EvenOrderMDS.SpaceLocalPropagation

open BinaryParameterization SpaceLocalEnvelope FourCofactor FourCofactorDerivatives

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

omit [CharP K 2] [Fintype K] in
theorem coordinate_nonzero {N : ℕ} (hN : 2 ≤ N)
    (a : Fin (N + 2) → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    (i : Fin (N + 2)) (j : Fin (N + 1)) (x y : Fin 4 → K) (v : Fin N → Fin 2 → K)
    (hv : ∀ k, point x y (v k) = cofactor (a i) (a (i.succAbove j)) (a (remaining i j k)))
    (k : Fin N) : v k 0 ≠ 0 ∨ v k 1 ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : v k = 0 := by funext l; fin_cases l <;> simp [h.1, h.2]
  have hpoint := hv k
  rw [hz, point_zero] at hpoint
  exact arc_cofactor_ne_zero (by omega) ha i (i.succAbove j) (remaining i j k)
    (Fin.ne_succAbove i j) (remaining_ne_first i j k).symm (remaining_ne_second i j k).symm hpoint.symm

omit [CharP K 2] [Fintype K] in
theorem coordinate_separated {N : ℕ} (hN : 2 ≤ N)
    (a : Fin (N + 2) → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    (i : Fin (N + 2)) (j : Fin (N + 1)) (x y : Fin 4 → K) (v : Fin N → Fin 2 → K)
    (hv : ∀ k, point x y (v k) = cofactor (a i) (a (i.succAbove j)) (a (remaining i j k)))
    (k l : Fin N) (hkl : k ≠ l) : v k 0 * v l 1 ≠ v l 0 * v k 1 := by
  intro hdet
  obtain ⟨s, hs⟩ := ChartGeometry.proportional_of_binary_det_zero (v k) (v l)
    (coordinate_nonzero hN a ha i j x y v hv k) hdet
  have hp : cofactor (a i) (a (i.succAbove j)) (a (remaining i j l)) =
      s • cofactor (a i) (a (i.succAbove j)) (a (remaining i j k)) := by
    rw [← hv l, hs, point_smul, hv k]
  have hn := arc_cofactor_avoids_other ha i (i.succAbove j) (remaining i j l) (remaining i j k)
    (Fin.ne_succAbove i j) (remaining_ne_first i j l).symm (remaining_ne_first i j k).symm
    (remaining_ne_second i j l).symm (remaining_ne_second i j k).symm
    (fun h => hkl (remaining_injective i j h).symm)
  apply hn
  rw [hp, HomogeneousEvaluation.eval_smul (LinearCoordinates.linearForm_homogeneous _),
    eval_linearForm_eq_dot, cofactor_on_third, mul_zero]

theorem propagate_from_subset {N t : ℕ} (hN : 2 ≤ N)
    (hsize : N + t = Fintype.card K + 1)
    (a : Fin (N + 2) → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous t)
    (i j : Fin (N + 2)) (hij : i ≠ j) (S : Finset (Fin (N + 2)))
    (hi : i ∉ S) (hj : j ∉ S) (hcard : t < S.card)
    (hvalues : ∀ k ∈ S, MvPolynomial.eval (cofactor (a i) (a j) (a k))
      (tripleComplement a i j k * F) = 1) :
    ∀ k, i ≠ k → j ≠ k →
      MvPolynomial.eval (cofactor (a i) (a j) (a k)) (tripleComplement a i j k * F) = 1 := by
  classical
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hij.symm
  obtain ⟨x, y, v, T, hT, hv, hlocal⟩ := exists_local_envelope hN hsize a ha i j
  have hex (k : S) : ∃ l, remaining i j l = k.val :=
    exists_remaining i j k.val (fun h => hi (h ▸ k.property)) (fun h => hj (h ▸ k.property))
  let f : S → Fin N := fun k => Classical.choose (hex k)
  have hf (k : S) : remaining i j (f k) = k.val := Classical.choose_spec (hex k)
  have hinj : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    rw [← hf k, ← hf l, h]
  have heq : restriction x y F = T := by
    apply sub_eq_zero.mp
    apply BinaryRootBound.zero_of_projective_roots
      ((restriction_homogeneous x y hF).sub hT) (fun k : S => v (f k))
    · intro k
      exact coordinate_nonzero hN a ha i j x y v hv (f k)
    · intro k l hkl
      exact coordinate_separated hN a ha i j x y v hv _ _ (fun h => hkl (hinj h))
    · intro k
      rw [map_sub, eval_restriction, hv, sub_eq_zero]
      have h1 := hvalues k.val k.property
      have h2 := hlocal (f k)
      rw [hf k] at h2 ⊢
      rw [map_mul] at h1
      apply mul_left_cancel₀ (NormalizedEnvelopeUniqueness.tripleComplement_eval_ne_zero ha i (i.succAbove j) k.val
        hij (fun h => hi (h ▸ k.property)) (fun h => hj (h ▸ k.property)))
      exact h1.trans h2.symm
    · simpa using hcard
  intro k hik hjk
  obtain ⟨l, rfl⟩ := exists_remaining i j k hik.symm hjk.symm
  rw [map_mul, ← hv l, ← eval_restriction x y (v l) F, heq, hv l]
  exact hlocal l

end EvenOrderMDS.SpaceLocalPropagation
