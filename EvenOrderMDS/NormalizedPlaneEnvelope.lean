module

public import EvenOrderMDS.PlaneStarInterpolation
public import EvenOrderMDS.PlaneLocalPropagation
public import EvenOrderMDS.NormalizedEnvelopeUniqueness

@[expose] public noncomputable section

/-!
# Constructed normalized envelope for an actual plane arc

The local binary quotients are instantiated from literal cofactor coordinates.
A finite star interpolant is propagated to every cofactor point by root counts.
-/

namespace EvenOrderMDS.NormalizedPlaneEnvelope

open PlaneCofactorDerivatives NormalizedPlaneHighest

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

omit [CharP K 2] [Fintype K] in
theorem pairComplement_symmetric {M : ℕ} (a : Fin M → Fin 3 → K) (i j : Fin M) :
    pairComplement a i j = pairComplement a j i := by
  classical
  unfold pairComplement
  congr 1
  ext k
  simp [and_comm]

omit [Fintype K] in
theorem normalized_value_symmetric {M : ℕ} (a : Fin M → Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) (i j : Fin M) :
    MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F) =
      MvPolynomial.eval (crossProduct (a j) (a i)) (pairComplement a j i * F) := by
  rw [PlaneStarInterpolation.cross_symmetric (a i) (a j), pairComplement_symmetric a i j]

theorem exists_normalized_envelope {N t : ℕ} (hN : 2 ≤ N)
    (hsize : N + t = Fintype.card K + 1) (ht : 2 * t ≤ Fintype.card K)
    (a : Fin (N + 1) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous t ∧ HasNormalizedValues a F := by
  classical
  obtain ⟨E, _, hE⟩ := Finset.exists_subset_card_eq
    (show t + 2 ≤ (Finset.univ : Finset (Fin (N + 1))).card by simp; omega)
  obtain ⟨F, hF, hbase⟩ := PlaneStarInterpolation.exists_interpolant_on_subset a ha E hE
  have hfirst : ∀ i ∈ E, ∀ j, i ≠ j →
      MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F) = 1 := by
    intro i hi
    apply PlaneLocalPropagation.propagate_from_subset hN hsize a ha F hF i (E.erase i)
      (Finset.notMem_erase i E)
    · rw [Finset.card_erase_of_mem hi, hE]
      omega
    · intro j hj
      exact hbase i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
  refine ⟨F, hF, ?_⟩
  intro i j hij
  by_cases hi : i ∈ E
  · exact hfirst i hi j hij
  · apply PlaneLocalPropagation.propagate_from_subset hN hsize a ha F hF i E hi
      (by omega) _ j hij
    intro k hk
    rw [normalized_value_symmetric]
    exact hfirst k hk i (fun h => hi (h ▸ hk))

theorem exists_plane_envelope {n t M : ℕ} (hn : 1 ≤ n) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous t ∧ HasNormalizedValues a F := by
  cases M with
  | zero => omega
  | succ N => exact exists_normalized_envelope (by omega) (by omega) (by omega) a ha

theorem exists_plane_envelope_highest {n t M : ℕ} (hn : 1 ≤ n) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous t ∧ HasNormalizedValues a F ∧
      (∀ i : Fin 3, secondDerivative (PlaneArcColon.lineProduct a * F) i = MvPolynomial.X i ^ (2 * n)) ∧
      ∃ S : MvPolynomial (Fin 3) K, S.IsHomogeneous (n + 1) ∧
        PlaneArcColon.lineProduct a * F = HighestPlaneForm.highest n + S ^ 2 := by
  obtain ⟨F, hF, hvalues⟩ := exists_plane_envelope hn ht hsize hcard a ha
  exact ⟨F, hF, hvalues,
    literal_second_derivatives_of_normalized_plane_envelope n t M hn ht hsize hcard a ha F hF hvalues,
    highest_form_of_normalized_plane_envelope n t M hn ht hsize hcard a ha F hF hvalues⟩

end EvenOrderMDS.NormalizedPlaneEnvelope
