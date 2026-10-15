module

public import EvenOrderMDS.SpaceStarInterpolation
public import EvenOrderMDS.SpaceLocalPropagation

@[expose] public noncomputable section

/-!
# Constructed normalized envelope for an actual space arc

Local binary quotients, finite homogeneous star interpolation and three passes
of root-count propagation construct every normalized cofactor value.
-/

namespace EvenOrderMDS.NormalizedSpaceEnvelope

open FourCofactor FourCofactorDerivatives NormalizedSpaceHighest

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

omit [CharP K 2] [Fintype K] in
theorem tripleComplement_swap_first {M : ℕ} (a : Fin M → Fin 4 → K) (i j k : Fin M) :
    tripleComplement a i j k = tripleComplement a j i k := by
  classical
  unfold tripleComplement
  congr 1
  ext l
  simp [and_comm]

omit [CharP K 2] [Fintype K] in
theorem tripleComplement_swap_last {M : ℕ} (a : Fin M → Fin 4 → K) (i j k : Fin M) :
    tripleComplement a i j k = tripleComplement a i k j := by
  classical
  unfold tripleComplement
  congr 1
  ext l
  simp [and_comm, and_left_comm, and_assoc]

omit [Fintype K] in
theorem normalized_value_swap_first {M : ℕ} (a : Fin M → Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) (i j k : Fin M) :
    MvPolynomial.eval (cofactor (a i) (a j) (a k)) (tripleComplement a i j k * F) =
      MvPolynomial.eval (cofactor (a j) (a i) (a k)) (tripleComplement a j i k * F) := by
  rw [SpaceStarInterpolation.cofactor_swap_first (a i) (a j), tripleComplement_swap_first a i j]

omit [Fintype K] in
theorem normalized_value_swap_last {M : ℕ} (a : Fin M → Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) (i j k : Fin M) :
    MvPolynomial.eval (cofactor (a i) (a j) (a k)) (tripleComplement a i j k * F) =
      MvPolynomial.eval (cofactor (a i) (a k) (a j)) (tripleComplement a i k j * F) := by
  rw [SpaceStarInterpolation.cofactor_swap_last (a i) (a j) (a k), tripleComplement_swap_last a i j k]

theorem exists_normalized_envelope {N t : ℕ} (hN : 2 ≤ N)
    (hsize : N + t = Fintype.card K + 1) (ht : 2 * t ≤ Fintype.card K)
    (a : Fin (N + 2) → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a) :
    ∃ F : MvPolynomial (Fin 4) K, F.IsHomogeneous t ∧ HasNormalizedValues a F := by
  classical
  obtain ⟨E, _, hE⟩ := Finset.exists_subset_card_eq
    (show t + 3 ≤ (Finset.univ : Finset (Fin (N + 2))).card by simp; omega)
  obtain ⟨F, hF, hbase⟩ := SpaceStarInterpolation.exists_interpolant_on_subset a ha E hE
  have hcard (i j : Fin (N + 2)) : t < ((E.erase i).erase j).card := by
    have h1 : E.card - 1 ≤ (E.erase i).card := Finset.pred_card_le_card_erase
    have h2 : (E.erase i).card - 1 ≤ ((E.erase i).erase j).card := Finset.pred_card_le_card_erase
    omega
  have hnot (i j : Fin (N + 2)) : i ∉ (E.erase i).erase j := by simp
  have hfirst : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → ∀ k, i ≠ k → j ≠ k →
      MvPolynomial.eval (cofactor (a i) (a j) (a k)) (tripleComplement a i j k * F) = 1 := by
    intro i hi j hj hij
    apply SpaceLocalPropagation.propagate_from_subset hN hsize a ha F hF i j hij
      ((E.erase i).erase j) (hnot i j) (Finset.notMem_erase j _) (hcard i j)
    intro k hk
    exact hbase i hi j hj k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)) hij
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)).symm (Finset.ne_of_mem_erase hk).symm
  have hsecond : ∀ i ∈ E, ∀ j, i ≠ j → ∀ k, i ≠ k → j ≠ k →
      MvPolynomial.eval (cofactor (a i) (a j) (a k)) (tripleComplement a i j k * F) = 1 := by
    intro i hi j hij
    apply SpaceLocalPropagation.propagate_from_subset hN hsize a ha F hF i j hij
      ((E.erase i).erase j) (hnot i j) (Finset.notMem_erase j _) (hcard i j)
    intro k hk
    rw [normalized_value_swap_last]
    exact hfirst i hi k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)).symm j hij (Finset.ne_of_mem_erase hk)
  refine ⟨F, hF, ?_⟩
  intro i j k hij hik hjk
  apply SpaceLocalPropagation.propagate_from_subset hN hsize a ha F hF i j hij
    ((E.erase i).erase j) (hnot i j) (Finset.notMem_erase j _) (hcard i j) _ k hik hjk
  intro l hl
  rw [normalized_value_swap_last, normalized_value_swap_first]
  exact hsecond l (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl)) i
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)) j (Finset.ne_of_mem_erase hl) hij

theorem exists_space_envelope {n t M : ℕ} (hn : 1 ≤ n) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 3) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a) :
    ∃ F : MvPolynomial (Fin 4) K, F.IsHomogeneous t ∧ HasNormalizedValues a F := by
  cases M with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N => exact exists_normalized_envelope (by omega) (by omega) (by omega) a ha

theorem exists_space_envelope_highest {n t M : ℕ} (hn : 1 ≤ n) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 3) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a) :
    ∃ F : MvPolynomial (Fin 4) K, F.IsHomogeneous t ∧ HasNormalizedValues a F ∧
      (∀ i : Fin 4, thirdDerivative (ArcPolynomialFactors.allFactors a * F) i = MvPolynomial.X i ^ (2 * n)) ∧
      ∃ B : Fin 4 → MvPolynomial (Fin 4) K,
        (∀ i, (B i).IsHomogeneous (n + 1)) ∧
        ArcPolynomialFactors.allFactors a * F = QuaternaryParity.highest n + ParityDerivation.parityForm B := by
  obtain ⟨F, hF, hvalues⟩ := exists_space_envelope hn ht hsize hcard a ha
  exact ⟨F, hF, hvalues,
    literal_third_derivatives_of_normalized_space_envelope n t M hn ht hsize hcard a ha F hF hvalues,
    highest_form_of_normalized_space_envelope n t M hn ht hsize hcard a ha F hF hvalues⟩

end EvenOrderMDS.NormalizedSpaceEnvelope
