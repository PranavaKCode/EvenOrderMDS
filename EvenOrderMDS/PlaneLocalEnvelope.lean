module

public import EvenOrderMDS.PlaneBinaryCoordinates

@[expose] public noncomputable section

/-! Binary local envelopes supplied by actual plane arcs. -/

namespace EvenOrderMDS.PlaneLocalEnvelope

open BinaryParameterization PlaneBinaryCoordinates LinearCoordinates PlaneCofactorDerivatives
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

omit [CharP K 2] [Fintype K] in
theorem complementary_product {R : Type*} [CommMonoid R] {N : ℕ}
    (f : Fin (N + 1) → R) (i : Fin (N + 1)) (j : Fin N) :
    (∏ k ∈ Finset.univ.erase j, f (i.succAbove k)) =
      ∏ k ∈ (Finset.univ.erase i).erase (i.succAbove j), f k := by
  classical
  apply Finset.prod_bij (fun k _ => i.succAbove k)
  · intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk ⊢
    exact ⟨fun h => hk (Fin.succAbove_right_injective h), Fin.succAbove_ne i k⟩
  · intro k _ l _ h
    exact Fin.succAbove_right_injective h
  · intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hki
    refine ⟨l, ?_, hl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    subst l
    exact (Finset.mem_erase.mp hk).1 hl.symm
  · intro k _
    rfl

omit [CharP K 2] [Fintype K] in
theorem eval_complement {N : ℕ} (a : Fin (N + 1) → Fin 3 → K)
    (i : Fin (N + 1)) (x y : Fin 3 → K) (v : Fin 2 → K) (j : Fin N) :
    MvPolynomial.eval v
      (BinaryLocalQuotient.complement (fun k => rowMap x y (a (i.succAbove k))) j) =
      MvPolynomial.eval (point x y v) (pairComplement a i (i.succAbove j)) := by
  classical
  simp only [BinaryLocalQuotient.complement, pairComplement, map_prod]
  rw [← complementary_product]
  apply Finset.prod_congr rfl
  intro k _
  rw [← restriction_linearForm, eval_restriction]

theorem exists_local_envelope {N t : ℕ} (hN : 2 ≤ N)
    (hsize : N + t = Fintype.card K + 1)
    (a : Fin (N + 1) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (i : Fin (N + 1)) :
    ∃ x y : Fin 3 → K, ∃ v : Fin N → Fin 2 → K, ∃ T : MvPolynomial (Fin 2) K,
      T.IsHomogeneous t ∧
      LinearMap.ker (rowMap x y) = Submodule.span K {a i} ∧
      (∀ j, point x y (v j) = crossProduct (a i) (a (i.succAbove j))) ∧
      (∀ j, MvPolynomial.eval (crossProduct (a i) (a (i.succAbove j)))
        (pairComplement a i (i.succAbove j)) * MvPolynomial.eval (v j) T = 1) := by
  obtain ⟨b, hbi, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  obtain ⟨c, hci, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt i b (by omega)
  have hd := PlaneCofactorGeometry.determinant_three_ne_zero ha i b c hbi.symm hci.symm hcb.symm
  let x := crossProduct (a i) (a b)
  let y := crossProduct (a i) (a c)
  let v := fun j : Fin N => coordinates (a i) (a b) (a c) (crossProduct (a i) (a (i.succAbove j)))
  have hk : LinearMap.ker (rowMap x y) = Submodule.span K {a i} := rowMap_kernel _ _ _ hd
  have hbinary := ArcContraction.contract ha i (rowMap x y) hk
  have hrel : ∀ j : Fin N, rowMap x y (a (i.succAbove j)) =
      Matrix.det ![a i, a b, a c] • ![v j 1, v j 0] := by
    intro j
    exact cofactor_relation _ _ _ _ hd
  obtain ⟨T, hT, _, hvalues⟩ := BinaryLocalQuotient.exists_normalized_local_quotient
    hN hsize _ hbinary v (Matrix.det ![a i, a b, a c]) hrel
  have hv (j : Fin N) : point x y (v j) = crossProduct (a i) (a (i.succAbove j)) :=
    cofactor_coordinates _ _ _ _ hd
  refine ⟨x, y, v, T, hT, hk, hv, ?_⟩
  intro j
  have h := hvalues j
  rw [map_mul, eval_complement, hv] at h
  exact h

end EvenOrderMDS.PlaneLocalEnvelope
