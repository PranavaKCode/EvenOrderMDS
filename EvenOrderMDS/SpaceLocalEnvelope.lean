module

public import EvenOrderMDS.SpaceBinaryCoordinates
public import EvenOrderMDS.FourCofactorDerivatives

@[expose] public noncomputable section

/-! Binary local envelopes constructed at each old pair of a space arc. -/

namespace EvenOrderMDS.SpaceLocalEnvelope

open BinaryParameterization SpaceBinaryCoordinates FourCofactor FourCofactorDerivatives
open LinearCoordinates
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

def remaining {N : ℕ} (i : Fin (N + 2)) (j : Fin (N + 1)) (k : Fin N) : Fin (N + 2) :=
  i.succAbove (j.succAbove k)

theorem remaining_ne_first {N : ℕ} (i : Fin (N + 2)) (j : Fin (N + 1)) (k : Fin N) :
    remaining i j k ≠ i := Fin.succAbove_ne i _

theorem remaining_ne_second {N : ℕ} (i : Fin (N + 2)) (j : Fin (N + 1)) (k : Fin N) :
    remaining i j k ≠ i.succAbove j := by
  intro h
  exact Fin.succAbove_ne j k (Fin.succAbove_right_injective h)

theorem remaining_injective {N : ℕ} (i : Fin (N + 2)) (j : Fin (N + 1)) :
    Function.Injective (remaining i j) :=
  Fin.succAbove_right_injective.comp Fin.succAbove_right_injective

theorem exists_remaining {N : ℕ} (i : Fin (N + 2)) (j : Fin (N + 1))
    (k : Fin (N + 2)) (hki : k ≠ i) (hkj : k ≠ i.succAbove j) :
    ∃ l, remaining i j l = k := by
  obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq hki
  have huj : u ≠ j := by intro h; subst u; exact hkj hu.symm
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq huj
  exact ⟨l, by simp only [remaining, hl, hu]⟩

theorem complementary_product {R : Type*} [CommMonoid R] {N : ℕ}
    (f : Fin (N + 2) → R) (i : Fin (N + 2)) (j : Fin (N + 1)) (k : Fin N) :
    (∏ l ∈ Finset.univ.erase k, f (remaining i j l)) =
      ∏ l ∈ ((Finset.univ.erase i).erase (i.succAbove j)).erase (remaining i j k), f l := by
  classical
  apply Finset.prod_bij (fun l _ => remaining i j l)
  · intro l hl
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl ⊢
    exact ⟨fun h => hl (remaining_injective i j h), remaining_ne_second i j l, remaining_ne_first i j l⟩
  · intro l _ m _ h
    exact remaining_injective i j h
  · intro l hl
    have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2).1
    have hlj := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    obtain ⟨m, hm⟩ := exists_remaining i j l hli hlj
    refine ⟨m, ?_, hm⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    subst m
    exact (Finset.mem_erase.mp hl).1 hm.symm
  · intro l _
    rfl

omit [CharP K 2] [Fintype K] in
theorem eval_complement {N : ℕ} (a : Fin (N + 2) → Fin 4 → K)
    (i : Fin (N + 2)) (j : Fin (N + 1)) (x y : Fin 4 → K) (v : Fin 2 → K) (k : Fin N) :
    MvPolynomial.eval v
      (BinaryLocalQuotient.complement (fun l => rowMap x y (a (remaining i j l))) k) =
      MvPolynomial.eval (point x y v) (tripleComplement a i (i.succAbove j) (remaining i j k)) := by
  classical
  simp only [BinaryLocalQuotient.complement, tripleComplement, map_prod]
  rw [← complementary_product]
  apply Finset.prod_congr rfl
  intro l _
  rw [← restriction_linearForm, eval_restriction]

omit [Fintype K] in
theorem binary_arc {N : ℕ} (a : Fin (N + 2) → Fin 4 → K)
    (ha : Arc.IsArc (K := K) 4 a) (i : Fin (N + 2)) (j : Fin (N + 1))
    (c d : Fin 4 → K) (hd : Matrix.det ![a i, a (i.succAbove j), c, d] ≠ 0) :
    Arc.IsArc (K := K) 2 (fun k : Fin N =>
      rowMap (cofactor (a i) (a (i.succAbove j)) c) (cofactor (a i) (a (i.succAbove j)) d)
        (a (remaining i j k))) := by
  intro e
  have hpair := arc_four_determinant_ne_zero ha i (i.succAbove j) (remaining i j (e 0)) (remaining i j (e 1))
    (Fin.ne_succAbove i j) (remaining_ne_first i j (e 0)).symm (remaining_ne_first i j (e 1)).symm
    (remaining_ne_second i j (e 0)).symm (remaining_ne_second i j (e 1)).symm
    (fun h => (by decide : (0 : Fin 2) ≠ 1) (e.injective (remaining_injective i j h)))
  have hdet : Matrix.det ![
      rowMap (cofactor (a i) (a (i.succAbove j)) c) (cofactor (a i) (a (i.succAbove j)) d) (a (remaining i j (e 0))),
      rowMap (cofactor (a i) (a (i.succAbove j)) c) (cofactor (a i) (a (i.succAbove j)) d) (a (remaining i j (e 1)))] ≠ 0 := by
    rw [projected_determinant _ _ _ _ _ _ hd]
    exact mul_ne_zero hd hpair
  convert Matrix.linearIndependent_rows_of_det_ne_zero hdet using 1
  funext k
  fin_cases k <;> rfl

theorem exists_local_envelope {N t : ℕ} (hN : 2 ≤ N)
    (hsize : N + t = Fintype.card K + 1)
    (a : Fin (N + 2) → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    (i : Fin (N + 2)) (j : Fin (N + 1)) :
    ∃ x y : Fin 4 → K, ∃ v : Fin N → Fin 2 → K, ∃ T : MvPolynomial (Fin 2) K,
      T.IsHomogeneous t ∧
      (∀ k, point x y (v k) = cofactor (a i) (a (i.succAbove j)) (a (remaining i j k))) ∧
      (∀ k, MvPolynomial.eval (cofactor (a i) (a (i.succAbove j)) (a (remaining i j k)))
        (tripleComplement a i (i.succAbove j) (remaining i j k)) * MvPolynomial.eval (v k) T = 1) := by
  let u : Fin N := ⟨0, by omega⟩
  let w : Fin N := ⟨1, by omega⟩
  have huw : u ≠ w := by simp [u, w]
  let c := a (remaining i j u)
  let d := a (remaining i j w)
  have hd : Matrix.det ![a i, a (i.succAbove j), c, d] ≠ 0 :=
    arc_four_determinant_ne_zero ha i (i.succAbove j) _ _ (Fin.ne_succAbove i j)
      (remaining_ne_first i j u).symm (remaining_ne_first i j w).symm
      (remaining_ne_second i j u).symm (remaining_ne_second i j w).symm
      (fun h => huw (remaining_injective i j h))
  let x := cofactor (a i) (a (i.succAbove j)) c
  let y := cofactor (a i) (a (i.succAbove j)) d
  let v := fun k : Fin N => coordinates (a i) (a (i.succAbove j)) c d
    (cofactor (a i) (a (i.succAbove j)) (a (remaining i j k)))
  have hbinary := binary_arc a ha i j c d hd
  have hrel : ∀ k : Fin N, rowMap x y (a (remaining i j k)) =
      Matrix.det ![a i, a (i.succAbove j), c, d] • ![v k 1, v k 0] := by
    intro k
    exact cofactor_relation _ _ _ _ _ hd
  obtain ⟨T, hT, _, hvalues⟩ := BinaryLocalQuotient.exists_normalized_local_quotient
    hN hsize _ hbinary v (Matrix.det ![a i, a (i.succAbove j), c, d]) hrel
  have hv (k : Fin N) : point x y (v k) = cofactor (a i) (a (i.succAbove j)) (a (remaining i j k)) :=
    cofactor_coordinates _ _ _ _ _ hd
  refine ⟨x, y, v, T, hT, hv, ?_⟩
  intro k
  have h := hvalues k
  rw [map_mul, eval_complement, hv] at h
  exact h

end EvenOrderMDS.SpaceLocalEnvelope
