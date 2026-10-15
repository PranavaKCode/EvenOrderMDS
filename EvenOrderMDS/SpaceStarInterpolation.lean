module

public import EvenOrderMDS.SpaceBinaryCoordinates
public import EvenOrderMDS.StarInterpolation
public import EvenOrderMDS.NormalizedEnvelopeUniqueness

@[expose] public noncomputable section

/-! Literal star interpolation for three-element subsets of a space arc. -/

namespace EvenOrderMDS.SpaceStarInterpolation

open FourCofactor FourCofactorDerivatives LinearCoordinates
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2]

theorem cofactor_swap_first (a b c : Fin 4 → K) : cofactor a b c = cofactor b a c := by
  funext l
  simp only [cofactor, detLast_apply]
  have h := SpaceBinaryCoordinates.det_swap_rows ![b, a, c, (Pi.single l (1 : K) : Fin 4 → K)] 0 1 (by decide)
  have hm : Matrix.submatrix ![b, a, c, (Pi.single l (1 : K) : Fin 4 → K)]
      (Equiv.swap (0 : Fin 4) 1) id = ![a, b, c, (Pi.single l (1 : K) : Fin 4 → K)] := by
    ext i j
    fin_cases i <;> rfl
  simpa only [hm] using h

theorem cofactor_swap_last (a b c : Fin 4 → K) : cofactor a b c = cofactor a c b := by
  funext l
  simp only [cofactor, detLast_apply]
  have h := SpaceBinaryCoordinates.det_swap_rows ![a, c, b, (Pi.single l (1 : K) : Fin 4 → K)] 1 2 (by decide)
  have hm : Matrix.submatrix ![a, c, b, (Pi.single l (1 : K) : Fin 4 → K)]
      (Equiv.swap (1 : Fin 4) 2) id = ![a, b, c, (Pi.single l (1 : K) : Fin 4 → K)] := by
    ext i j
    fin_cases i <;> rfl
  simpa only [hm] using h

theorem cofactor_triple_set_eq {M : ℕ} (a : Fin M → Fin 4 → K)
    (i j k u v w : Fin M) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (heq : ({i, j, k} : Finset (Fin M)) = {u, v, w}) :
    cofactor (a i) (a j) (a k) = cofactor (a u) (a v) (a w) := by
  have hi : i = u ∨ i = v ∨ i = w := by
    have h : i ∈ ({u, v, w} : Finset (Fin M)) := heq ▸ (by simp)
    simpa using h
  have hj : j = u ∨ j = v ∨ j = w := by
    have h : j ∈ ({u, v, w} : Finset (Fin M)) := heq ▸ (by simp)
    simpa using h
  have hk : k = u ∨ k = v ∨ k = w := by
    have h : k ∈ ({u, v, w} : Finset (Fin M)) := heq ▸ (by simp)
    simpa using h
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
  all_goals try contradiction
  all_goals simp only [cofactor_swap_first, cofactor_swap_last]

theorem exists_subset_cofactor {M : ℕ} (a : Fin M → Fin 4 → K) :
    ∃ p : Finset (Fin M) → Fin 4 → K,
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k → p {i, j, k} = cofactor (a i) (a j) (a k) := by
  classical
  have hex (S : Finset (Fin M)) : ∃ z : Fin 4 → K,
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k → S = {i, j, k} → z = cofactor (a i) (a j) (a k) := by
    by_cases hS : S.card = 3
    · obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hS
      exact ⟨cofactor (a u) (a v) (a w), fun i j k _ _ _ heq =>
        cofactor_triple_set_eq a u v w i j k huv huw hvw heq⟩
    · refine ⟨0, ?_⟩
      intro i j k hij hik hjk heq
      exact (hS (by rw [heq]; simp [hij, hik, hjk])).elim
  choose p hp using hex
  exact ⟨p, fun i j k hij hik hjk => hp {i, j, k} i j k hij hik hjk rfl⟩

omit [CharP K 2] in
theorem basis_complement_triple {M : ℕ} (a : Fin M → Fin 4 → K) (i j k : Fin M) :
    StarInterpolation.basisPolynomial (fun l => linearForm (a l)) Finset.univ {i, j, k} =
      tripleComplement a i j k := by
  classical
  unfold StarInterpolation.basisPolynomial tripleComplement
  congr 1
  ext l
  simp [and_comm, and_assoc]

theorem exists_interpolant_on_subset {M t : ℕ} (a : Fin M → Fin 4 → K)
    (ha : Arc.IsArc (K := K) 4 a) (E : Finset (Fin M)) (hE : E.card = t + 3) :
    ∃ F : MvPolynomial (Fin 4) K, F.IsHomogeneous t ∧
      ∀ i ∈ E, ∀ j ∈ E, ∀ k ∈ E, i ≠ j → i ≠ k → j ≠ k →
        MvPolynomial.eval (cofactor (a i) (a j) (a k)) (tripleComplement a i j k * F) = 1 := by
  classical
  obtain ⟨p, hp⟩ := exists_subset_cofactor a
  let L := fun k => linearForm (a k)
  let w := fun S => (MvPolynomial.eval (p S) (StarInterpolation.basisPolynomial L Finset.univ S))⁻¹
  let F := StarInterpolation.interpolate L E 3 p w
  have hF : F.IsHomogeneous t := by
    have h := StarInterpolation.interpolate_homogeneous L (fun k => linearForm_homogeneous (a k)) E 3 p w
    simpa only [hE, Nat.add_sub_cancel] using h
  have hzero : ∀ S ∈ E.powersetCard 3, ∀ i ∈ S, MvPolynomial.eval (p S) (L i) = 0 := by
    intro S hS i hi
    obtain ⟨u, v, z, huv, huz, hvz, rfl⟩ := Finset.card_eq_three.mp (Finset.mem_powersetCard.mp hS).2
    rw [hp u v z huv huz hvz]
    rcases (show i = u ∨ i = v ∨ i = z by simpa using hi) with rfl | rfl | rfl
    · rw [eval_linearForm_eq_dot]; exact cofactor_on_first _ _ _
    · rw [eval_linearForm_eq_dot]; exact cofactor_on_second _ _ _
    · rw [eval_linearForm_eq_dot]; exact cofactor_on_third _ _ _
  have hne : ∀ S ∈ E.powersetCard 3, ∀ i ∈ E \ S, MvPolynomial.eval (p S) (L i) ≠ 0 := by
    intro S hS i hi
    obtain ⟨u, v, z, huv, huz, hvz, rfl⟩ := Finset.card_eq_three.mp (Finset.mem_powersetCard.mp hS).2
    rw [hp u v z huv huz hvz]
    have hin := (Finset.mem_sdiff.mp hi).2
    have hiu : u ≠ i := by intro h; apply hin; simp [h]
    have hiv : v ≠ i := by intro h; apply hin; simp [h]
    have hiz : z ≠ i := by intro h; apply hin; simp [h]
    exact arc_cofactor_avoids_other ha u v z i huv huz hiu hvz hiv hiz
  refine ⟨F, hF, ?_⟩
  intro i hi j hj k hk hij hik hjk
  have hmem : ({i, j, k} : Finset (Fin M)) ∈ E.powersetCard 3 := by
    rw [Finset.mem_powersetCard]
    refine ⟨?_, by simp [hij, hik, hjk]⟩
    intro l hl
    rcases (show l = i ∨ l = j ∨ l = k by simpa using hl) with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  have h := StarInterpolation.interpolate_values L E 3 p w hzero hne {i, j, k} hmem
  change MvPolynomial.eval (p {i, j, k}) F =
    (MvPolynomial.eval (p {i, j, k}) (StarInterpolation.basisPolynomial L Finset.univ {i, j, k}))⁻¹ at h
  rw [hp i j k hij hik hjk, basis_complement_triple] at h
  rw [map_mul, h]
  exact mul_inv_cancel₀ (NormalizedEnvelopeUniqueness.tripleComplement_eval_ne_zero ha i j k hij hik hjk)

end EvenOrderMDS.SpaceStarInterpolation
