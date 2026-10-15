module

public import EvenOrderMDS.StarInterpolation
public import EvenOrderMDS.PlaneCofactorGeometry

@[expose] public noncomputable section

/-! Concrete interpolation on a subset of the plane-arc star points. -/

namespace EvenOrderMDS.PlaneStarInterpolation

open LinearCoordinates PlaneCofactorDerivatives
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2]

theorem cross_symmetric (a b : Fin 3 → K) : crossProduct a b = crossProduct b a := by
  rw [← cross_anticomm b a]
  funext i
  exact CharTwo.neg_eq _

theorem cofactor_pair_set_eq {M : ℕ} (a : Fin M → Fin 3 → K)
    (i j u v : Fin M) (hij : i ≠ j) (huv : u ≠ v) (heq : ({i, j} : Finset (Fin M)) = {u, v}) :
    crossProduct (a i) (a j) = crossProduct (a u) (a v) := by
  have hi : i = u ∨ i = v := by have h : i ∈ ({u, v} : Finset (Fin M)) := heq ▸ (by simp); simpa using h
  have hj : j = u ∨ j = v := by have h : j ∈ ({u, v} : Finset (Fin M)) := heq ▸ (by simp); simpa using h
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · rfl
  · exact cross_symmetric _ _
  · exact (hij rfl).elim

theorem exists_subset_cofactor {M : ℕ} (a : Fin M → Fin 3 → K) :
    ∃ p : Finset (Fin M) → Fin 3 → K,
      ∀ i j, i ≠ j → p {i, j} = crossProduct (a i) (a j) := by
  classical
  have hex (S : Finset (Fin M)) : ∃ z : Fin 3 → K,
      ∀ i j, i ≠ j → S = {i, j} → z = crossProduct (a i) (a j) := by
    by_cases hS : S.card = 2
    · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hS
      exact ⟨crossProduct (a u) (a v), fun i j hij heq => cofactor_pair_set_eq a u v i j huv hij heq⟩
    · refine ⟨0, ?_⟩
      intro i j hij heq
      exact (hS (by rw [heq]; simp [hij])).elim
  choose p hp using hex
  exact ⟨p, fun i j hij => hp {i, j} i j hij rfl⟩

omit [CharP K 2] in
theorem basis_complement_pair {M : ℕ} (a : Fin M → Fin 3 → K) (i j : Fin M) :
    StarInterpolation.basisPolynomial (fun k => linearForm (a k)) Finset.univ {i, j} =
      pairComplement a i j := by
  classical
  unfold StarInterpolation.basisPolynomial pairComplement
  congr 1
  ext k
  simp [and_comm]

theorem exists_interpolant_on_subset {M t : ℕ} (a : Fin M → Fin 3 → K)
    (ha : Arc.IsArc (K := K) 3 a) (E : Finset (Fin M)) (hE : E.card = t + 2) :
    ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous t ∧
      ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
        MvPolynomial.eval (crossProduct (a i) (a j)) (pairComplement a i j * F) = 1 := by
  classical
  obtain ⟨p, hp⟩ := exists_subset_cofactor a
  let L := fun k => linearForm (a k)
  let w := fun S => (MvPolynomial.eval (p S) (StarInterpolation.basisPolynomial L Finset.univ S))⁻¹
  let F := StarInterpolation.interpolate L E 2 p w
  have hF : F.IsHomogeneous t := by
    have h := StarInterpolation.interpolate_homogeneous L (fun k => linearForm_homogeneous (a k)) E 2 p w
    simpa only [hE, Nat.add_sub_cancel] using h
  have hzero : ∀ S ∈ E.powersetCard 2, ∀ i ∈ S, MvPolynomial.eval (p S) (L i) = 0 := by
    intro S hS i hi
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hS).2
    rw [hp u v huv]
    rcases (show i = u ∨ i = v by simpa using hi) with rfl | rfl
    · exact cofactor_on_left _ _
    · exact cofactor_on_right _ _
  have hne : ∀ S ∈ E.powersetCard 2, ∀ i ∈ E \ S, MvPolynomial.eval (p S) (L i) ≠ 0 := by
    intro S hS i hi
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hS).2
    rw [hp u v huv]
    have hin := (Finset.mem_sdiff.mp hi).2
    have hiu : u ≠ i := by intro h; apply hin; simp [h]
    have hiv : v ≠ i := by intro h; apply hin; simp [h]
    exact PlaneCofactorGeometry.cofactor_avoids_other ha u v i huv hiu hiv
  refine ⟨F, hF, ?_⟩
  intro i hi j hj hij
  have hmem : ({i, j} : Finset (Fin M)) ∈ E.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    refine ⟨?_, by simp [hij]⟩
    intro k hk
    rcases (show k = i ∨ k = j by simpa using hk) with rfl | rfl
    · exact hi
    · exact hj
  have h := StarInterpolation.interpolate_values L E 2 p w hzero hne {i, j} hmem
  change MvPolynomial.eval (p {i, j}) F =
    (MvPolynomial.eval (p {i, j}) (StarInterpolation.basisPolynomial L Finset.univ {i, j}))⁻¹ at h
  rw [hp i j hij, basis_complement_pair] at h
  rw [map_mul, h]
  exact mul_inv_cancel₀ (PlaneCofactorGeometry.pairComplement_eval_ne_zero ha i j hij)

end EvenOrderMDS.PlaneStarInterpolation
