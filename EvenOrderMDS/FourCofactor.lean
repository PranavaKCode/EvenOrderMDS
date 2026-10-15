module

public import EvenOrderMDS.RankFourStar
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public noncomputable section

/-! Literal four-dimensional cofactor vectors and their one-dimensional intersection property. -/

namespace EvenOrderMDS.FourCofactor

open scoped BigOperators Matrix

variable {K : Type*} [Field K]

noncomputable def detLast (a b c : Fin 4 → K) : (Fin 4 → K) →ₗ[K] K :=
  (Matrix.detRowAlternating (n := Fin 4) (R := K)).toMultilinearMap.toLinearMap ![a, b, c, 0] 3

theorem detLast_apply (a b c x : Fin 4 → K) : detLast a b c x = Matrix.det ![a, b, c, x] := by
  change Matrix.det (Function.update ![a, b, c, 0] 3 x) = _
  congr 1
  funext i
  fin_cases i <;> simp

noncomputable def cofactor (a b c : Fin 4 → K) : Fin 4 → K :=
  fun i => detLast a b c (Pi.single i 1)

theorem cofactor_dot (a b c x : Fin 4 → K) :
    cofactor a b c ⬝ᵥ x = Matrix.det ![a, b, c, x] := by
  have hx : (∑ i, x i • (Pi.single i (1 : K) : Fin 4 → K)) = x := by
    funext j
    simp [Pi.single_apply]
  symm
  calc
    _ = detLast a b c x := (detLast_apply a b c x).symm
    _ = detLast a b c (∑ i, x i • (Pi.single i (1 : K) : Fin 4 → K)) := congrArg _ hx.symm
    _ = ∑ i, x i * cofactor a b c i := by simp [cofactor]
    _ = _ := by simp [dotProduct, mul_comm]

theorem cofactor_on_first (a b c : Fin 4 → K) : a ⬝ᵥ cofactor a b c = 0 := by
  rw [dotProduct_comm, cofactor_dot]
  apply Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 3) (by decide)
  rfl

theorem cofactor_on_second (a b c : Fin 4 → K) : b ⬝ᵥ cofactor a b c = 0 := by
  rw [dotProduct_comm, cofactor_dot]
  apply Matrix.det_zero_of_row_eq (i := (1 : Fin 4)) (j := 3) (by decide)
  rfl

theorem cofactor_on_third (a b c : Fin 4 → K) : c ⬝ᵥ cofactor a b c = 0 := by
  rw [dotProduct_comm, cofactor_dot]
  apply Matrix.det_zero_of_row_eq (i := (2 : Fin 4)) (j := 3) (by decide)
  rfl

theorem cofactor_ne_zero_of_det_ne_zero (a b c d : Fin 4 → K)
    (hd : Matrix.det ![a, b, c, d] ≠ 0) : cofactor a b c ≠ 0 := by
  intro hz
  apply hd
  rw [← cofactor_dot, hz]
  simp

theorem proportional_of_three_equations (a b c d x : Fin 4 → K)
    (hd : Matrix.det ![a, b, c, d] ≠ 0)
    (ha : a ⬝ᵥ x = 0) (hb : b ⬝ᵥ x = 0) (hc : c ⬝ᵥ x = 0) :
    x = (d ⬝ᵥ x / Matrix.det ![a, b, c, d]) • cofactor a b c := by
  have hu := (Matrix.isUnit_iff_isUnit_det ![a, b, c, d]).mpr (isUnit_iff_ne_zero.mpr hd)
  have hinj := (Matrix.mulVec_injective_iff_isUnit).mpr hu
  apply hinj
  funext i
  fin_cases i
  · change a ⬝ᵥ x = a ⬝ᵥ (_ • cofactor a b c)
    simp [dotProduct_smul, ha, cofactor_on_first]
  · change b ⬝ᵥ x = b ⬝ᵥ (_ • cofactor a b c)
    simp [dotProduct_smul, hb, cofactor_on_second]
  · change c ⬝ᵥ x = c ⬝ᵥ (_ • cofactor a b c)
    simp [dotProduct_smul, hc, cofactor_on_third]
  · change d ⬝ᵥ x = d ⬝ᵥ (_ • cofactor a b c)
    rw [dotProduct_smul, dotProduct_comm d (cofactor a b c), cofactor_dot]
    exact (div_mul_cancel₀ _ hd).symm

theorem exists_fourth_label {M : ℕ} (hM : 4 ≤ M) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ∃ l : Fin M, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  classical
  have hcard : ({i, j, k} : Finset (Fin M)).card = 3 := by simp [hij, hik, hjk]
  have hlt : ({i, j, k} : Finset (Fin M)).card < (Finset.univ : Finset (Fin M)).card := by
    rw [hcard, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨l, by simpa using hl⟩

theorem arc_four_independent {M : ℕ} {a : Fin M → Fin 4 → K}
    (ha : Arc.IsArc (K := K) 4 a) (i j k l : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    LinearIndependent K ![a i, a j, a k, a l] := by
  let e : Fin 4 ↪ Fin M := ⟨![i, j, k, l], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all⟩
  convert ha e using 1
  funext t
  fin_cases t <;> rfl

theorem arc_four_determinant_ne_zero {M : ℕ} {a : Fin M → Fin 4 → K}
    (ha : Arc.IsArc (K := K) 4 a) (i j k l : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : Matrix.det ![a i, a j, a k, a l] ≠ 0 := by
  have hlin := arc_four_independent ha i j k l hij hik hil hjk hjl hkl
  exact ((Matrix.isUnit_iff_isUnit_det ![a i, a j, a k, a l]).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hlin)).ne_zero

theorem arc_cofactor_ne_zero {M : ℕ} (hM : 4 ≤ M) {a : Fin M → Fin 4 → K}
    (ha : Arc.IsArc (K := K) 4 a) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : cofactor (a i) (a j) (a k) ≠ 0 := by
  obtain ⟨l, hli, hlj, hlk⟩ := exists_fourth_label hM i j k hij hik hjk
  apply cofactor_ne_zero_of_det_ne_zero _ _ _ (a l)
  exact arc_four_determinant_ne_zero ha i j k l hij hik hli.symm hjk hlj.symm hlk.symm

theorem eval_linearForm_eq_dot (a x : Fin 4 → K) :
    MvPolynomial.eval x (LinearCoordinates.linearForm a) = a ⬝ᵥ x := by
  simp [LinearCoordinates.linearForm_apply, dotProduct]

theorem arc_cofactor_avoids_other {M : ℕ} {a : Fin M → Fin 4 → K}
    (ha : Arc.IsArc (K := K) 4 a) (i j k l : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    MvPolynomial.eval (cofactor (a i) (a j) (a k)) (LinearCoordinates.linearForm (a l)) ≠ 0 := by
  rw [eval_linearForm_eq_dot, dotProduct_comm, cofactor_dot]
  exact arc_four_determinant_ne_zero ha i j k l hij hik hil hjk hjl hkl

theorem triple_intersection_proportional {M : ℕ} (hM : 4 ≤ M) {a : Fin M → Fin 4 → K}
    (ha : Arc.IsArc (K := K) 4 a) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : Fin 4 → K)
    (hi : MvPolynomial.eval x (LinearCoordinates.linearForm (a i)) = 0)
    (hj : MvPolynomial.eval x (LinearCoordinates.linearForm (a j)) = 0)
    (hk : MvPolynomial.eval x (LinearCoordinates.linearForm (a k)) = 0) :
    ∃ s : K, x = s • cofactor (a i) (a j) (a k) := by
  obtain ⟨l, hli, hlj, hlk⟩ := exists_fourth_label hM i j k hij hik hjk
  have hd := arc_four_determinant_ne_zero ha i j k l hij hik hli.symm hjk hlj.symm hlk.symm
  rw [eval_linearForm_eq_dot] at hi hj hk
  exact ⟨_, proportional_of_three_equations (a i) (a j) (a k) (a l) x hd hi hj hk⟩

theorem zero_of_cofactor_values [CharP K 2] {M : ℕ} (hM : 4 ≤ M)
    (a : Fin M → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a)
    {p : MvPolynomial (Fin 4) K} {d : ℕ} (hp : p.IsHomogeneous d) (hdegree : d < M - 2)
    (hzero : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → MvPolynomial.eval (cofactor (a i) (a j) (a k)) p = 0) :
    p = 0 := by
  apply RankFourStar.zero_of_rank_four_star_vanishing hM a ha hp hdegree
  intro i j k hij hik hjk x _ hi hj hk
  obtain ⟨s, hs⟩ := triple_intersection_proportional hM ha i j k hij hik hjk x hi hj hk
  rw [hs, HomogeneousEvaluation.eval_smul hp, hzero i j k hij hik hjk, mul_zero]

theorem cofactor_coordinate [CharP K 2] (a b c : Fin 4 → K) (i : Fin 4) :
    cofactor a b c i = Matrix.det ![(fun j : Fin 3 => a (i.succAbove j)),
      (fun j : Fin 3 => b (i.succAbove j)), (fun j : Fin 3 => c (i.succAbove j))] := by
  rw [cofactor, detLast_apply]
  erw [Matrix.det_succ_row _ (3 : Fin 4)]
  change (∑ j : Fin 4, (-1 : K) ^ (3 + (j : ℕ)) * (Pi.single i (1 : K) : Fin 4 → K) j *
    Matrix.det (Matrix.submatrix ![a, b, c, (Pi.single i (1 : K) : Fin 4 → K)]
      (3 : Fin 4).succAbove j.succAbove)) = _
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, mul_one, CharTwo.neg_eq, one_pow, one_mul]
    congr 1
    ext r s
    fin_cases r <;> rfl
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

end EvenOrderMDS.FourCofactor
