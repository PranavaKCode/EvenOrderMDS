module

public import EvenOrderMDS.ChartGeometry
public import Mathlib.LinearAlgebra.CrossProduct

@[expose] public noncomputable section

/-!
# Actual vertices of a general-position charted line arrangement

Vertices are literal cross products. General position is the nonvanishing
of every three-row determinant of the actual normal vectors.
-/

namespace EvenOrderMDS.CrossArrangement

open PlaneLineChart ChartGeometry ChartFrobenius
open scoped Matrix

variable {K : Type*} [Field K] [CharP K 2]

def GeneralPosition {M : ℕ} (c : Fin M → Chart K) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    Matrix.det ![normal (c k), normal (c i), normal (c j)] ≠ 0

def vertex {M : ℕ} (c : Fin M → Chart K) (i j : Fin M) : Fin 3 → K :=
  crossProduct (normal (c i)) (normal (c j))

theorem eval_polynomial_eq_dot (c : Chart K) (x : Fin 3 → K) :
    MvPolynomial.eval x (polynomial c) = normal c ⬝ᵥ x := by
  rw [polynomial_eq_linearForm_normal, LinearCoordinates.linearForm_apply]
  simp [dotProduct]

theorem eval_polynomial_smul (c : Chart K) (s : K) (x : Fin 3 → K) :
    MvPolynomial.eval (s • x) (polynomial c) = s * MvPolynomial.eval x (polynomial c) := by
  simp [eval_polynomial_eq_dot, dotProduct_smul, smul_eq_mul]

theorem vertex_on_first {M : ℕ} (c : Fin M → Chart K) (i j : Fin M) :
    MvPolynomial.eval (vertex c i j) (polynomial (c i)) = 0 := by
  rw [eval_polynomial_eq_dot]
  exact dot_self_cross _ _

theorem vertex_on_second {M : ℕ} (c : Fin M → Chart K) (i j : Fin M) :
    MvPolynomial.eval (vertex c i j) (polynomial (c j)) = 0 := by
  rw [eval_polynomial_eq_dot]
  exact dot_cross_self _ _

theorem vertex_off_third {M : ℕ} (c : Fin M → Chart K) (h : GeneralPosition c)
    (i j k : Fin M) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MvPolynomial.eval (vertex c i j) (polynomial (c k)) ≠ 0 := by
  rw [eval_polynomial_eq_dot]
  exact (triple_product_eq_det _ _ _).trans_ne (h i j k hij hik hjk)

theorem vertex_ne_zero {M : ℕ} (hM : 3 ≤ M) (c : Fin M → Chart K)
    (h : GeneralPosition c) (i j : Fin M) (hij : i ≠ j) : vertex c i j ≠ 0 := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have hn := vertex_off_third c h i j k hij hki.symm hkj.symm
  intro hz
  apply hn
  rw [hz, eval_polynomial_eq_dot]
  simp

theorem nondividing_factors {M : ℕ} (hM : 3 ≤ M) (c : Fin M → Chart K)
    (h : GeneralPosition c) (i j : Fin M) (hij : i ≠ j) :
    ¬ polynomial (c i) ∣ polynomial (c j) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have hn := vertex_off_third c h i k j hki.symm hij hkj
  rintro ⟨r, hr⟩
  apply hn
  rw [hr, map_mul, vertex_on_first, zero_mul]

theorem projected_vertices_separated {M : ℕ} (hM : 3 ≤ M) (c : Fin M → Chart K)
    (h : GeneralPosition c) (i j k : Fin M) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    project (c i) (vertex c i j) 0 * project (c i) (vertex c i k) 1 ≠
      project (c i) (vertex c i k) 0 * project (c i) (vertex c i j) 1 := by
  intro heq
  obtain ⟨s, hs⟩ := proportional_of_binary_det_zero _ _
    (project_nonzero_of_eval_zero (c i) _ (vertex_on_first c i j)
      (vertex_ne_zero hM c h i j hij)) heq
  have hv : vertex c i k = s • vertex c i j := by
    have hp := congrArg (point (c i)) hs
    rw [point_smul, point_project_of_eval_zero _ _ (vertex_on_first c i k),
      point_project_of_eval_zero _ _ (vertex_on_first c i j)] at hp
    exact hp
  have hn := vertex_off_third c h i k j hik hij hjk.symm
  apply hn
  rw [hv, eval_polynomial_smul, vertex_on_second, mul_zero]

noncomputable def configuration (M : ℕ) (hM : 2 ≤ M) (c : Fin (M + 1) → Chart K)
    (h : GeneralPosition c) : StarChartColon.Configuration K (M + 1) where
  charts := c
  vertices i t := project (c i) (vertex c i (i.succAbove t))
  nonzero i t := project_nonzero_of_eval_zero (c i) _ (vertex_on_first c i _)
    (vertex_ne_zero (by omega) c h i _ (Fin.ne_succAbove i t))
  separated i t u htu := projected_vertices_separated (by omega) c h i _ _
    (Fin.ne_succAbove i t) (Fin.ne_succAbove i u)
    (fun heq => htu (Fin.succAbove_right_injective heq))
  distinct := nondividing_factors (by omega) c h
  intersection i t := ⟨i.succAbove t, Fin.succAbove_ne i t,
    project (c (i.succAbove t)) (vertex c i (i.succAbove t)), by
      rw [point_project_of_eval_zero _ _ (vertex_on_first c i _),
        point_project_of_eval_zero _ _ (vertex_on_second c i _)]⟩

theorem exists_configuration {M : ℕ} (hM : 3 ≤ M) (c : Fin M → Chart K)
    (h : GeneralPosition c) :
    ∃ S : StarChartColon.Configuration K M, S.charts = c := by
  cases M with
  | zero => omega
  | succ m => exact ⟨configuration m (by omega) c h, rfl⟩

end EvenOrderMDS.CrossArrangement
