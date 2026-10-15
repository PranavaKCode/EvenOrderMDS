module

public import EvenOrderMDS.StarChartColon

@[expose] public noncomputable section

/-! Actual chart coordinates for arbitrary points on a line. -/

namespace EvenOrderMDS.ChartGeometry

open PlaneLineChart

variable {K : Type*} [Field K]

def project (c : Chart K) (x : Fin 3 → K) : Fin 2 → K :=
  ![x (c.perm 0), x (c.perm 1)]

theorem project_point (c : Chart K) (v : Fin 2 → K) : project c (point c v) = v := by
  funext i
  fin_cases i <;> simp [project, point]

theorem point_injective (c : Chart K) : Function.Injective (point c) := by
  intro v w h
  have hp := congrArg (project c) h
  simpa only [project_point] using hp

theorem eval_polynomial (c : Chart K) (x : Fin 3 → K) :
    MvPolynomial.eval x (polynomial c) =
      x (c.perm 2) - c.a * x (c.perm 0) - c.b * x (c.perm 1) := by
  simp [polynomial, NormalizedLine.equation]

theorem eval_polynomial_point (c : Chart K) (v : Fin 2 → K) :
    MvPolynomial.eval (point c v) (polynomial c) = 0 := by
  rw [← eval_restrict, (restrict_zero_iff_divisible c (polynomial c)).mpr (dvd_refl _)]
  simp

theorem point_project_of_eval_zero (c : Chart K) (x : Fin 3 → K)
    (hx : MvPolynomial.eval x (polynomial c) = 0) : point c (project c x) = x := by
  rw [eval_polynomial] at hx
  have heq : x (c.perm 2) = c.a * x (c.perm 0) + c.b * x (c.perm 1) := by
    rw [← sub_add_eq_sub_sub, sub_eq_zero] at hx
    exact hx
  funext i
  obtain ⟨k, rfl⟩ := c.perm.surjective i
  fin_cases k <;> simp [point, project, heq]

theorem point_zero (c : Chart K) : point c 0 = 0 := by
  funext i
  obtain ⟨k, rfl⟩ := c.perm.surjective i
  fin_cases k <;> simp [point]

theorem project_nonzero_of_eval_zero (c : Chart K) (x : Fin 3 → K)
    (hx : MvPolynomial.eval x (polynomial c) = 0) (hne : x ≠ 0) :
    project c x 0 ≠ 0 ∨ project c x 1 ≠ 0 := by
  by_contra h
  push_neg at h
  have hp : project c x = 0 := by
    funext i
    fin_cases i <;> simp [h.1, h.2]
  have heq := point_project_of_eval_zero c x hx
  rw [hp, point_zero] at heq
  exact hne heq.symm

theorem point_smul (c : Chart K) (s : K) (v : Fin 2 → K) :
    point c (s • v) = s • point c v := by
  funext i
  obtain ⟨k, rfl⟩ := c.perm.surjective i
  fin_cases k <;> simp [point, mul_add, mul_left_comm]

theorem proportional_of_binary_det_zero (v w : Fin 2 → K)
    (hv : v 0 ≠ 0 ∨ v 1 ≠ 0) (hdet : v 0 * w 1 = w 0 * v 1) :
    ∃ s : K, w = s • v := by
  rcases hv with hv | hv
  · refine ⟨w 0 / v 0, ?_⟩
    funext i
    fin_cases i
    · simp [div_mul_cancel₀ _ hv]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hv).mpr
      change w 1 * v 0 = w 0 * v 1
      rw [mul_comm (w 1) (v 0)]
      exact hdet
  · refine ⟨w 1 / v 1, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hv).mpr
      change w 0 * v 1 = w 1 * v 0
      rw [mul_comm (w 1) (v 0)]
      exact hdet.symm
    · simp [div_mul_cancel₀ _ hv]

end EvenOrderMDS.ChartGeometry
