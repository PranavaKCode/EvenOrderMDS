module

public import EvenOrderMDS.PlaneArcColon
public import EvenOrderMDS.HomogeneousEvaluation

@[expose] public noncomputable section

/-! The degree bound at actual plane-arc cofactor vectors. -/

namespace EvenOrderMDS.PlaneStarBound

open PlaneLineChart ChartGeometry ChartFrobenius CrossArrangement

variable {K : Type*} [Field K] [CharP K 2]

theorem zero_of_chart_cofactor_values {M : ℕ} (hM : 3 ≤ M)
    (c : Fin M → Chart K) (hgeneral : GeneralPosition c)
    {p : MvPolynomial (Fin 3) K} {j : ℕ} (hp : p.IsHomogeneous j)
    (hdegree : j < M - 1)
    (hzero : ∀ i k, i ≠ k → MvPolynomial.eval (vertex c i k) p = 0) : p = 0 := by
  cases M with
  | zero => omega
  | succ m =>
    let S := configuration m (by omega) c hgeneral
    apply LineVanishing.zero_of_star_chart_data (m + 1) S.charts S.distinct
      S.vertices S.nonzero S.separated hp hdegree
    intro i t
    change MvPolynomial.eval
      (point (c i) (project (c i) (vertex c i (i.succAbove t)))) p = 0
    rw [point_project_of_eval_zero _ _ (vertex_on_first c i _)]
    exact hzero i (i.succAbove t) (Fin.ne_succAbove i t)

theorem zero_of_plane_arc_cofactor_values {M : ℕ} (hM : 3 ≤ M)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    {p : MvPolynomial (Fin 3) K} {j : ℕ} (hp : p.IsHomogeneous j)
    (hdegree : j < M - 1)
    (hzero : ∀ i k, i ≠ k → MvPolynomial.eval (crossProduct (a i) (a k)) p = 0) :
    p = 0 := by
  obtain ⟨c, u, hu, heq, hgeneral⟩ :=
    PlaneArcNormalization.exists_generalPosition_charts_of_arc hM a ha
  apply zero_of_chart_cofactor_values hM c hgeneral hp hdegree
  intro i k hik
  have hscale : crossProduct (a i) (a k) = (u i * u k) • vertex c i k := by
    simp only [heq, map_smul, LinearMap.smul_apply, smul_smul, vertex]
    rw [mul_comm (u k) (u i)]
  have hz := hzero i k hik
  rw [hscale, HomogeneousEvaluation.eval_smul hp] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (mul_ne_zero (hu i) (hu k)))

end EvenOrderMDS.PlaneStarBound
