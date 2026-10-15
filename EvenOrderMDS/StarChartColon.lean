module

public import EvenOrderMDS.ChartFrobenius
public import EvenOrderMDS.LineVanishing
public import EvenOrderMDS.CriticalColon

@[expose] public noncomputable section

/-!
# No earlier annihilator from explicit star-chart geometry

The configuration contains actual line charts and their distinct nonzero
vertices, with each vertex also represented on a second distinct line.
This proves the geometric algebraic implication; construction of this data
from the retained arc predicate is a separate remaining adapter.
-/

namespace EvenOrderMDS.StarChartColon

open PlaneLineChart ChartFrobenius PowerIdeal
open scoped BigOperators

variable {K : Type*} [Field K]

structure Configuration (K : Type*) [Field K] (M : ℕ) where
  charts : Fin M → Chart K
  vertices : Fin M → Fin (M - 1) → Fin 2 → K
  nonzero : ∀ i t, vertices i t 0 ≠ 0 ∨ vertices i t 1 ≠ 0
  separated : ∀ i t u, t ≠ u →
    vertices i t 0 * vertices i u 1 ≠ vertices i u 0 * vertices i t 1
  distinct : ∀ i k, i ≠ k → ¬ polynomial (charts i) ∣ polynomial (charts k)
  intersection : ∀ i t, ∃ k, k ≠ i ∧ ∃ w : Fin 2 → K,
    point (charts i) (vertices i t) = point (charts k) w

noncomputable def lineProduct {M : ℕ} (S : Configuration K M) : PolynomialRing K :=
  ∏ i, polynomial (S.charts i)

theorem lineProduct_homogeneous {M : ℕ} (S : Configuration K M) :
    (lineProduct S).IsHomogeneous M := by
  simpa [lineProduct] using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => polynomial (S.charts i)) (fun _ => 1)
    (fun i _ => polynomial_homogeneous (S.charts i))

theorem lineProduct_ne_zero {M : ℕ} (S : Configuration K M) : lineProduct S ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => polynomial_ne_zero (S.charts i))

theorem restrict_lineProduct_zero {M : ℕ} (S : Configuration K M) (i : Fin M) :
    restrict (S.charts i) (lineProduct S) = 0 := by
  apply (restrict_zero_iff_divisible _ _).mpr
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem no_earlier_annihilator_of_star_charts [CharP K 2]
    (e d : ℕ) (hn : 2 ≤ 2 ^ e) (hd : d ≤ 2 ^ e - 2)
    (S : Configuration K (2 * 2 ^ e - d)) :
    CriticalColon.NoEarlierAnnihilator (2 ^ e) (lineProduct S) d := by
  intro j hj f hf hI
  let M := 2 * 2 ^ e - d
  have hnd : 2 ^ e ≤ M + j := by dsimp [M]; omega
  obtain ⟨B, hB, hdecomp⟩ :=
    PowerIdealDecomposition.homogeneous_powerIdeal_decomposition (2 ^ e) (M + j) hnd
      ((lineProduct_homogeneous S).mul hf) hI
  have hb : M + j - 2 ^ e < 2 ^ e := by dsimp [M]; omega
  have hbstar : M + j - 2 ^ e < M - 1 := by dsimp [M]; omega
  have hrel : ∀ i, restrict (S.charts i)
      (∑ k, MvPolynomial.X k ^ (2 ^ e) * B k) = 0 := by
    intro i
    rw [← hdecomp, map_mul, restrict_lineProduct_zero, zero_mul]
  have hcoeffzero : ∀ k, B k = 0 := by
    intro k
    apply LineVanishing.zero_of_star_chart_data M S.charts S.distinct S.vertices
      S.nonzero S.separated (hB k) hbstar
    intro i t
    obtain ⟨u, hui, w, heq⟩ := S.intersection i t
    have hleft := coefficient_values_on_line (S.charts i) e (M + j - 2 ^ e)
      hb B hB (hrel i) (S.vertices i t)
    have hright := coefficient_values_on_line (S.charts u) e (M + j - 2 ^ e)
      hb B hB (hrel u) w
    rw [← heq] at hright
    have hz := common_frobenius_multiple_zero (S.charts i) (S.charts u) e
      (S.distinct u i hui)
      (fun k => MvPolynomial.eval (point (S.charts i) (S.vertices i t)) (B k))
      _ _ hleft hright
    exact congrFun hz k
  have hmulzero : lineProduct S * f = 0 := by
    rw [hdecomp]
    simp [hcoeffzero]
  exact (mul_eq_zero.mp hmulzero).resolve_left (lineProduct_ne_zero S)

theorem critical_colon_bound_of_star_charts [CharP K 2]
    (e d : ℕ) (hn : 2 ≤ 2 ^ e) (hd : d ≤ 2 ^ e - 2)
    (S : Configuration K (2 * 2 ^ e - d)) :
    Module.finrank K (CriticalColon.component (2 ^ e) (lineProduct S) d) ≤ d + 1 :=
  CriticalColon.critical_colon_bound_of_no_earlier_annihilator hn hd (lineProduct S)
    (lineProduct_homogeneous S) (no_earlier_annihilator_of_star_charts e d hn hd S)

theorem critical_colon_endpoint_exact_of_star_charts [CharP K 2]
    (e d : ℕ) (hd : 2 ≤ d) (hend : d + 2 = 2 ^ e)
    (S : Configuration K (2 * 2 ^ e - d)) :
    Module.finrank K (CriticalColon.component (2 ^ e) (lineProduct S) d) = d + 1 :=
  CriticalColon.critical_colon_endpoint_exact_of_no_earlier_annihilator hd hend
    (lineProduct S) (lineProduct_homogeneous S)
    (no_earlier_annihilator_of_star_charts e d (by omega) (by omega) S)

end EvenOrderMDS.StarChartColon
