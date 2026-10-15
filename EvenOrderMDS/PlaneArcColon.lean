module

public import EvenOrderMDS.PlaneArcNormalization

@[expose] public noncomputable section

/-!
# The literal plane-arc line product has no earlier colon annihilator

The only geometric premise is the original literal-column plane arc predicate.
All star-chart data are constructed. Representative normalization records and
cancels a nonzero scalar rather than identifying distinct polynomials.
-/

namespace EvenOrderMDS.PlaneArcColon

open PlaneLineChart ChartFrobenius PowerIdeal
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def lineProduct {M : ℕ} (a : Fin M → Fin 3 → K) : PolynomialRing K :=
  ∏ i, LinearCoordinates.linearForm (a i)

theorem lineProduct_homogeneous {M : ℕ} (a : Fin M → Fin 3 → K) :
    (lineProduct a).IsHomogeneous M := by
  simpa [lineProduct] using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => LinearCoordinates.linearForm (a i)) (fun _ => 1)
    (fun i _ => LinearCoordinates.linearForm_homogeneous (a i))

theorem normalized_lineProduct [CharP K 2] {M : ℕ}
    (a : Fin M → Fin 3 → K) (c : Fin M → Chart K) (u : Fin M → K)
    (heq : ∀ i, a i = u i • normal (c i)) :
    lineProduct a = (∏ i, u i) • ∏ i, polynomial (c i) := by
  unfold lineProduct
  simp only [heq, map_smul, ← polynomial_eq_linearForm_normal,
    MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, ← map_prod]

theorem no_earlier_annihilator_of_plane_arc [CharP K 2]
    (e d : ℕ) (hn : 2 ≤ 2 ^ e) (hd : d ≤ 2 ^ e - 2)
    (a : Fin (2 * 2 ^ e - d) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    CriticalColon.NoEarlierAnnihilator (2 ^ e) (lineProduct a) d := by
  obtain ⟨c, u, hu, heq, hgeneral⟩ :=
    PlaneArcNormalization.exists_generalPosition_charts_of_arc (by omega) a ha
  obtain ⟨S, hS⟩ := CrossArrangement.exists_configuration (by omega) c hgeneral
  have hprod : lineProduct a = (∏ i, u i) • StarChartColon.lineProduct S := by
    rw [StarChartColon.lineProduct, hS]
    exact normalized_lineProduct a c u heq
  have hu' : (∏ i, u i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hu i)
  have hearly := StarChartColon.no_earlier_annihilator_of_star_charts e d hn hd S
  intro j hj f hf hI
  apply hearly j hj f hf
  rw [hprod, smul_mul_assoc] at hI
  exact (((powerIdeal (K := K) (2 ^ e)).restrictScalars K).smul_mem_iff hu').mp hI

theorem critical_colon_bound_of_plane_arc [CharP K 2]
    (e d : ℕ) (hn : 2 ≤ 2 ^ e) (hd : d ≤ 2 ^ e - 2)
    (a : Fin (2 * 2 ^ e - d) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    Module.finrank K (CriticalColon.component (2 ^ e) (lineProduct a) d) ≤ d + 1 :=
  CriticalColon.critical_colon_bound_of_no_earlier_annihilator hn hd (lineProduct a)
    (lineProduct_homogeneous a) (no_earlier_annihilator_of_plane_arc e d hn hd a ha)

theorem critical_colon_endpoint_exact_of_plane_arc [CharP K 2]
    (e d : ℕ) (hd : 2 ≤ d) (hend : d + 2 = 2 ^ e)
    (a : Fin (2 * 2 ^ e - d) → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    Module.finrank K (CriticalColon.component (2 ^ e) (lineProduct a) d) = d + 1 :=
  CriticalColon.critical_colon_endpoint_exact_of_no_earlier_annihilator hd hend
    (lineProduct a) (lineProduct_homogeneous a)
    (no_earlier_annihilator_of_plane_arc e d (by omega) (by omega) a ha)

end EvenOrderMDS.PlaneArcColon
