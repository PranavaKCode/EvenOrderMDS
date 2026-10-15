module

public import EvenOrderMDS.TruncatedColon
public import EvenOrderMDS.HomogeneousDimension
public import EvenOrderMDS.CriticalDimension
public import EvenOrderMDS.SmallDegree

@[expose] public noncomputable section

/-!
# The concrete critical colon bound from no earlier annihilator

J_j is the actual kernel of multiplication by C modulo the ternary power ideal,
restricted to literal degree-j homogeneous polynomials. The no-earlier condition
is explicit: its geometric proof remains a separate upstream obligation.

The d=0 branch uses only the one-dimensional constant polynomial space and
does not assume a nonzero Gorenstein quotient.
-/

namespace EvenOrderMDS.CriticalColon

open PowerIdeal TruncatedGrading TruncatedColon

variable {K : Type*} [Field K]

def component (n : ℕ) (C : PolynomialRing K) (j : ℕ) : Submodule K (polynomialPieces K j) :=
  ((colonIdeal n C).restrictScalars K).comap (polynomialPieces K j).subtype

def degreeMap (n : ℕ) (C : PolynomialRing K) (j : ℕ) : polynomialPieces K j →ₗ[K] ColonRing n C :=
  (colonMap n C).toLinearMap.comp (polynomialPieces K j).subtype

def NoEarlierAnnihilator (n : ℕ) (C : PolynomialRing K) (d : ℕ) : Prop :=
  ∀ j : ℕ, j < d → ∀ p : PolynomialRing K, p.IsHomogeneous j →
    C * p ∈ powerIdeal (K := K) n → p = 0

theorem degreeMap_kernel (n : ℕ) (C : PolynomialRing K) (j : ℕ) :
    LinearMap.ker (degreeMap n C j) = component n C j := by
  ext p
  exact colonMap_eq_zero_iff n C p

theorem degreeMap_range (n : ℕ) (C : PolynomialRing K) (j : ℕ) :
    LinearMap.range (degreeMap n C j) = colonPieces n C j := by
  rw [degreeMap, LinearMap.range_comp, Submodule.range_subtype,
    colonPieces_eq_polynomial_image]
  rfl

theorem component_rank_nullity (n : ℕ) (C : PolynomialRing K) (j : ℕ) :
    Module.finrank K (colonPieces n C j) + Module.finrank K (component n C j) =
      Nat.choose (j + 2) 2 := by
  have h := (degreeMap n C j).finrank_range_add_finrank_ker
  rw [degreeMap_range, degreeMap_kernel, HomogeneousDimension.polynomialPiece_finrank] at h
  exact h

theorem earlier_component_zero
    {n d : ℕ} {C : PolynomialRing K} (hearly : NoEarlierAnnihilator n C d)
    {j : ℕ} (hj : j < d) : component n C j = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  apply Subtype.ext
  exact hearly j hj p p.property hp

theorem earlier_hilbert_full
    {n d : ℕ} {C : PolynomialRing K} (hearly : NoEarlierAnnihilator n C d)
    {j : ℕ} (hj : j < d) :
    Module.finrank K (colonPieces n C j) = Nat.choose (j + 2) 2 := by
  have h := component_rank_nullity n C j
  rw [earlier_component_zero hearly hj, finrank_bot, add_zero] at h
  exact h

theorem no_earlier_implies_class_nonzero
    {n d : ℕ} {C : PolynomialRing K} (hd : 1 ≤ d)
    (hearly : NoEarlierAnnihilator n C d) : C ∉ powerIdeal (K := K) n := by
  intro hC
  have h := hearly 0 (by omega) 1 (MvPolynomial.isHomogeneous_one (Fin 3) K) (by simpa using hC)
  exact one_ne_zero h

theorem critical_colon_bound_of_no_earlier_annihilator
    {n d : ℕ} (hn : 2 ≤ n) (hdn : d ≤ n - 2)
    (C : PolynomialRing K) (hC : C.IsHomogeneous (2 * n - d))
    (hearly : NoEarlierAnnihilator n C d) :
    Module.finrank K (component n C d) ≤ d + 1 := by
  have hdimension := component_rank_nullity n C d
  by_cases hd0 : d = 0
  · subst d
    norm_num at hdimension ⊢
    omega
  have hd : 1 ≤ d := by omega
  have hnot := no_earlier_implies_class_nonzero hd hearly
  have halgebra := colon_hilbert_symmetric_unimodal (by omega : 1 ≤ n) hC hnot
  have hindex : 3 * (n - 1) - (2 * n - d) = n + d - 3 := by omega
  rw [hindex] at halgebra
  have hpositive : d = 1 → 1 ≤ Module.finrank K (colonPieces n C 1) := by
    intro hd1
    have htop := colon_top_nonzero (by omega : 1 ≤ n) hC hnot
    have hdegreepos : 0 < 3 * (n - 1) - (2 * n - d) := by omega
    have hone := StandardGeneration.degree_one_nonzero (colonPieces n C)
      (colon_standard_generated n C) hdegreepos htop
    exact Submodule.one_le_finrank_iff.mpr hone
  apply CriticalDimension.kernel_bound_of_hilbert_data hn hdn
    (fun j => Module.finrank K (colonPieces n C j))
  · exact (Nat.add_comm _ _).trans hdimension
  · intro j hj
    exact earlier_hilbert_full hearly hj
  · exact hpositive
  · exact halgebra.1
  · exact halgebra.2

theorem critical_colon_endpoint_exact_of_no_earlier_annihilator
    {n d : ℕ} (hd : 2 ≤ d) (hend : d + 2 = n)
    (C : PolynomialRing K) (hC : C.IsHomogeneous (2 * n - d))
    (hearly : NoEarlierAnnihilator n C d) :
    Module.finrank K (component n C d) = d + 1 := by
  have hnot := no_earlier_implies_class_nonzero (by omega : 1 ≤ d) hearly
  have halgebra := colon_hilbert_symmetric_unimodal (by omega : 1 ≤ n) hC hnot
  have hindex : 3 * (n - 1) - (2 * n - d) = n + d - 3 := by omega
  rw [hindex] at halgebra
  apply CriticalDimension.kernel_endpoint_exact_of_hilbert_data hd hend
    (fun j => Module.finrank K (colonPieces n C j))
  · exact (Nat.add_comm _ _).trans (component_rank_nullity n C d)
  · exact earlier_hilbert_full hearly (by omega)
  · exact halgebra.1

end EvenOrderMDS.CriticalColon
