module

public import EvenOrderMDS.PlaneLineChart
public import EvenOrderMDS.BinaryRootBound
public import EvenOrderMDS.PowerIdealDecomposition
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public noncomputable section

/-!
# From many roots on distinct lines to a zero polynomial

The line charts, pairwise nondividing factors, and projectively distinct
sample points are explicit. Applying this to star vertices still requires
the arrangement-to-chart adapter.
-/

namespace EvenOrderMDS.LineVanishing

open PlaneLineChart
open scoped BigOperators

variable {K ι κ : Type*} [Field K] [Fintype ι]

theorem zero_of_restrictions_on_distinct_lines (c : ι → Chart K)
    (hdistinct : ∀ i k, i ≠ k → ¬ polynomial (c i) ∣ polynomial (c k))
    {p : MvPolynomial (Fin 3) K} {j : ℕ} (hp : p.IsHomogeneous j)
    (hdegree : j < Fintype.card ι) (hzero : ∀ i, restrict (c i) p = 0) : p = 0 := by
  classical
  have hdvd (s : Finset ι) : (∏ i ∈ s, polynomial (c i)) ∣ p := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      obtain ⟨r, hr⟩ := ih
      have hpi := (restrict_zero_iff_divisible (c i) p).mp (hzero i)
      rw [hr] at hpi
      have hnot : ¬ polynomial (c i) ∣ ∏ k ∈ s, polynomial (c k) := by
        intro h
        obtain ⟨k, hk, hdiv⟩ := (polynomial_prime (c i)).dvd_finset_prod_iff _ |>.mp h
        exact hdistinct i k (by intro heq; subst k; exact hi hk) hdiv
      obtain ⟨t, ht⟩ := ((polynomial_prime (c i)).dvd_or_dvd hpi).resolve_left hnot
      refine ⟨t, ?_⟩
      rw [hr, ht]
      ac_rfl
  have hdiv : (∏ i, polynomial (c i)) ∣ p := hdvd Finset.univ
  have hprod : (∏ i, polynomial (c i)).IsHomogeneous (Fintype.card ι) := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i => polynomial (c i)) (fun _ => 1) (fun i _ => polynomial_homogeneous (c i))
  exact PowerIdealDecomposition.homogeneous_zero_of_higher_degree_divisor
    (TruncatedGrading.polynomialPieces K) hdegree hprod hp hdiv

theorem zero_of_many_points_on_distinct_lines [Fintype κ] (c : ι → Chart K)
    (hdistinct : ∀ i k, i ≠ k → ¬ polynomial (c i) ∣ polynomial (c k))
    (v : ι → κ → Fin 2 → K)
    (hne : ∀ i t, v i t 0 ≠ 0 ∨ v i t 1 ≠ 0)
    (hsep : ∀ i t u, t ≠ u → v i t 0 * v i u 1 ≠ v i u 0 * v i t 1)
    {p : MvPolynomial (Fin 3) K} {j : ℕ} (hp : p.IsHomogeneous j)
    (hdegree_lines : j < Fintype.card ι) (hdegree_points : j < Fintype.card κ)
    (hzero : ∀ i t, MvPolynomial.eval (point (c i) (v i t)) p = 0) : p = 0 := by
  apply zero_of_restrictions_on_distinct_lines c hdistinct hp hdegree_lines
  intro i
  apply BinaryRootBound.zero_of_projective_roots (restrict_homogeneous (c i) hp)
    (v i) (hne i) (hsep i) _ hdegree_points
  intro t
  rw [eval_restrict]
  exact hzero i t

theorem zero_of_star_chart_data (M : ℕ) (c : Fin M → Chart K)
    (hdistinct : ∀ i k, i ≠ k → ¬ polynomial (c i) ∣ polynomial (c k))
    (v : Fin M → Fin (M - 1) → Fin 2 → K)
    (hne : ∀ i t, v i t 0 ≠ 0 ∨ v i t 1 ≠ 0)
    (hsep : ∀ i t u, t ≠ u → v i t 0 * v i u 1 ≠ v i u 0 * v i t 1)
    {p : MvPolynomial (Fin 3) K} {j : ℕ} (hp : p.IsHomogeneous j)
    (hdegree : j < M - 1)
    (hzero : ∀ i t, MvPolynomial.eval (point (c i) (v i t)) p = 0) : p = 0 := by
  apply zero_of_many_points_on_distinct_lines c hdistinct v hne hsep hp
    (by simpa using (show j < M by omega)) (by simpa using hdegree) hzero

end EvenOrderMDS.LineVanishing
