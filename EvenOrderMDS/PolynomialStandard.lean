module

public import EvenOrderMDS.TruncatedGrading
public import EvenOrderMDS.StandardGeneration
public import Mathlib.Tactic.FinCases

@[expose] public noncomputable section

/-!
# Standard generation and embedding dimension for the actual ternary grading

These statements connect the concrete polynomial quotient to the proved
graded-algebra unimodality theorem. They are literal polynomial identities.
-/

namespace EvenOrderMDS.PolynomialStandard

open PowerIdeal TruncatedGrading
open scoped BigOperators

variable {K : Type*} [Field K]

theorem monomial_mem_degree_one_power (d : Fin 3 →₀ ℕ) (a : K) :
    MvPolynomial.monomial d a ∈ (polynomialPieces K 1) ^ d.degree := by
  have hprod := SetLike.prod_pow_mem_graded
    (fun j : ℕ => (polynomialPieces K 1) ^ j)
    (fun _ : Fin 3 => 1)
    (fun i : Fin 3 => (MvPolynomial.X i : PolynomialRing K))
    (fun i : Fin 3 => d i)
    (F := Finset.univ)
    (fun i _ => by
      simpa only [polynomialPieces, pow_one, MvPolynomial.mem_homogeneousSubmodule] using
        MvPolynomial.isHomogeneous_X K i)
  have hmonic : MvPolynomial.monomial d (1 : K) ∈ (polynomialPieces K 1) ^ d.degree := by
    rw [MvPolynomial.monic_monomial_eq,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum]
    simpa using hprod
  simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using
    ((polynomialPieces K 1) ^ d.degree).smul_mem a hmonic

theorem degree_one_power_le_piece (j : ℕ) :
    (polynomialPieces K 1) ^ j ≤ polynomialPieces K j := by
  induction j with
  | zero =>
      rw [pow_zero]
      exact Submodule.one_le.mpr (SetLike.one_mem_graded (polynomialPieces K))
  | succ j ih =>
      rw [pow_succ]
      apply le_trans (mul_le_mul' ih le_rfl)
      exact Submodule.mul_le.mpr (fun _ hp _ hq => SetLike.mul_mem_graded hp hq)

theorem polynomial_standard_generated :
    StandardGeneration.StandardGenerated (polynomialPieces K) := by
  intro j
  apply le_antisymm ?_ (degree_one_power_le_piece j)
  intro p hp
  rw [MvPolynomial.as_sum p]
  apply Submodule.sum_mem
  intro d hd
  have hdegree : d.degree = j := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  have hmonomial := monomial_mem_degree_one_power d (p.coeff d)
  rw [hdegree] at hmonomial
  exact hmonomial

theorem degree_one_exponent_single (d : Fin 3 →₀ ℕ) (hd : d.degree = 1) :
    ∃ i : Fin 3, d = Finsupp.single i 1 := by
  have hsum : d 0 + (d 1 + d 2) = 1 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc] using hd
  have hcases :
      (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 1) := by omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    ext i
    fin_cases i <;> simp_all
  · refine ⟨1, ?_⟩
    ext i
    fin_cases i <;> simp_all
  · refine ⟨2, ?_⟩
    ext i
    fin_cases i <;> simp_all

theorem polynomial_piece_one_eq_span_variables :
    polynomialPieces K 1 =
      Submodule.span K (Set.range (fun i : Fin 3 => (MvPolynomial.X i : PolynomialRing K))) := by
  apply le_antisymm
  · intro p hp
    rw [MvPolynomial.as_sum p]
    apply Submodule.sum_mem
    intro d hd
    have hdegree : d.degree = 1 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hp (MvPolynomial.mem_support_iff.mp hd)
    obtain ⟨i, hi⟩ := degree_one_exponent_single d hdegree
    have hX : (MvPolynomial.X i : PolynomialRing K) ∈
        Submodule.span K (Set.range (fun i : Fin 3 => (MvPolynomial.X i : PolynomialRing K))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have hscaled := (Submodule.span K (Set.range
      (fun i : Fin 3 => (MvPolynomial.X i : PolynomialRing K)))).smul_mem (p.coeff d) hX
    simpa only [hi, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hscaled
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact MvPolynomial.isHomogeneous_X K i

theorem truncated_standard_generated (n : ℕ) :
    StandardGeneration.StandardGenerated (pieces (K := K) n) :=
  StandardGeneration.image_standard_generated (polynomialPieces K)
    polynomial_standard_generated (quotientMap (K := K) n)

theorem truncated_piece_one_eq_span_variables (n : ℕ) :
    pieces (K := K) n 1 = Submodule.span K
      (Set.range (fun i : Fin 3 => quotientMap (K := K) n (MvPolynomial.X i))) := by
  change (polynomialPieces K 1).map (quotientMap (K := K) n).toLinearMap = _
  rw [polynomial_piece_one_eq_span_variables, Submodule.map_span]
  rw [← Set.range_comp]
  rfl

theorem truncated_embedding_dimension_bound (n : ℕ) :
    Module.finrank K (pieces (K := K) n 1) ≤ 3 := by
  have heq := congrArg (fun V : Submodule K (PolynomialRing K ⧸ powerIdeal (K := K) n) =>
      Module.finrank K V) (truncated_piece_one_eq_span_variables (K := K) n)
  rw [heq]
  simpa [Set.finrank] using (finrank_range_le_card (R := K)
    (fun i : Fin 3 => quotientMap (K := K) n (MvPolynomial.X i)))

end EvenOrderMDS.PolynomialStandard
