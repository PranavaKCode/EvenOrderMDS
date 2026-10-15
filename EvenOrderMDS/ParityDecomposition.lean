module

public import EvenOrderMDS.SquareRootCoefficients
public import EvenOrderMDS.ExponentParity

@[expose] public noncomputable section

/-!
# Literal squarefree-parity decomposition over finite fields of characteristic two

Every component is constructed by filtering actual coefficient exponents and
applying the inverse Frobenius to coefficients. No polynomial-function quotient
is used. The degree of each square-root component is also proved.
-/

namespace EvenOrderMDS.ParityDecomposition

open ExponentParity SquareRootCoefficients
open scoped BigOperators

variable {K ι : Type*} [Field K] [CharP K 2] [Finite K] [Fintype ι]

noncomputable def rootComponent (b : ι → Fin 2) (p : MvPolynomial ι K) : MvPolynomial ι K :=
  ∑ d ∈ p.support.filter (fun d => bits d = b),
    MvPolynomial.monomial (half d) (squareRoot K (p.coeff d))

noncomputable def parityComponent (b : ι → Fin 2) (p : MvPolynomial ι K) : MvPolynomial ι K :=
  MvPolynomial.monomial (bitExponent b) 1 * rootComponent b p ^ 2

theorem rootComponent_square (b : ι → Fin 2) (p : MvPolynomial ι K) :
    rootComponent b p ^ 2 = ∑ d ∈ p.support.filter (fun d => bits d = b),
      MvPolynomial.monomial (2 • half d) (p.coeff d) := by
  rw [rootComponent, CharTwo.sum_sq]
  simp only [MvPolynomial.monomial_pow, squareRoot_sq]

theorem parityComponent_eq_filter_sum (b : ι → Fin 2) (p : MvPolynomial ι K) :
    parityComponent b p = ∑ d ∈ p.support.filter (fun d => bits d = b),
      MvPolynomial.monomial d (p.coeff d) := by
  classical
  rw [parityComponent, rootComponent_square, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hb := (Finset.mem_filter.mp hd).2
  rw [MvPolynomial.monomial_mul, one_mul, ← hb, bitExponent_bits, exponent_decomposition]

theorem sum_parityComponents [DecidableEq ι] (p : MvPolynomial ι K) :
    (∑ b : ι → Fin 2, parityComponent b p) = p := by
  classical
  simp only [parityComponent_eq_filter_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem rootComponent_homogeneous {p : MvPolynomial ι K} {j : ℕ}
    (hp : p.IsHomogeneous j) (b : ι → Fin 2) :
    (rootComponent b p).IsHomogeneous ((j - (bitExponent b).degree) / 2) := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  have hmem := (Finset.mem_filter.mp hd).1
  have hbits := (Finset.mem_filter.mp hd).2
  have hdegree : d.degree = j := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hmem)
  apply MvPolynomial.isHomogeneous_monomial
  exact half_degree_of_parity hdegree hbits

theorem rootComponent_eq_zero_of_wrong_parity {p : MvPolynomial ι K} {j : ℕ}
    (hp : p.IsHomogeneous j) (b : ι → Fin 2)
    (hparity : j % 2 ≠ (bitExponent b).degree % 2) : rootComponent b p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d hd
  have hmem := (Finset.mem_filter.mp hd).1
  have hbits := (Finset.mem_filter.mp hd).2
  have hdegree : d.degree = j := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hmem)
  have h := degree_decomposition d
  rw [hdegree, ← bitExponent_bits, hbits] at h
  exfalso
  apply hparity
  omega

end EvenOrderMDS.ParityDecomposition
