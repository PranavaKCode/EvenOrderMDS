module

public import EvenOrderMDS.LinearCoordinates
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

/-!
# Disjoint-support Frobenius coefficient syzygies

If every coefficient polynomial has all exponents below n, the summands
X_i^n B_i have disjoint supports. This is the literal polynomial fact used
after restricting a ternary relation to an old line.
-/

namespace EvenOrderMDS.BoundedSyzygy

open scoped BigOperators

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem coefficient_below_power (n : ℕ) (i : ι) (d : ι →₀ ℕ)
    (p : MvPolynomial ι K) (hd : d i < n) :
    (MvPolynomial.X i ^ n * p).coeff d = 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
  apply if_neg
  intro h
  have := h i
  simp only [Finsupp.single_eq_same] at this
  omega

theorem zero_of_bounded_power_syzygy (n : ℕ) (B : ι → MvPolynomial ι K)
    (hbox : ∀ i d, d ∈ (B i).support → ∀ k, d k < n)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0) :
    ∀ i, B i = 0 := by
  intro i
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ (B i).support
  · have h := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i n + d)) hrel
    rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero] at h
    rw [Finset.sum_eq_single i] at h
    · rw [MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.coeff_monomial_mul, one_mul] at h
      simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using h
    · intro k _ hki
      apply coefficient_below_power
      simpa [Finsupp.single_apply, Ne.symm hki] using hbox i d hd k
    · simp
  · simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      MvPolynomial.notMem_support_iff.mp hd

theorem zero_of_homogeneous_power_syzygy (n b : ℕ) (hb : b < n)
    (B : ι → MvPolynomial ι K) (hB : ∀ i, (B i).IsHomogeneous b)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0) :
    ∀ i, B i = 0 := by
  apply zero_of_bounded_power_syzygy n B _ hrel
  intro i d hd k
  have hdeg := hB i (MvPolynomial.mem_support_iff.mp hd)
  have hle := Finsupp.le_degree k d
  have hdegree : d.degree = b := by
    rw [Finsupp.degree_eq_weight_one]
    exact hdeg
  rw [hdegree] at hle
  exact lt_of_le_of_lt hle hb

end EvenOrderMDS.BoundedSyzygy
