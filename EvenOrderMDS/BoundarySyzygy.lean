module

public import EvenOrderMDS.BoundedSyzygy

@[expose] public noncomputable section

/-!
# First boundary-degree power syzygies

At coefficient degree n, only pure n-th variable powers can occur in a
relation sum X_i^n B_i=0. The diagonal coefficient is zero.
-/

namespace EvenOrderMDS.BoundarySyzygy

open scoped BigOperators

variable {K : Type*} [Field K]

theorem coefficient_zero_of_unique_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (B : ι → MvPolynomial ι K)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0)
    (i : ι) (d : ι →₀ ℕ) (hd : ∀ k, k ≠ i → d k < n) :
    (B i).coeff d = 0 := by
  have h := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i n + d)) hrel
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single i] at h
  · rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul, one_mul] at h
    exact h
  · intro k _ hki
    apply BoundedSyzygy.coefficient_below_power
    simpa [Finsupp.single_apply, Ne.symm hki] using hd k hki
  · simp

theorem exponent_is_axis_of_large {n : ℕ} (d : Fin 3 →₀ ℕ)
    (hdegree : d.degree = n) (k : Fin 3) (hk : n ≤ d k) :
    d = Finsupp.single k n := by
  have hs : d 0 + d 1 + d 2 = n := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_three] using hdegree
  ext i
  fin_cases k <;> fin_cases i <;> simp_all <;> omega

theorem coefficient_zero_off_axes (n : ℕ) (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hB : ∀ i, (B i).IsHomogeneous n)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0)
    (i : Fin 3) (d : Fin 3 →₀ ℕ) (haxis : ∀ k, d ≠ Finsupp.single k n) :
    (B i).coeff d = 0 := by
  by_contra hcoeff
  have hdegree : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hB i hcoeff
  apply hcoeff
  apply coefficient_zero_of_unique_shift n B hrel i d
  intro k _
  by_contra hge
  exact haxis k (exponent_is_axis_of_large d hdegree k (Nat.le_of_not_gt hge))

theorem coefficient_zero_on_diagonal (n : ℕ) (hn : 0 < n)
    (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0) (i : Fin 3) :
    (B i).coeff (Finsupp.single i n) = 0 := by
  apply coefficient_zero_of_unique_shift n B hrel i (Finsupp.single i n)
  intro k hki
  simpa [Finsupp.single_apply, Ne.symm hki] using hn

theorem coefficient_polynomials_are_pure_powers (n : ℕ) (hn : 0 < n)
    (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hB : ∀ i, (B i).IsHomogeneous n)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0) (i : Fin 3) :
    B i = ∑ k, (B i).coeff (Finsupp.single k n) • MvPolynomial.X k ^ n := by
  apply MvPolynomial.ext
  intro d
  by_cases haxis : ∃ k, d = Finsupp.single k n
  · obtain ⟨k, rfl⟩ := haxis
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_X_pow, Finsupp.single_eq_single_iff, Nat.ne_of_gt hn,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  · have hnone : ∀ k, d ≠ Finsupp.single k n := by simpa using haxis
    rw [coefficient_zero_off_axes n B hB hrel i d hnone, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro k _
    simp [MvPolynomial.coeff_X_pow, Ne.symm (hnone k)]

theorem off_diagonal_coefficients_sum_zero (n : ℕ) (hn : 0 < n)
    (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0)
    (i j : Fin 3) (hij : i ≠ j) :
    (B i).coeff (Finsupp.single j n) +
      (B j).coeff (Finsupp.single i n) = 0 := by
  have hterm (k : Fin 3) :
      (MvPolynomial.X k ^ n * B k).coeff (Finsupp.single i n + Finsupp.single j n) =
      (if k = i then (B i).coeff (Finsupp.single j n) else 0) +
      (if k = j then (B j).coeff (Finsupp.single i n) else 0) := by
    by_cases hki : k = i
    · subst k
      simp only [ite_true, if_neg hij, add_zero, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.coeff_monomial_mul, one_mul]
    · by_cases hkj : k = j
      · subst k
        simp only [if_neg hki, ite_true, zero_add]
        rw [add_comm (Finsupp.single i n) (Finsupp.single j n),
          MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul, one_mul]
      · simp only [if_neg hki, if_neg hkj, add_zero]
        apply BoundedSyzygy.coefficient_below_power
        simpa [Finsupp.single_apply, Ne.symm hki, Ne.symm hkj] using hn
  have h := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i n + Finsupp.single j n)) hrel
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h
  simp only [hterm, Finset.sum_add_distrib] at h
  simpa using h

theorem ternary_constant_koszul_form (n : ℕ) (hn : 0 < n)
    (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hB : ∀ i, (B i).IsHomogeneous n)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0) :
    ∃ a b c : K,
      B 0 = a • MvPolynomial.X 1 ^ n + b • MvPolynomial.X 2 ^ n ∧
      B 1 = (-a) • MvPolynomial.X 0 ^ n + c • MvPolynomial.X 2 ^ n ∧
      B 2 = (-b) • MvPolynomial.X 0 ^ n + (-c) • MvPolynomial.X 1 ^ n := by
  let a := (B 0).coeff (Finsupp.single 1 n)
  let b := (B 0).coeff (Finsupp.single 2 n)
  let c := (B 1).coeff (Finsupp.single 2 n)
  have h01 := off_diagonal_coefficients_sum_zero n hn B hrel 1 0 (by decide)
  have h02 := off_diagonal_coefficients_sum_zero n hn B hrel 2 0 (by decide)
  have h12 := off_diagonal_coefficients_sum_zero n hn B hrel 2 1 (by decide)
  have hc01 := eq_neg_of_add_eq_zero_left h01
  have hc02 := eq_neg_of_add_eq_zero_left h02
  have hc12 := eq_neg_of_add_eq_zero_left h12
  refine ⟨a, b, c, ?_, ?_, ?_⟩
  · rw [coefficient_polynomials_are_pure_powers n hn B hB hrel 0, Fin.sum_univ_three,
      coefficient_zero_on_diagonal n hn B hrel 0, zero_smul, zero_add]
  · rw [coefficient_polynomials_are_pure_powers n hn B hB hrel 1, Fin.sum_univ_three,
      coefficient_zero_on_diagonal n hn B hrel 1, zero_smul, add_zero, hc01]
  · rw [coefficient_polynomials_are_pure_powers n hn B hB hrel 2, Fin.sum_univ_three,
      coefficient_zero_on_diagonal n hn B hrel 2, zero_smul, add_zero, hc02, hc12]

end EvenOrderMDS.BoundarySyzygy
