module

public import EvenOrderMDS.LinearCoordinates

@[expose] public noncomputable section

/-! Homogeneous evaluation at scaled literal vectors. -/

namespace EvenOrderMDS.HomogeneousEvaluation

open scoped BigOperators

variable {K ι : Type*} [Field K] [Fintype ι]

theorem eval_smul {p : MvPolynomial ι K} {j : ℕ} (hp : p.IsHomogeneous j)
    (s : K) (x : ι → K) :
    MvPolynomial.eval (s • x) p = s ^ j * MvPolynomial.eval x p := by
  classical
  rw [p.as_sum, MvPolynomial.eval_sum, MvPolynomial.eval_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree : (∑ i, d i) = j := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdegree]
  ac_rfl

theorem eval_smul_zero_iff {p : MvPolynomial ι K} {j : ℕ} (hp : p.IsHomogeneous j)
    {s : K} (hs : s ≠ 0) (x : ι → K) :
    MvPolynomial.eval (s • x) p = 0 ↔ MvPolynomial.eval x p = 0 := by
  rw [eval_smul hp, mul_eq_zero]
  exact or_iff_right (pow_ne_zero _ hs)

end EvenOrderMDS.HomogeneousEvaluation
