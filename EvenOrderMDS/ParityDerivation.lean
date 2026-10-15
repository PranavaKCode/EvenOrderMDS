module

public import EvenOrderMDS.KoszulParity
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.CharP.Reduced

@[expose] public noncomputable section

/-!
# Literal characteristic-two parity derivatives

Partial differentiation recovers each square coefficient. The Frobenius
derivation of the weight-one parity form is the square of its power syzygy.
-/

namespace EvenOrderMDS.ParityDerivation

open scoped BigOperators

variable {K ι : Type*} [Field K] [CharP K 2] [Fintype ι] [DecidableEq ι]

noncomputable def parityForm (B : ι → MvPolynomial ι K) : MvPolynomial ι K :=
  ∑ i, MvPolynomial.X i * B i ^ 2

omit [Fintype ι] [DecidableEq ι] in
theorem pderiv_square_zero (i : ι) (p : MvPolynomial ι K) :
    MvPolynomial.pderiv i (p ^ 2) = 0 := by
  simp [CharTwo.two_eq_zero]

theorem pderiv_parityForm (B : ι → MvPolynomial ι K) (i : ι) :
    MvPolynomial.pderiv i (parityForm B) = B i ^ 2 := by
  rw [parityForm, map_sum]
  simp only [MvPolynomial.pderiv_mul, pderiv_square_zero, mul_zero, add_zero,
    MvPolynomial.pderiv_X]
  simp [Pi.single_apply]

theorem parityForm_injective : Function.Injective (parityForm (K := K) (ι := ι)) := by
  intro B C h
  funext i
  have heq := congrArg (MvPolynomial.pderiv i) h
  rw [pderiv_parityForm, pderiv_parityForm] at heq
  exact frobenius_inj (MvPolynomial ι K) 2 heq

noncomputable def frobeniusDerivation (q : ℕ) :
    Derivation K (MvPolynomial ι K) (MvPolynomial ι K) :=
  MvPolynomial.mkDerivation K (fun i => MvPolynomial.X i ^ q)

omit [CharP K 2] [Fintype ι] [DecidableEq ι] in
theorem frobeniusDerivation_X (q : ℕ) (i : ι) :
    frobeniusDerivation (K := K) q (MvPolynomial.X i) = MvPolynomial.X i ^ q := by
  simp [frobeniusDerivation]

omit [Fintype ι] [DecidableEq ι] in
theorem frobeniusDerivation_square_zero (q : ℕ) (p : MvPolynomial ι K) :
    frobeniusDerivation (K := K) q (p ^ 2) = 0 := by
  rw [(frobeniusDerivation (K := K) q).leibniz_pow]
  simp [two_smul, CharTwo.add_self_eq_zero]

omit [DecidableEq ι] in
theorem frobeniusDerivation_parityForm (n : ℕ) (B : ι → MvPolynomial ι K) :
    frobeniusDerivation (K := K) (2 * n) (parityForm B) =
      (∑ i, MvPolynomial.X i ^ n * B i) ^ 2 := by
  rw [parityForm, map_sum, CharTwo.sum_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [(frobeniusDerivation (K := K) (2 * n)).leibniz,
    frobeniusDerivation_square_zero, frobeniusDerivation_X]
  simp [smul_eq_mul, mul_pow, ← pow_mul, mul_comm]

omit [DecidableEq ι] in
theorem parity_derivative_zero_iff_syzygy (n : ℕ) (B : ι → MvPolynomial ι K) :
    frobeniusDerivation (K := K) (2 * n) (parityForm B) = 0 ↔
      (∑ i, MvPolynomial.X i ^ n * B i) = 0 := by
  rw [frobeniusDerivation_parityForm]
  exact sq_eq_zero_iff

end EvenOrderMDS.ParityDerivation
