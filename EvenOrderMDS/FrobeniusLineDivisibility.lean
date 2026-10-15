module

public import EvenOrderMDS.CompatiblePolynomial

@[expose] public noncomputable section

/-! Rational old lines are preserved by the Frobenius derivation. -/

namespace EvenOrderMDS.FrobeniusLineDivisibility

open LinearCoordinates ParityDerivation ActualLiftCompatibility CompatiblePolynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

theorem derivative_linearForm (e : ℕ) (hcard : Fintype.card K = 2 ^ e) (a : Fin 3 → K) :
    frobeniusDerivation (2 ^ e) (linearForm a) = linearForm a ^ (2 ^ e) := by
  rw [linearForm_apply, map_sum, sum_pow_char_pow 2 e _ _]
  simp only [(frobeniusDerivation (2 ^ e)).map_smul, frobeniusDerivation_X, smul_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hcard, FiniteField.pow_card]

theorem linearForm_dvd_derivative (e : ℕ) (hcard : Fintype.card K = 2 ^ e)
    (a : Fin 3 → K) (p : MvPolynomial (Fin 3) K) (hp : linearForm a ∣ p) :
    linearForm a ∣ frobeniusDerivation (2 ^ e) p := by
  obtain ⟨r, rfl⟩ := hp
  rw [(frobeniusDerivation (2 ^ e)).leibniz, derivative_linearForm e hcard,
    smul_eq_mul, smul_eq_mul]
  apply dvd_add (dvd_mul_right _ _)
  exact dvd_mul_of_dvd_right (dvd_pow_self _ (by positivity : 2 ^ e ≠ 0)) _

theorem derivative_complement_envelope {M : ℕ} (hM : 3 ≤ M)
    (e : ℕ) (hcard : Fintype.card K = 2 ^ e)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K)
    (hCF : frobeniusDerivation (2 ^ e) (PlaneArcColon.lineProduct a * F) = 0) (i : Fin M) :
    frobeniusDerivation (2 ^ e) (complement a i * F) =
      linearForm (a i) ^ (2 ^ e - 1) * (complement a i * F) := by
  rw [lineProduct_eq_single a i, mul_assoc, (frobeniusDerivation (2 ^ e)).leibniz,
    derivative_linearForm e hcard, smul_eq_mul, smul_eq_mul] at hCF
  have hpow : linearForm (a i) ^ (2 ^ e) = linearForm (a i) * linearForm (a i) ^ (2 ^ e - 1) := by
    rw [← pow_succ']
    congr 1
    have hp : 0 < 2 ^ e := by positivity
    omega
  rw [hpow] at hCF
  have heq : linearForm (a i) * (frobeniusDerivation (2 ^ e) (complement a i * F) +
      linearForm (a i) ^ (2 ^ e - 1) * (complement a i * F)) = 0 := by
    convert hCF using 1
    ring
  have hn : linearForm (a i) ≠ 0 := (PlaneCofactorGeometry.old_line_prime hM ha i).ne_zero
  have hz := (mul_eq_zero.mp heq).resolve_left hn
  exact (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq _)

omit [CharP K 2] [Fintype K] in
theorem polynomial_mod_old_line {M : ℕ} (a : Fin M → Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) (h : Fin M → K) (Q : MvPolynomial (Fin 3) K) (i : Fin M) :
    linearForm (a i) ∣ polynomial a F h Q - h i • (complement a i * F) := by
  classical
  have hrest : linearForm (a i) ∣ ∑ j ∈ Finset.univ.erase i, h j • complement a j := by
    apply Finset.dvd_sum
    intro j hj
    rw [MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right (old_line_dvd_complement a i j (Finset.ne_of_mem_erase hj).symm) _
  have heq : polynomial a F h Q - h i • (complement a i * F) =
      PlaneArcColon.lineProduct a * Q + (∑ j ∈ Finset.univ.erase i, h j • complement a j) * F := by
    rw [polynomial, heightTerm_eq_single]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  rw [heq]
  apply dvd_add _ (dvd_mul_of_dvd_left hrest _)
  rw [lineProduct_eq_single a i]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem old_line_dvd_derivative_polynomial {M : ℕ} (hM : 3 ≤ M)
    (e : ℕ) (hq : 2 ≤ 2 ^ e) (hcard : Fintype.card K = 2 ^ e)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K)
    (hCF : frobeniusDerivation (2 ^ e) (PlaneArcColon.lineProduct a * F) = 0)
    (h : Fin M → K) (Q : MvPolynomial (Fin 3) K) (i : Fin M) :
    linearForm (a i) ∣ frobeniusDerivation (2 ^ e) (polynomial a F h Q) := by
  have hd := linearForm_dvd_derivative e hcard (a i) _ (polynomial_mod_old_line a F h Q i)
  rw [map_sub, (frobeniusDerivation (2 ^ e)).map_smul, derivative_complement_envelope hM e hcard a ha F hCF i] at hd
  have hterm : linearForm (a i) ∣ h i • (linearForm (a i) ^ (2 ^ e - 1) * (complement a i * F)) := by
    rw [MvPolynomial.smul_eq_C_mul]
    apply dvd_mul_of_dvd_right
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  exact (dvd_sub_left hterm).mp hd

theorem oldProduct_dvd_obstruction {M : ℕ} (hM : 3 ≤ M)
    (e n : ℕ) (hexp : 2 ^ e = 2 * n) (hq : 2 ≤ 2 ^ e) (hcard : Fintype.card K = 2 ^ e)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K)
    (hCF : frobeniusDerivation (2 ^ e) (PlaneArcColon.lineProduct a * F) = 0)
    (h : Fin M → K) (Q : MvPolynomial (Fin 3) K) (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hparity : polynomial a F h Q = parityForm B) :
    PlaneArcColon.lineProduct a ∣ ∑ i, MvPolynomial.X i ^ n * B i := by
  apply PlaneCofactorGeometry.lineProduct_dvd_of_each hM ha
  intro i
  have hd := old_line_dvd_derivative_polynomial hM e hq hcard a ha F hCF h Q i
  rw [hparity, hexp, frobeniusDerivation_parityForm] at hd
  exact (PlaneCofactorGeometry.old_line_prime hM ha i).dvd_of_dvd_pow hd

end EvenOrderMDS.FrobeniusLineDivisibility
