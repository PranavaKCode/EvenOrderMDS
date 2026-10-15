module

public import EvenOrderMDS.PlaneLineChart
public import Mathlib.Algebra.CharP.Reduced

@[expose] public noncomputable section

/-!
# Frobenius coefficient relations in every coordinate-permuted line chart

This transports the explicit binary substitution identity, including the
coefficient-vector permutation, rather than assuming coordinate covariance.
-/

namespace EvenOrderMDS.ChartFrobenius

open PlaneLineChart LineRestriction
open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem renamed_power_sum (c : Chart K) (n : ℕ)
    (B : Fin 3 → MvPolynomial (Fin 3) K) :
    MvPolynomial.rename c.perm.symm (∑ i, MvPolynomial.X i ^ n * B i) =
      ∑ i, MvPolynomial.X i ^ n * MvPolynomial.rename c.perm.symm (B (c.perm i)) := by
  have hs : (∑ i, MvPolynomial.X i ^ n * B i) =
      ∑ i, MvPolynomial.X (c.perm i) ^ n * B (c.perm i) :=
    (Equiv.sum_comp c.perm (fun i => MvPolynomial.X i ^ n * B i)).symm
  rw [hs, map_sum]
  simp only [map_mul, map_pow, MvPolynomial.rename_X, Equiv.symm_apply_apply]

theorem chart_coefficient_relations (c : Chart K) (e j : ℕ) (hj : j < 2 ^ e)
    (B : Fin 3 → MvPolynomial (Fin 3) K) (hB : ∀ i, (B i).IsHomogeneous j)
    (hrel : restrict c (∑ i, MvPolynomial.X i ^ (2 ^ e) * B i) = 0) :
    restrict c (B (c.perm 0)) = c.a ^ (2 ^ e) • restrict c (B (c.perm 2)) ∧
      restrict c (B (c.perm 1)) = c.b ^ (2 ^ e) • restrict c (B (c.perm 2)) := by
  change lineMap c.a c.b (MvPolynomial.rename c.perm.symm _) = 0 at hrel
  rw [renamed_power_sum] at hrel
  exact restricted_coefficient_relations c.a c.b e j hj
    (fun i => MvPolynomial.rename c.perm.symm (B (c.perm i)))
    (fun i => (hB (c.perm i)).rename_isHomogeneous) hrel

def normal (c : Chart K) : Fin 3 → K :=
  fun i => ![c.a, c.b, 1] (c.perm.symm i)

omit [CharP K 2] in
theorem normal_pivot (c : Chart K) : normal c (c.perm 2) = 1 := by
  simp [normal]

theorem polynomial_eq_linearForm_normal (c : Chart K) :
    polynomial c = LinearCoordinates.linearForm (normal c) := by
  rw [LinearCoordinates.linearForm_apply]
  have hs := Equiv.sum_comp c.perm
    (fun i => normal c i • (MvPolynomial.X i : MvPolynomial (Fin 3) K))
  rw [← hs]
  simp [normal, polynomial, NormalizedLine.equation, Fin.sum_univ_three,
    CharTwo.sub_eq_add, add_comm, add_left_comm, add_assoc]

theorem common_frobenius_multiple_zero (c d : Chart K) (e : ℕ)
    (hdistinct : ¬ polynomial d ∣ polynomial c)
    (v : Fin 3 → K) (r s : K)
    (hc : ∀ i, v i = normal c i ^ (2 ^ e) * r)
    (hd : ∀ i, v i = normal d i ^ (2 ^ e) * s) : v = 0 := by
  by_cases hr : r = 0
  · funext i
    simp [hc i, hr]
  · have hs : s = normal c (d.perm 2) ^ (2 ^ e) * r := by
      have h := (hd (d.perm 2)).symm.trans (hc (d.perm 2))
      simpa only [normal_pivot, one_pow, one_mul] using h
    have hnormal : normal c = normal c (d.perm 2) • normal d := by
      funext i
      have heq := (hc i).symm.trans (hd i)
      rw [hs, ← mul_assoc] at heq
      have hp := mul_right_cancel₀ hr heq
      rw [← mul_pow] at hp
      have h := iterateFrobenius_inj K 2 e hp
      simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using h
    have hpoly : polynomial c = normal c (d.perm 2) • polynomial d := by
      rw [polynomial_eq_linearForm_normal, polynomial_eq_linearForm_normal]
      calc
        _ = LinearCoordinates.linearForm (normal c (d.perm 2) • normal d) :=
          congrArg LinearCoordinates.linearForm hnormal
        _ = _ := map_smul _ _ _
    apply False.elim
    apply hdistinct
    rw [hpoly, MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_left _ _

theorem coefficient_values_on_line (c : Chart K) (e j : ℕ) (hj : j < 2 ^ e)
    (B : Fin 3 → MvPolynomial (Fin 3) K) (hB : ∀ i, (B i).IsHomogeneous j)
    (hrel : restrict c (∑ i, MvPolynomial.X i ^ (2 ^ e) * B i) = 0)
    (v : Fin 2 → K) :
    ∀ i, MvPolynomial.eval (point c v) (B i) =
      (normal c i) ^ (2 ^ e) * MvPolynomial.eval (point c v) (B (c.perm 2)) := by
  obtain ⟨h0, h1⟩ := chart_coefficient_relations c e j hj B hB hrel
  have hv0 := congrArg (MvPolynomial.eval v) h0
  have hv1 := congrArg (MvPolynomial.eval v) h1
  simp [eval_restrict] at hv0 hv1
  intro i
  obtain ⟨k, rfl⟩ := c.perm.surjective i
  fin_cases k
  · simpa [normal] using hv0
  · simpa [normal] using hv1
  · simp [normal]

end EvenOrderMDS.ChartFrobenius
