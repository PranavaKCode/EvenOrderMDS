module

public import EvenOrderMDS.BoundedSyzygy
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public noncomputable section

/-!
# Literal restriction to a line and its Frobenius coefficient relation

The map substitutes Z = a X + b Y into a ternary polynomial. Its output
is a literal binary polynomial, not a function on the finite field.
-/

namespace EvenOrderMDS.LineRestriction

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def lineMap (a b : K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1,
    a • MvPolynomial.X 0 + b • MvPolynomial.X 1]

theorem lineMap_X_zero (a b : K) :
    lineMap a b (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [lineMap]

theorem lineMap_X_one (a b : K) :
    lineMap a b (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [lineMap]

theorem lineMap_X_two (a b : K) :
    lineMap a b (MvPolynomial.X 2) = a • MvPolynomial.X 0 + b • MvPolynomial.X 1 := by
  simp [lineMap]

theorem lineMap_equation (a b : K) :
    lineMap a b (MvPolynomial.X 2 - a • MvPolynomial.X 0 - b • MvPolynomial.X 1) = 0 := by
  simp only [map_sub, map_smul, lineMap_X_zero, lineMap_X_one, lineMap_X_two]
  abel

theorem lineMap_homogeneous (a b : K) {p : MvPolynomial (Fin 3) K} {j : ℕ}
    (hp : p.IsHomogeneous j) : (lineMap a b p).IsHomogeneous j := by
  have hg : ∀ i : Fin 3,
      (![MvPolynomial.X 0, MvPolynomial.X 1,
        a • MvPolynomial.X 0 + b • MvPolynomial.X 1] i : MvPolynomial (Fin 2) K).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact MvPolynomial.isHomogeneous_X K 0
    · exact MvPolynomial.isHomogeneous_X K 1
    · exact (MvPolynomial.homogeneousSubmodule (Fin 2) K 1).add_mem
        ((MvPolynomial.homogeneousSubmodule (Fin 2) K 1).smul_mem a (MvPolynomial.isHomogeneous_X K 0))
        ((MvPolynomial.homogeneousSubmodule (Fin 2) K 1).smul_mem b (MvPolynomial.isHomogeneous_X K 1))
  simpa only [lineMap, one_mul] using hp.aeval _ hg

theorem lineMap_of_divisible_equation (a b : K) {p : MvPolynomial (Fin 3) K}
    (hp : MvPolynomial.X 2 - a • MvPolynomial.X 0 - b • MvPolynomial.X 1 ∣ p) :
    lineMap a b p = 0 := by
  obtain ⟨r, rfl⟩ := hp
  rw [map_mul, lineMap_equation, zero_mul]

theorem lineMap_power_two [CharP K 2] (a b : K) (e : ℕ) :
    lineMap a b (MvPolynomial.X 2 ^ (2 ^ e)) =
      a ^ (2 ^ e) • MvPolynomial.X 0 ^ (2 ^ e) +
      b ^ (2 ^ e) • MvPolynomial.X 1 ^ (2 ^ e) := by
  rw [map_pow, lineMap_X_two, add_pow_char_pow]
  simp only [smul_pow]

theorem restricted_coefficient_relations [CharP K 2] (a b : K) (e j : ℕ)
    (hj : j < 2 ^ e) (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hB : ∀ i, (B i).IsHomogeneous j)
    (hrel : lineMap a b (∑ i, MvPolynomial.X i ^ (2 ^ e) * B i) = 0) :
    lineMap a b (B 0) = a ^ (2 ^ e) • lineMap a b (B 2) ∧
      lineMap a b (B 1) = b ^ (2 ^ e) • lineMap a b (B 2) := by
  let D : Fin 2 → MvPolynomial (Fin 2) K :=
    ![lineMap a b (B 0) + a ^ (2 ^ e) • lineMap a b (B 2),
      lineMap a b (B 1) + b ^ (2 ^ e) • lineMap a b (B 2)]
  have hD : ∀ i, (D i).IsHomogeneous j := by
    intro i
    fin_cases i <;>
      exact (MvPolynomial.homogeneousSubmodule (Fin 2) K j).add_mem
        (lineMap_homogeneous a b (hB _))
        ((MvPolynomial.homogeneousSubmodule (Fin 2) K j).smul_mem _
          (lineMap_homogeneous a b (hB 2)))
  have hDrel : ∑ i, MvPolynomial.X i ^ (2 ^ e) * D i = 0 := by
    rw [Fin.sum_univ_three, map_add, map_add, map_mul, map_mul, map_mul,
      lineMap_power_two, map_pow, map_pow, lineMap_X_zero, lineMap_X_one] at hrel
    rw [Fin.sum_univ_two]
    change MvPolynomial.X 0 ^ (2 ^ e) *
        (lineMap a b (B 0) + a ^ (2 ^ e) • lineMap a b (B 2)) +
      MvPolynomial.X 1 ^ (2 ^ e) *
        (lineMap a b (B 1) + b ^ (2 ^ e) • lineMap a b (B 2)) = 0
    convert hrel using 1
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    ac_rfl
  have hz := BoundedSyzygy.zero_of_homogeneous_power_syzygy (2 ^ e) j hj D hD hDrel
  constructor
  · have h := eq_neg_of_add_eq_zero_left (hz 0)
    simpa only [D, Matrix.cons_val_zero, CharTwo.neg_eq] using h
  · have h := eq_neg_of_add_eq_zero_left (hz 1)
    simpa only [D, Matrix.cons_val_one, Matrix.head_cons, CharTwo.neg_eq] using h

end EvenOrderMDS.LineRestriction
