module

public import EvenOrderMDS.BinaryGrowth
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public noncomputable section

/-!
# Binary homogeneous evaluation and its relation slices

For two elements x,y of an actual commutative K-algebra, a univariate
coefficient polynomial represents the degree-j homogeneous expression
sum_i coeff_i x^i y^(j-i). The relation slices are concrete polynomial kernels.
-/

namespace EvenOrderMDS.BinaryEvaluation

open Polynomial
open scoped BigOperators

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def evaluate (x y : R) (j : ℕ) : K[X] →ₗ[K] R :=
  ∑ i ∈ Finset.range (j + 1), (Polynomial.lcoeff K i).smulRight (x ^ i * y ^ (j - i))

theorem evaluate_apply (x y : R) (j : ℕ) (p : K[X]) :
    evaluate (K := K) x y j p =
      ∑ i ∈ Finset.range (j + 1), p.coeff i • (x ^ i * y ^ (j - i)) := by
  simp [evaluate]

theorem evaluate_next_inclusion (x y : R) (j : ℕ) (p : K[X])
    (hp : p ∈ Polynomial.degreeLT K (j + 1)) :
    evaluate (K := K) x y (j + 1) p = y * evaluate (K := K) x y j p := by
  have hcoeff : p.coeff (j + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (Polynomial.mem_degreeLT.mp hp)
  rw [evaluate_apply, Finset.sum_range_succ, hcoeff, zero_smul, add_zero,
    evaluate_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by
    have := Finset.mem_range.mp hi
    omega
  have hindex : j + 1 - i = (j - i) + 1 := by omega
  simp [hindex, pow_succ, mul_comm, mul_left_comm]

theorem evaluate_next_mul_X (x y : R) (j : ℕ) (p : K[X]) :
    evaluate (K := K) x y (j + 1) (X * p) = x * evaluate (K := K) x y j p := by
  rw [evaluate_apply, Finset.sum_range_succ']
  simp only [Polynomial.coeff_X_mul_zero, zero_smul, add_zero]
  rw [evaluate_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hindex : j + 1 - (i + 1) = j - i := by omega
  simp [hindex, pow_succ, mul_assoc, mul_comm]

def relationSlice (x y : R) (j : ℕ) : Submodule K K[X] :=
  Polynomial.degreeLT K (j + 1) ⊓ LinearMap.ker (evaluate (K := K) x y j)

theorem relationSlice_degree (x y : R) (j : ℕ) (p : K[X])
    (hp : p ∈ relationSlice (K := K) x y j) : p.natDegree ≤ j := by
  by_cases hp0 : p = 0
  · subst p
    simp
  · have hdeg : p.degree < j + 1 := Polynomial.mem_degreeLT.mp hp.1
    have hnat : p.natDegree < j + 1 := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hdeg
    omega

theorem relationSlice_inclusion (x y : R) (j : ℕ) :
    relationSlice (K := K) x y j ≤ relationSlice (K := K) x y (j + 1) := by
  intro p hp
  refine ⟨Polynomial.degreeLT_mono (by omega) hp.1, ?_⟩
  change evaluate (K := K) x y (j + 1) p = 0
  rw [evaluate_next_inclusion x y j p hp.1]
  rw [show evaluate (K := K) x y j p = 0 from hp.2, mul_zero]

theorem relationSlice_mul_X (x y : R) (j : ℕ) (p : K[X])
    (hp : p ∈ relationSlice (K := K) x y j) : X * p ∈ relationSlice (K := K) x y (j + 1) := by
  by_cases hp0 : p = 0
  · subst p
    simp
  refine ⟨?_, ?_⟩
  · apply Polynomial.mem_degreeLT.mpr
    have hnat := relationSlice_degree x y j p hp
    have hX : X * p ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hp0
    apply (Polynomial.natDegree_lt_iff_degree_lt hX).mp
    rw [Polynomial.natDegree_X_mul hp0]
    omega
  · change evaluate (K := K) x y (j + 1) (X * p) = 0
    rw [evaluate_next_mul_X]
    rw [show evaluate (K := K) x y j p = 0 from hp.2, mul_zero]

instance degreeLT_finite (j : ℕ) : FiniteDimensional K (Polynomial.degreeLT K (j + 1)) :=
  (Polynomial.degreeLTEquiv K (j + 1)).symm.finiteDimensional

instance relationSlice_finite (x y : R) (j : ℕ) : FiniteDimensional K (relationSlice (K := K) x y j) := by
  dsimp [relationSlice]
  exact Submodule.finiteDimensional_of_le inf_le_left

def boundedEvaluation (x y : R) (j : ℕ) : Polynomial.degreeLT K (j + 1) →ₗ[K] R :=
  (evaluate (K := K) x y j).comp (Polynomial.degreeLT K (j + 1)).subtype

noncomputable def hilbert (x y : R) (j : ℕ) : ℕ :=
  Module.finrank K (LinearMap.range (boundedEvaluation (K := K) x y j))

theorem relation_dimension_identity (x y : R) (j : ℕ) :
    hilbert (K := K) x y j + Module.finrank K (relationSlice (K := K) x y j) = j + 1 := by
  have hkernel :
      (LinearMap.ker (boundedEvaluation (K := K) x y j)).map (Polynomial.degreeLT K (j + 1)).subtype =
        relationSlice (K := K) x y j := by
    rw [boundedEvaluation, LinearMap.ker_comp, Submodule.map_comap_subtype]
    rfl
  have hkerdim : Module.finrank K (relationSlice (K := K) x y j) =
      Module.finrank K (LinearMap.ker (boundedEvaluation (K := K) x y j)) := by
    rw [← hkernel]
    exact Submodule.finrank_map_subtype_eq _ _
  have hdim := (boundedEvaluation (K := K) x y j).finrank_range_add_finrank_ker
  have hamb : Module.finrank K (Polynomial.degreeLT K (j + 1)) = j + 1 := by
    rw [(Polynomial.degreeLTEquiv K (j + 1)).finrank_eq]
    simp
  change Module.finrank K (LinearMap.range (boundedEvaluation (K := K) x y j)) + _ = _
  rw [hkerdim, hdim, hamb]

theorem binary_evaluation_no_rise (x y : R) :
    ∀ j : ℕ, hilbert (K := K) x y j < j + 1 →
      hilbert (K := K) x y (j + 1) ≤ hilbert (K := K) x y j := by
  exact BinaryGrowth.no_rise_of_polynomial_slices (relationSlice (K := K) x y)
    (relationSlice_degree x y) (relationSlice_inclusion x y) (relationSlice_mul_X x y)
    (hilbert (K := K) x y) (relation_dimension_identity x y)

theorem evaluate_X_pow (x y : R) {i j : ℕ} (hi : i ≤ j) :
    evaluate (K := K) x y j (X ^ i) = x ^ i * y ^ (j - i) := by
  simp [evaluate_apply, Polynomial.coeff_X_pow, show i < j + 1 by omega]

/-- The actual degree-j span generated by two algebra elements. -/
def binaryPiece (x y : R) (j : ℕ) : Submodule K R :=
  Submodule.span K (Set.range (fun i : Fin (j + 1) => x ^ (i : ℕ) * y ^ (j - (i : ℕ))))

theorem boundedEvaluation_range_eq_binaryPiece (x y : R) (j : ℕ) :
    LinearMap.range (boundedEvaluation (K := K) x y j) = binaryPiece (K := K) x y j := by
  apply le_antisymm
  · rintro z ⟨p, rfl⟩
    change evaluate (K := K) x y j (p : K[X]) ∈ binaryPiece (K := K) x y j
    rw [evaluate_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(⟨i, Finset.mem_range.mp hi⟩ : Fin (j + 1)), rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    have hpoly : (X ^ (i : ℕ) : K[X]) ∈ Polynomial.degreeLT K (j + 1) := by
      apply Polynomial.mem_degreeLT.mpr
      exact (Polynomial.degree_X_pow_le (i : ℕ)).trans_lt (WithBot.coe_lt_coe.mpr i.is_lt)
    refine ⟨⟨X ^ (i : ℕ), hpoly⟩, ?_⟩
    change evaluate (K := K) x y j (X ^ (i : ℕ)) = _
    exact evaluate_X_pow x y (by omega)

theorem hilbert_eq_binaryPiece_finrank (x y : R) (j : ℕ) :
    hilbert (K := K) x y j = Module.finrank K (binaryPiece (K := K) x y j) := by
  exact congrArg (fun V : Submodule K R => Module.finrank K V)
    (boundedEvaluation_range_eq_binaryPiece (K := K) x y j)

theorem binary_piece_dimension_bound (x y : R) (j : ℕ) :
    Module.finrank K (binaryPiece (K := K) x y j) ≤ j + 1 := by
  have h := relation_dimension_identity (K := K) x y j
  rw [hilbert_eq_binaryPiece_finrank] at h
  omega

/-- Binary no-rise for concrete monomial spans in any commutative K-algebra. -/
theorem binary_piece_no_rise (x y : R) {j : ℕ}
    (hj : Module.finrank K (binaryPiece (K := K) x y j) < j + 1) :
    Module.finrank K (binaryPiece (K := K) x y (j + 1)) ≤
      Module.finrank K (binaryPiece (K := K) x y j) := by
  have hj' : hilbert (K := K) x y j < j + 1 := by
    simpa only [hilbert_eq_binaryPiece_finrank] using hj
  have h := binary_evaluation_no_rise (K := K) x y j hj'
  simpa only [hilbert_eq_binaryPiece_finrank] using h

end EvenOrderMDS.BinaryEvaluation
