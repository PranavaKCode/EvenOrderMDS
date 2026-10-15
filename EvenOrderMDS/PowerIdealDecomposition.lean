module

public import EvenOrderMDS.TruncatedGrading
public import EvenOrderMDS.LinearColonSequence

@[expose] public noncomputable section

/-!
# Homogeneous coefficients in the actual ternary power ideal

Membership of a homogeneous polynomial in (X_0^n,X_1^n,X_2^n)
provides literal homogeneous coefficient polynomials of the exact degree.
-/

namespace EvenOrderMDS.PowerIdealDecomposition

open PowerIdeal TruncatedGrading
open scoped BigOperators

variable {K : Type*} [Field K]

theorem homogeneous_powerIdeal_decomposition (n d : ℕ) (hnd : n ≤ d)
    {p : PolynomialRing K} (hp : p.IsHomogeneous d)
    (hI : p ∈ powerIdeal (K := K) n) :
    ∃ B : Fin 3 → PolynomialRing K,
      (∀ i, (B i).IsHomogeneous (d - n)) ∧
        p = ∑ i, MvPolynomial.X i ^ n * B i := by
  rw [powerIdeal_eq_span_variable_powers] at hI
  obtain ⟨C, hC⟩ := Ideal.mem_span_range_iff_exists_fun.mp hI
  let B : Fin 3 → PolynomialRing K := fun i =>
    DirectSum.decompose (polynomialPieces K) (C i) (d - n)
  refine ⟨B, fun i => (DirectSum.decompose (polynomialPieces K) (C i) (d - n)).property, ?_⟩
  have hp' : (DirectSum.decompose (polynomialPieces K) p d : PolynomialRing K) = p :=
    DirectSum.decompose_of_mem_same (polynomialPieces K) hp
  have hcomp (r : PolynomialRing K) :
      (DirectSum.decompose (polynomialPieces K) r d : PolynomialRing K) =
        MvPolynomial.homogeneousComponent d r :=
    MvPolynomial.decomposition.decompose'_apply r d
  rw [← hp', ← hC, hcomp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hcomp, mul_comm, DirectSum.coe_decompose_mul_of_left_mem (polynomialPieces K) d
    (MvPolynomial.isHomogeneous_X_pow i n), if_pos hnd]

theorem homogeneous_zero_of_higher_degree_divisor
    {R : Type*} [CommRing R] [Algebra K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {m j : ℕ}
    (hjm : j < m) {c p : R} (hc : c ∈ A m) (hp : p ∈ A j)
    (hdiv : c ∣ p) : p = 0 := by
  obtain ⟨r, rfl⟩ := hdiv
  have h : (DirectSum.decompose A (c * r) j : R) = c * r :=
    DirectSum.decompose_of_mem_same A hp
  rw [DirectSum.coe_decompose_mul_of_left_mem A j hc, if_neg (by omega)] at h
  exact h.symm

end EvenOrderMDS.PowerIdealDecomposition
