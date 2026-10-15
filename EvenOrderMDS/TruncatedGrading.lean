module

public import EvenOrderMDS.PowerIdeal
public import EvenOrderMDS.GradedImage
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public noncomputable section

/-!
# Actual grading and exact top of the truncated ternary ring

The ring is K[X_0,X_1,X_2]/(X_0^n,X_1^n,X_2^n), as an actual algebra quotient.
The grading is constructed through the homogeneous kernel. The top degree is
3(n-1), with a specified nonzero monomial whenever n>0.
-/

namespace EvenOrderMDS.TruncatedGrading

open PowerIdeal
open scoped BigOperators

variable {K : Type*} [Field K]

def polynomialPieces (K : Type*) [Field K] : ℕ → Submodule K (PolynomialRing K) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) K

noncomputable instance polynomialGrading : GradedAlgebra (polynomialPieces K) :=
  MvPolynomial.gradedAlgebra

theorem powerIdeal_eq_span_variable_powers (n : ℕ) :
    powerIdeal (K := K) n = Ideal.span (Set.range (fun i : Fin 3 => (MvPolynomial.X i : PolynomialRing K) ^ n)) := by
  unfold powerIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨d, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, MvPolynomial.X_pow_eq_monomial⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Finsupp.single i n, ⟨i, rfl⟩, MvPolynomial.X_pow_eq_monomial.symm⟩

theorem powerIdeal_kernel_homogeneous (n : ℕ) :
    GradedImage.HomogeneousKernel (polynomialPieces K) (quotientMap (K := K) n) := by
  intro p hp j
  apply (quotientMap_eq_zero_iff n _).mpr
  intro d hd
  have hcoeff := (quotientMap_eq_zero_iff n p).mp hp d hd
  have hcomponent : (DirectSum.decompose (polynomialPieces K) p j : PolynomialRing K) =
      MvPolynomial.homogeneousComponent j p := MvPolynomial.decomposition.decompose'_apply p j
  rw [hcomponent]
  rw [MvPolynomial.coeff_homogeneousComponent]
  simp [hcoeff]

def pieces (n : ℕ) : ℕ → Submodule K (PolynomialRing K ⧸ powerIdeal (K := K) n) :=
  GradedImage.imagePieces (polynomialPieces K) (quotientMap (K := K) n)

noncomputable instance quotientGrading (n : ℕ) : GradedAlgebra (pieces (K := K) n) :=
  GradedImage.imageGrading (polynomialPieces K) (quotientMap (K := K) n)
    (quotientMap_surjective n) (powerIdeal_kernel_homogeneous n)

theorem box_degree_bound (n : ℕ) (d : Fin 3 →₀ ℕ) (hd : InBox n d) :
    d.degree ≤ 3 * (n - 1) := by
  rw [Finsupp.degree_eq_sum]
  calc
    (∑ i : Fin 3, d i) ≤ (∑ _i : Fin 3, (n - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hd i
      omega
    _ = 3 * (n - 1) := by simp [Nat.mul_comm]

theorem pieces_above_top (n j : ℕ) (hj : 3 * (n - 1) < j) :
    pieces (K := K) n j = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  obtain ⟨p, hp, rfl⟩ := hu
  apply (quotientMap_eq_zero_iff n p).mpr
  intro d hd
  apply Classical.byContradiction
  intro hcoeff
  have hhomogeneous : p.IsHomogeneous j := hp
  have hdegree : d.degree = j := by
    rw [Finsupp.degree_eq_weight_one]
    exact hhomogeneous hcoeff
  have hbound := box_degree_bound n d hd
  omega

noncomputable def topExponent (n : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ : Fin 3 => n - 1)

theorem topExponent_apply (n : ℕ) (i : Fin 3) : topExponent n i = n - 1 := by
  simp [topExponent]

theorem topExponent_degree (n : ℕ) : (topExponent n).degree = 3 * (n - 1) := by
  rw [Finsupp.degree_eq_sum]
  simp [topExponent_apply, Nat.mul_comm]

theorem topExponent_inBox {n : ℕ} (hn : 1 ≤ n) : InBox n (topExponent n) := by
  intro i
  rw [topExponent_apply]
  omega

theorem pieces_top_nonzero {n : ℕ} (hn : 1 ≤ n) :
    pieces (K := K) n (3 * (n - 1)) ≠ ⊥ := by
  apply (pieces (K := K) n (3 * (n - 1))).ne_bot_iff.mpr
  let p : PolynomialRing K := MvPolynomial.monomial (topExponent n) 1
  refine ⟨quotientMap (K := K) n p, ?_, ?_⟩
  · refine ⟨p, ?_, rfl⟩
    exact MvPolynomial.isHomogeneous_monomial 1 (topExponent_degree n)
  · exact box_monomial_nonzero n (topExponent n) (topExponent_inBox hn) one_ne_zero

end EvenOrderMDS.TruncatedGrading
