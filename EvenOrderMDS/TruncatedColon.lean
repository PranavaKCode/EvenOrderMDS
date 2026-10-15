module

public import EvenOrderMDS.TruncatedSocle
public import EvenOrderMDS.PolynomialStandard
public import EvenOrderMDS.GorensteinUnimodality
public import EvenOrderMDS.ColonQuotient

@[expose] public noncomputable section

/-!
# Concrete homogeneous colon quotients of the truncated ternary algebra

The actual algebra is formed by first quotienting by (X_0^n,X_1^n,X_2^n),
then by the annihilator of the class of C. The composite quotient map has
exactly the polynomial colon ideal as kernel. Its grading, exact shifted top,
socle, standard generation, and Hilbert unimodality are proved here.

C is required to be homogeneous and not in the power ideal. The geometric
no-earlier-annihilator theorem that supplies this premise in the manuscript
is still a separate unproved target.
-/

namespace EvenOrderMDS.TruncatedColon

open PowerIdeal TruncatedGrading

variable {K : Type*} [Field K]

abbrev BaseRing (K : Type*) [Field K] (n : ℕ) := PolynomialRing K ⧸ powerIdeal (K := K) n

abbrev ColonRing (n : ℕ) (C : PolynomialRing K) :=
  BaseRing K n ⧸ ColonQuotient.annihilatorIdeal (quotientMap (K := K) n C)

def colonMap (n : ℕ) (C : PolynomialRing K) : PolynomialRing K →ₐ[K] ColonRing n C :=
  (ColonQuotient.quotientMap (K := K) (quotientMap (K := K) n C)).comp (quotientMap (K := K) n)

def colonIdeal (n : ℕ) (C : PolynomialRing K) : Ideal (PolynomialRing K) where
  carrier := {p | C * p ∈ powerIdeal (K := K) n}
  zero_mem' := by simp
  add_mem' := by
    intro p r hp hr
    change C * (p + r) ∈ powerIdeal (K := K) n
    rw [mul_add]
    exact (powerIdeal (K := K) n).add_mem hp hr
  smul_mem' := by
    intro a p hp
    change C * (a * p) ∈ powerIdeal (K := K) n
    rw [mul_left_comm]
    exact (powerIdeal (K := K) n).mul_mem_left a hp

def colonPieces (n : ℕ) (C : PolynomialRing K) : ℕ → Submodule K (ColonRing n C) :=
  GradedImage.imagePieces (pieces (K := K) n)
    (ColonQuotient.quotientMap (K := K) (quotientMap (K := K) n C))

theorem colonMap_eq_zero_iff (n : ℕ) (C p : PolynomialRing K) :
    colonMap n C p = 0 ↔ C * p ∈ powerIdeal (K := K) n := by
  change ColonQuotient.quotientMap (K := K) (quotientMap (K := K) n C)
    (quotientMap (K := K) n p) = 0 ↔ _
  rw [ColonQuotient.quotientMap_eq_zero_iff, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem colonMap_kernel (n : ℕ) (C : PolynomialRing K) :
    RingHom.ker (colonMap n C).toRingHom = colonIdeal n C := by
  ext p
  exact colonMap_eq_zero_iff n C p

theorem colonMap_surjective (n : ℕ) (C : PolynomialRing K) : Function.Surjective (colonMap n C) :=
  (ColonQuotient.quotientMap_surjective (K := K) (quotientMap (K := K) n C)).comp
    (quotientMap_surjective (K := K) n)

theorem colonPieces_eq_polynomial_image (n : ℕ) (C : PolynomialRing K) :
    colonPieces n C = GradedImage.imagePieces (polynomialPieces K) (colonMap n C) := by
  funext j
  unfold colonPieces pieces GradedImage.imagePieces
  rw [← Submodule.map_comp]
  rfl

theorem class_nonzero (n : ℕ) (C : PolynomialRing K) (hC : C ∉ powerIdeal (K := K) n) :
    quotientMap (K := K) n C ≠ 0 := by
  intro hzero
  exact hC (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

theorem class_mem_piece (n : ℕ) {C : PolynomialRing K} {m : ℕ} (hC : C.IsHomogeneous m) :
    quotientMap (K := K) n C ∈ pieces (K := K) n m :=
  ⟨C, hC, rfl⟩

theorem degree_le_top_of_nonzero_class
    (n : ℕ) {C : PolynomialRing K} {m : ℕ} (hC : C.IsHomogeneous m)
    (hnot : C ∉ powerIdeal (K := K) n) : m ≤ 3 * (n - 1) := by
  apply Nat.le_of_not_gt
  intro hlarge
  have hmem := class_mem_piece n hC
  rw [pieces_above_top n m hlarge] at hmem
  exact class_nonzero n C hnot hmem

noncomputable def colonGrading
    (n : ℕ) {C : PolynomialRing K} {m : ℕ} (hC : C.IsHomogeneous m) :
    GradedAlgebra (colonPieces n C) :=
  ColonQuotient.quotientGrading (pieces (K := K) n) (class_mem_piece n hC)

instance colon_finiteDimensional (n : ℕ) (C : PolynomialRing K) : FiniteDimensional K (ColonRing n C) :=
  FiniteDimensional.of_injective
    (ColonQuotient.quotientMul (K := K) (quotientMap (K := K) n C))
    (ColonQuotient.quotientMul_injective (K := K) (quotientMap (K := K) n C))

theorem colon_standard_generated (n : ℕ) (C : PolynomialRing K) :
    StandardGeneration.StandardGenerated (colonPieces n C) :=
  StandardGeneration.image_standard_generated (pieces (K := K) n)
    (PolynomialStandard.truncated_standard_generated n) _

theorem colon_embedding_dimension_bound (n : ℕ) (C : PolynomialRing K) :
    Module.finrank K (colonPieces n C 1) ≤ 3 :=
  (ColonQuotient.quotient_piece_finrank_le (pieces (K := K) n)
    (quotientMap (K := K) n C) 1).trans (PolynomialStandard.truncated_embedding_dimension_bound n)

theorem colon_above_top
    (n : ℕ) {C : PolynomialRing K} {m : ℕ} (hC : C.IsHomogeneous m)
    (hnot : C ∉ powerIdeal (K := K) n) {j : ℕ} (hj : 3 * (n - 1) - m < j) :
    colonPieces n C j = ⊥ :=
  ColonQuotient.quotient_piece_above_top (pieces (K := K) n)
    (fun j hj => pieces_above_top n j hj) (degree_le_top_of_nonzero_class n hC hnot)
    (class_mem_piece n hC) hj

theorem colon_top_nonzero
    {n : ℕ} (hn : 1 ≤ n) {C : PolynomialRing K} {m : ℕ} (hC : C.IsHomogeneous m)
    (hnot : C ∉ powerIdeal (K := K) n) : colonPieces n C (3 * (n - 1) - m) ≠ ⊥ :=
  ColonQuotient.quotient_top_nonzero (pieces (K := K) n)
    (fun j hj => pieces_above_top n j hj) (pieces_top_nonzero hn)
    (TruncatedSocle.positiveSocle_dimension hn) (class_mem_piece n hC) (class_nonzero n C hnot)

theorem colon_socle_dimension
    {n : ℕ} (hn : 1 ≤ n) {C : PolynomialRing K} {m : ℕ} (hC : C.IsHomogeneous m)
    (hnot : C ∉ powerIdeal (K := K) n) :
    Module.finrank K (GradedSocle.positiveSocle (colonPieces n C)) = 1 :=
  ColonQuotient.quotient_socle_dimension (pieces (K := K) n)
    (fun j hj => pieces_above_top n j hj) (pieces_top_nonzero hn)
    (TruncatedSocle.positiveSocle_dimension hn) (degree_le_top_of_nonzero_class n hC hnot)
    (class_mem_piece n hC) (class_nonzero n C hnot)

theorem colon_hilbert_symmetric_unimodal
    {n : ℕ} (hn : 1 ≤ n) {C : PolynomialRing K} {m : ℕ} (hC : C.IsHomogeneous m)
    (hnot : C ∉ powerIdeal (K := K) n) :
    HilbertSequence.Symmetric (3 * (n - 1) - m) (fun j => Module.finrank K (colonPieces n C j)) ∧
      HilbertSequence.FirstHalfMonotone (3 * (n - 1) - m)
        (fun j => Module.finrank K (colonPieces n C j)) := by
  letI : GradedAlgebra (colonPieces n C) := colonGrading n hC
  exact GorensteinUnimodality.symmetric_unimodal_of_embedding_dimension_le_three
    (colonPieces n C) (colon_standard_generated n C)
    (fun j hj => colon_above_top n hC hnot hj) (colon_top_nonzero hn hC hnot)
    (colon_socle_dimension hn hC hnot) (colon_embedding_dimension_bound n C)

end EvenOrderMDS.TruncatedColon
