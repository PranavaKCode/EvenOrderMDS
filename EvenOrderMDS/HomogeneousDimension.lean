module

public import EvenOrderMDS.TruncatedGrading
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public noncomputable section

/-!
# Exact dimensions of ternary homogeneous polynomial pieces

The monomial index set is identified with the symmetric power of three labels.
Stars and bars is used through its proved finite-cardinality theorem.
-/

namespace EvenOrderMDS.HomogeneousDimension

open PowerIdeal TruncatedGrading

variable {K : Type*} [Field K]

abbrev DegreeExponent (j : ℕ) := {d : Fin 3 →₀ ℕ // d.degree = j}

def degreeExponentEquivSym (j : ℕ) : DegreeExponent j ≃ Sym (Fin 3) j :=
  (Sym.equivNatSum (Fin 3) j).symm

noncomputable instance degreeExponent_fintype (j : ℕ) : Fintype (DegreeExponent j) :=
  Fintype.ofEquiv (Sym (Fin 3) j) (degreeExponentEquivSym j).symm

theorem degreeExponent_card (j : ℕ) : Fintype.card (DegreeExponent j) = Nat.choose (j + 2) 2 := by
  rw [Fintype.card_congr (degreeExponentEquivSym j), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  rw [show 3 + j - 1 = j + 2 by omega]
  have hsym := Nat.choose_symm (show j ≤ j + 2 by omega)
  rw [show j + 2 - j = 2 by omega] at hsym
  exact hsym.symm

noncomputable def homogeneousEquivFinsupp (j : ℕ) :
    polynomialPieces K j ≃ₗ[K] (DegreeExponent j →₀ K) :=
  (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) K j)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) {d : Fin 3 →₀ ℕ | d.degree = j})

instance polynomialPiece_finiteDimensional (j : ℕ) : FiniteDimensional K (polynomialPieces K j) :=
  (homogeneousEquivFinsupp (K := K) j).symm.finiteDimensional

theorem polynomialPiece_finrank (j : ℕ) :
    Module.finrank K (polynomialPieces K j) = Nat.choose (j + 2) 2 := by
  rw [(homogeneousEquivFinsupp (K := K) j).finrank_eq, Module.finrank_finsupp_self,
    degreeExponent_card]

end EvenOrderMDS.HomogeneousDimension
