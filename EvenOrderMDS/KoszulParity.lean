module

public import EvenOrderMDS.BoundarySyzygy
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public noncomputable section

/-!
# Boundary syzygies give the three literal characteristic-two parity forms

This is the polynomial kernel calculation used in the shear argument.
Identification with derivatives of a normalized envelope comes later.
-/

namespace EvenOrderMDS.KoszulParity

open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2]

noncomputable def pairForm (n : ℕ) (i j : Fin 3) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X i * (MvPolynomial.X j ^ n) ^ 2 +
    MvPolynomial.X j * (MvPolynomial.X i ^ n) ^ 2

omit [CharP K 2] in
theorem pairForm_eq (n : ℕ) (i j : Fin 3) :
    pairForm (K := K) n i j =
      MvPolynomial.X i ^ (2 * n) * MvPolynomial.X j +
        MvPolynomial.X i * MvPolynomial.X j ^ (2 * n) := by
  simp [pairForm, ← pow_mul, mul_comm, add_comm]

theorem parity_form_of_boundary_syzygy (n : ℕ) (hn : 0 < n)
    (B : Fin 3 → MvPolynomial (Fin 3) K)
    (hB : ∀ i, (B i).IsHomogeneous n)
    (hrel : ∑ i, MvPolynomial.X i ^ n * B i = 0) :
    ∃ a b c : K,
      (∑ i, MvPolynomial.X i * B i ^ 2) =
        a ^ 2 • pairForm n 0 1 + b ^ 2 • pairForm n 0 2 + c ^ 2 • pairForm n 1 2 := by
  obtain ⟨a, b, c, h0, h1, h2⟩ :=
    BoundarySyzygy.ternary_constant_koszul_form n hn B hB hrel
  refine ⟨a, b, c, ?_⟩
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [CharTwo.neg_eq, CharTwo.add_sq, smul_pow, pairForm, smul_add,
    mul_add, mul_smul_comm]
  ac_rfl

end EvenOrderMDS.KoszulParity
