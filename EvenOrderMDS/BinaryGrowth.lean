module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import EvenOrderMDS.HilbertSequence

@[expose] public noncomputable section

/-!
# Polynomial-subspace growth for the binary no-rise argument

Dehomogenizing degree-j binary forms identifies them with univariate
polynomials of degree at most j. Multiplication by the two original variables
becomes inclusion and multiplication by X. A bounded nonzero subspace cannot
be closed under multiplication by X, giving the required strict growth.

This module proves that actual polynomial-subspace statement. A homogeneous
binary-ideal/dehomogenization adapter remains separate.
-/

namespace EvenOrderMDS.BinaryGrowth

open Polynomial

variable {K : Type*} [Field K]

/-- A bounded nonzero polynomial subspace has an element whose X-multiple escapes. -/
theorem exists_mul_X_not_mem
    (V : Submodule K K[X]) (hV : V ≠ ⊥) {d : ℕ}
    (hdegree : ∀ p : K[X], p ∈ V → p.natDegree ≤ d) :
    ∃ p : K[X], p ∈ V ∧ X * p ∉ V := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hstable : ∀ p : K[X], p ∈ V → X * p ∈ V := by
    intro p hp
    apply Classical.byContradiction
    intro hnot
    exact hnone ⟨p, hp, hnot⟩
  obtain ⟨p, hpV, hp0⟩ := V.ne_bot_iff.mp hV
  have hpowers : ∀ n : ℕ, X ^ n * p ∈ V := by
    intro n
    induction n with
    | zero => simpa using hpV
    | succ n ih =>
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
          hstable (X ^ n * p) ih
  have hbounded := hdegree (X ^ (d + 1) * p) (hpowers (d + 1))
  rw [Polynomial.natDegree_X_pow_mul _ hp0] at hbounded
  omega

/-- Inclusion and multiplication by X increase a nonzero slice dimension by ≥1. -/
theorem dimension_growth
    (V W : Submodule K K[X]) [FiniteDimensional K W]
    (hV : V ≠ ⊥) {d : ℕ}
    (hdegree : ∀ p : K[X], p ∈ V → p.natDegree ≤ d)
    (hinclusion : V ≤ W)
    (hmul : ∀ p : K[X], p ∈ V → X * p ∈ W) :
    Module.finrank K V + 1 ≤ Module.finrank K W := by
  obtain ⟨p, hp, hnot⟩ := exists_mul_X_not_mem V hV hdegree
  have hne : V ≠ W := by
    intro heq
    exact hnot (heq.symm ▸ hmul p hp)
  have hstrict : V < W := lt_of_le_of_ne hinclusion hne
  have hdim := Submodule.finrank_lt_finrank_of_lt hstrict
  omega

/--
No-rise for an actual bounded polynomial-slice family. The exact Hilbert
dimension identity and the two multiplication containments are explicit.
-/
theorem no_rise_of_polynomial_slices
    (V : ℕ → Submodule K K[X])
    [∀ j, FiniteDimensional K (V j)]
    (hdegree : ∀ j p, p ∈ V j → p.natDegree ≤ j)
    (hinclusion : ∀ j, V j ≤ V (j + 1))
    (hmul : ∀ j p, p ∈ V j → X * p ∈ V (j + 1))
    (e : ℕ → ℕ)
    (hdim : ∀ j, e j + Module.finrank K (V j) = j + 1) :
    ∀ j, e j < j + 1 → e (j + 1) ≤ e j := by
  intro j hj
  have hnonzero : V j ≠ ⊥ := by
    intro hzero
    have hz : Module.finrank K (V j) = 0 := Submodule.finrank_eq_zero.mpr hzero
    have h := hdim j
    omega
  have hgrowth := dimension_growth (V j) (V (j + 1)) hnonzero
    (hdegree j) (hinclusion j) (hmul j)
  have hcurrent := hdim j
  have hnext := hdim (j + 1)
  omega

theorem no_rise_tail_of_polynomial_slices
    (V : ℕ → Submodule K K[X])
    [∀ j, FiniteDimensional K (V j)]
    (hdegree : ∀ j p, p ∈ V j → p.natDegree ≤ j)
    (hinclusion : ∀ j, V j ≤ V (j + 1))
    (hmul : ∀ j p, p ∈ V j → X * p ∈ V (j + 1))
    (e : ℕ → ℕ)
    (hdim : ∀ j, e j + Module.finrank K (V j) = j + 1)
    {j t : ℕ} (hdeficit : e j < j + 1) (hjt : j ≤ t) : e t ≤ e j := by
  exact HilbertSequence.binary_no_rise_tail e
    (no_rise_of_polynomial_slices V hdegree hinclusion hmul e hdim) hdeficit hjt

end EvenOrderMDS.BinaryGrowth
