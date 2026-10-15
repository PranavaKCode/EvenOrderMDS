module

public import EvenOrderMDS.HilbertSequence
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum

@[expose] public noncomputable section

/-!
# The numerical critical-kernel bound

This module proves the arithmetic implication used in manuscript Lemma 6.6.
The Hilbert data are explicit premises. No polynomial colon ideal is defined
here, and this theorem is not presented as the colon-ideal theorem itself.
-/

namespace EvenOrderMDS.CriticalDimension

open HilbertSequence

/-- The number of degree-d monomials in three variables. -/
def ternaryDimension (d : ℕ) : ℕ := Nat.choose (d + 2) 2

@[simp] theorem ternaryDimension_zero : ternaryDimension 0 = 1 := by
  norm_num [ternaryDimension]

@[simp] theorem ternaryDimension_one : ternaryDimension 1 = 3 := by
  norm_num [ternaryDimension]

theorem ternaryDimension_step (d : ℕ) :
    ternaryDimension (d + 1) = ternaryDimension d + (d + 2) := by
  unfold ternaryDimension
  rw [show d + 1 + 2 = (d + 2) + 1 by omega]
  rw [Nat.choose_succ_succ]
  simp
  omega

theorem ternaryDimension_pred_step {d : ℕ} (hd : 1 ≤ d) :
    ternaryDimension d = ternaryDimension (d - 1) + (d + 1) := by
  have h := ternaryDimension_step (d - 1)
  have hidx : d - 1 + 1 = d := by omega
  have hinc : d - 1 + 2 = d + 1 := by omega
  rw [hidx, hinc] at h
  exact h

/--
All branches of the numerical bound, including d=0 and the upper endpoint.
The d=0 branch makes no use of nonzero quotient or Gorenstein hypotheses.
-/
theorem kernel_bound_of_hilbert_data
    {n d κ : ℕ} (hn : 2 ≤ n) (hdn : d ≤ n - 2)
    (h : ℕ → ℕ)
    (ambientDimension : κ + h d = ternaryDimension d)
    (noEarlierKernel : ∀ j : ℕ, j < d → h j = ternaryDimension j)
    (positiveDegreeOne : d = 1 → 1 ≤ h 1)
    (symmetry : Symmetric (n + d - 3) h)
    (firstHalf : FirstHalfMonotone (n + d - 3) h) :
    κ ≤ d + 1 := by
  by_cases hd0 : d = 0
  · subst d
    simp only [ternaryDimension_zero] at ambientDimension
    omega
  by_cases hd1 : d = 1
  · have hpos := positiveDegreeOne hd1
    subst d
    simp only [ternaryDimension_one] at ambientDimension
    omega
  have hd2 : 2 ≤ d := by omega
  have hprev := noEarlierKernel (d - 1) (by omega)
  have hdim := ternaryDimension_pred_step (d := d) (by omega)
  have hmono : h (d - 1) ≤ h d := by
    by_cases hend : d = n - 2
    · have hs : n + d - 3 = 2 * d - 1 := by omega
      have hsym := symmetry d (by omega)
      have hidx : (n + d - 3) - d = d - 1 := by omega
      rw [hidx] at hsym
      omega
    · exact firstHalf d (by omega) (by omega)
  omega

/-- At the upper endpoint, symmetry alone forces the maximal critical kernel. -/
theorem kernel_endpoint_exact_of_hilbert_data
    {n d κ : ℕ} (hd : 2 ≤ d) (hend : d + 2 = n)
    (h : ℕ → ℕ)
    (ambientDimension : κ + h d = ternaryDimension d)
    (previousDegree : h (d - 1) = ternaryDimension (d - 1))
    (symmetry : Symmetric (n + d - 3) h) :
    κ = d + 1 := by
  have hsym := symmetry d (by omega)
  have hidx : (n + d - 3) - d = d - 1 := by omega
  rw [hidx] at hsym
  have hdim := ternaryDimension_pred_step (d := d) (by omega)
  omega

/-- Pure dimensional contradiction. The positive-center guard is essential. -/
theorem impossible_height_capacity
    {t quotientDimension kernelDimension : ℕ} (ht : 1 ≤ t)
    (independentRows : t ≤ quotientDimension)
    (forwardInjection : quotientDimension ≤ kernelDimension)
    (kernelBound : kernelDimension ≤ t - 1) : False := by
  omega

end EvenOrderMDS.CriticalDimension
