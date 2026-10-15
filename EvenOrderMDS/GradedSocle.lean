module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Find
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

/-!
# Positive-degree socle and complementary products

This is a concrete internally graded algebra result over an arbitrary field.
The socle is defined as annihilation by all positive homogeneous pieces, not
by assuming a perfect pairing. A one-dimensional socle and an exact top degree
then give nonzero complementary products.

The bridge from the manuscript's standard-graded presentation to these data,
and the linear-colon quotient construction, are separate later modules.
-/

namespace EvenOrderMDS.GradedSocle

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def positiveSocle (A : ℕ → Submodule K R) : Submodule K R where
  carrier := {u | ∀ j : ℕ, 0 < j → ∀ v : R, v ∈ A j → v * u = 0}
  zero_mem' := by intro j hj v hv; simp
  add_mem' := by
    intro u w hu hw j hj v hv
    rw [mul_add, hu j hj v hv, hw j hj v hv, add_zero]
  smul_mem' := by
    intro c u hu j hj v hv
    rw [mul_smul_comm, hu j hj v hv, smul_zero]

theorem top_le_positiveSocle
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥) : A s ≤ positiveSocle A := by
  intro u hu j hj v hv
  have hprod : v * u ∈ A (j + s) := SetLike.mul_mem_graded hv hu
  rw [aboveTop (j + s) (by omega)] at hprod
  exact hprod

theorem top_eq_positiveSocle
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (positiveSocle A) = 1) :
    A s = positiveSocle A := by
  have hle := top_le_positiveSocle A aboveTop
  have hpos : 1 ≤ Module.finrank K (A s) := Submodule.one_le_finrank_iff.mpr topNonzero
  apply Submodule.eq_of_le_of_finrank_le hle
  simpa only [socleDimension] using hpos

/--
Every nonzero homogeneous element has a nonzero complementary product. The
proof maximizes the degree of a multiplier, then reaches the actual socle.
-/
theorem complementary_product_exists
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (positiveSocle A) = 1)
    {i : ℕ} {u : R} (hu : u ∈ A i) (hu0 : u ≠ 0) :
    ∃ v : R, v ∈ A (s - i) ∧ v * u ≠ 0 := by
  classical
  let P : ℕ → Prop := fun j => ∃ v : R, v ∈ A j ∧ v * u ≠ 0
  have hP0 : P 0 := ⟨1, SetLike.one_mem_graded A, by simpa using hu0⟩
  let t := Nat.findGreatest P s
  have htP : P t := Nat.findGreatest_spec (Nat.zero_le s) hP0
  obtain ⟨v, hv, hvu⟩ := htP
  have hsocle : v * u ∈ positiveSocle A := by
    intro j hj z hz
    apply Classical.byContradiction
    intro hnonzero
    have hzv : z * v ∈ A (j + t) := SetLike.mul_mem_graded hz hv
    have hzu : (z * v) * u ≠ 0 := by simpa only [mul_assoc] using hnonzero
    have hbound : j + t ≤ s := by
      apply Nat.le_of_not_gt
      intro hlarge
      rw [aboveTop (j + t) hlarge] at hzv
      have hzv0 : z * v = 0 := hzv
      exact hzu (by rw [hzv0, zero_mul])
    have hPjt : P (j + t) := ⟨z * v, hzv, hzu⟩
    have hmax : j + t ≤ t := Nat.le_findGreatest hbound hPjt
    omega
  have htop : v * u ∈ A s := by
    rw [top_eq_positiveSocle A aboveTop topNonzero socleDimension]
    exact hsocle
  have hgraded : v * u ∈ A (t + i) := SetLike.mul_mem_graded hv hu
  have hindices : t + i = s := DirectSum.degree_eq_of_mem_mem A hgraded htop hvu
  have ht : t = s - i := by omega
  exact ⟨v, ht ▸ hv, hvu⟩

end EvenOrderMDS.GradedSocle
