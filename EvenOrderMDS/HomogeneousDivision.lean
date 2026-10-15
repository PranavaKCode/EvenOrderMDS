module

public import EvenOrderMDS.PowerIdealDecomposition

@[expose] public noncomputable section

/-! Actual division by a homogeneous factor in an internally graded algebra. -/

namespace EvenOrderMDS.HomogeneousDivision

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem exists_homogeneous_quotient (A : ℕ → Submodule K R) [GradedAlgebra A]
    {m n : ℕ} {c p : R} (hc : c ∈ A m) (hp : p ∈ A (m + n)) (hdiv : c ∣ p) :
    ∃ r : R, r ∈ A n ∧ p = c * r := by
  obtain ⟨r, rfl⟩ := hdiv
  have h : (DirectSum.decompose A (c * r) (m + n) : R) = c * r :=
    DirectSum.decompose_of_mem_same A hp
  rw [DirectSum.coe_decompose_mul_of_left_mem A (m + n) hc, if_pos (by omega)] at h
  have hi : m + n - m = n := by omega
  rw [hi] at h
  exact ⟨DirectSum.decompose A r n, (DirectSum.decompose A r n).property, h.symm⟩

end EvenOrderMDS.HomogeneousDivision
