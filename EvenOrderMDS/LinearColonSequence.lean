module

public import EvenOrderMDS.ColonQuotient
public import EvenOrderMDS.HilbertSequence

@[expose] public noncomputable section

/-!
# The exact Hilbert dimension sequence for a linear class

The principal quotient and annihilator quotient are actual quotient rings.
Homogeneous decomposition proves the precise graded kernel; rank-nullity then
gives h_j = g_(j-1) + e_j, including the zero-degree convention.
-/

namespace EvenOrderMDS.LinearColonSequence

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def principalMap (c : R) : R →ₐ[K] R ⧸ Ideal.span ({c} : Set R) :=
  Ideal.Quotient.mkₐ K (Ideal.span ({c} : Set R))

theorem principalMap_eq_zero_iff (c r : R) :
    principalMap (K := K) c r = 0 ↔ c ∣ r := by
  change Ideal.Quotient.mk (Ideal.span ({c} : Set R)) r = 0 ↔ c ∣ r
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

def principalKernelSlice (A : ℕ → Submodule K R) (c : R) (j : ℕ) : Submodule K R :=
  A j ⊓ LinearMap.ker (principalMap (K := K) c).toLinearMap

def multipliedColonSlice (A : ℕ → Submodule K R) (c : R) (j : ℕ) : Submodule K R :=
  (GradedImage.imagePieces A (ColonQuotient.quotientMap (K := K) c) j).map
    (ColonQuotient.quotientMul (K := K) c)

theorem principalKernelSlice_eq_multipliedColonSlice
    (A : ℕ → Submodule K R) [GradedAlgebra A] {c : R} (hc : c ∈ A 1)
    {j : ℕ} (hj : 1 ≤ j) :
    principalKernelSlice A c j = multipliedColonSlice A c (j - 1) := by
  ext u
  constructor
  · intro hu
    have hdiv : c ∣ u := (principalMap_eq_zero_iff (K := K) c u).mp hu.2
    obtain ⟨r, rfl⟩ := hdiv
    have hcomponent : (DirectSum.decompose A (c * r) j : R) = c * r :=
      DirectSum.decompose_of_mem_same A hu.1
    rw [DirectSum.coe_decompose_mul_of_left_mem A j hc, if_pos hj] at hcomponent
    refine ⟨ColonQuotient.quotientMap (K := K) c (DirectSum.decompose A r (j - 1)), ?_, ?_⟩
    · exact ⟨DirectSum.decompose A r (j - 1), (DirectSum.decompose A r (j - 1)).property, rfl⟩
    · exact hcomponent
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hv
    change c * r ∈ A j ∧ principalMap (K := K) c (c * r) = 0
    constructor
    · have hprod : c * r ∈ A (1 + (j - 1)) := SetLike.mul_mem_graded hc hr
      have hindex : 1 + (j - 1) = j := by omega
      simpa only [hindex] using hprod
    · exact (principalMap_eq_zero_iff (K := K) c _).mpr ⟨r, rfl⟩

theorem principalKernelSlice_zero
    (A : ℕ → Submodule K R) [GradedAlgebra A] {c : R} (hc : c ∈ A 1) :
    principalKernelSlice A c 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  have hdiv : c ∣ u := (principalMap_eq_zero_iff (K := K) c u).mp hu.2
  obtain ⟨r, rfl⟩ := hdiv
  have hcomponent : (DirectSum.decompose A (c * r) 0 : R) = c * r :=
    DirectSum.decompose_of_mem_same A hu.1
  rw [DirectSum.coe_decompose_mul_of_left_mem A 0 hc, if_neg (by omega)] at hcomponent
  exact hcomponent.symm

theorem multipliedColonSlice_finrank
    (A : ℕ → Submodule K R) (c : R) (j : ℕ) :
    Module.finrank K (multipliedColonSlice A c j) =
      Module.finrank K (GradedImage.imagePieces A (ColonQuotient.quotientMap (K := K) c) j) := by
  let G := GradedImage.imagePieces A (ColonQuotient.quotientMap (K := K) c) j
  let f := (ColonQuotient.quotientMul (K := K) c).comp G.subtype
  have hf : Function.Injective f :=
    (ColonQuotient.quotientMul_injective (K := K) c).comp Subtype.val_injective
  have hdim := LinearMap.finrank_range_of_inj hf
  have hrange : LinearMap.range f = multipliedColonSlice A c j := by
    dsimp only [f]
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  rw [hrange] at hdim
  exact hdim

theorem principal_rank_nullity
    [FiniteDimensional K R] (A : ℕ → Submodule K R) (c : R) (j : ℕ) :
    Module.finrank K (GradedImage.imagePieces A (principalMap (K := K) c) j) +
      Module.finrank K (principalKernelSlice A c j) = Module.finrank K (A j) := by
  let f := (principalMap (K := K) c).toLinearMap.comp (A j).subtype
  have hdim := f.finrank_range_add_finrank_ker
  have hrange : LinearMap.range f = GradedImage.imagePieces A (principalMap (K := K) c) j := by
    dsimp only [f]
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hkernel : (LinearMap.ker f).map (A j).subtype = principalKernelSlice A c j := by
    dsimp only [f]
    rw [LinearMap.ker_comp, Submodule.map_comap_subtype]
    rfl
  have hkerdim : Module.finrank K (principalKernelSlice A c j) =
      Module.finrank K (LinearMap.ker f) := by
    rw [← hkernel]
    exact Submodule.finrank_map_subtype_eq _ _
  rw [hrange] at hdim
  rw [hkerdim]
  exact hdim

theorem hilbert_dimension_sequence
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {c : R} (hc : c ∈ A 1) (j : ℕ) :
    Module.finrank K (A j) =
      HilbertSequence.shift
        (fun i => Module.finrank K (GradedImage.imagePieces A (ColonQuotient.quotientMap (K := K) c) i)) j +
      Module.finrank K (GradedImage.imagePieces A (principalMap (K := K) c) j) := by
  have hdim := principal_rank_nullity A c j
  by_cases hj0 : j = 0
  · subst j
    rw [principalKernelSlice_zero A hc] at hdim
    simpa using hdim.symm
  · have hj : 1 ≤ j := by omega
    rw [principalKernelSlice_eq_multipliedColonSlice A hc hj,
      multipliedColonSlice_finrank] at hdim
    rw [HilbertSequence.shift_of_pos _ hj]
    omega

end EvenOrderMDS.LinearColonSequence
