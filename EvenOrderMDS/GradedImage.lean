module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public noncomputable section

/-!
# Grading the image of a surjective algebra map with homogeneous kernel

The quotient grading is constructed, rather than inserted as an assumption.
This will be applied to both the linear-principal quotient and the annihilator
quotient in the Gorenstein induction.
-/

namespace EvenOrderMDS.GradedImage

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]

def imagePieces (A : ℕ → Submodule K R) (q : R →ₐ[K] S) : ℕ → Submodule K S :=
  fun i => (A i).map q.toLinearMap

def pieceMap (A : ℕ → Submodule K R) (q : R →ₐ[K] S) (i : ℕ) :
    A i →ₗ[K] imagePieces A q i :=
  (q.toLinearMap.comp (A i).subtype).codRestrict (imagePieces A q i)
    (fun x => ⟨x, x.property, rfl⟩)

instance imagePieces_gradedMonoid
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S) :
    SetLike.GradedMonoid (imagePieces A q) where
  one_mem := ⟨1, SetLike.one_mem_graded A, q.map_one⟩
  mul_mem i j x y hx hy := by
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨u * v, SetLike.mul_mem_graded hu hv, q.map_mul u v⟩

def mappedDecomposition
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S) :
    R →ₗ[K] DirectSum ℕ (fun i => imagePieces A q i) :=
  (DirectSum.lmap (pieceMap A q)).comp (DirectSum.decomposeLinearEquiv A).toLinearMap

theorem mappedDecomposition_of_mem
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    {i : ℕ} (u : A i) :
    mappedDecomposition A q u =
      DirectSum.of (fun j => imagePieces A q j) i (pieceMap A q i u) := by
  simp [mappedDecomposition, DirectSum.decompose_coe, DirectSum.lof_eq_of]

theorem recompose_mappedDecomposition
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S) :
    (DirectSum.coeLinearMap (imagePieces A q)).comp (mappedDecomposition A q) =
      q.toLinearMap := by
  apply DirectSum.decompose_lhom_ext A
  intro i
  ext u
  simp [mappedDecomposition_of_mem, pieceMap, LinearMap.codRestrict_apply] <;> rfl

def HomogeneousKernel
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S) : Prop :=
  ∀ r : R, q r = 0 → ∀ i : ℕ, q (DirectSum.decompose A r i : R) = 0

theorem kernel_le_mappedDecomposition_kernel
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    (hkernel : HomogeneousKernel A q) :
    LinearMap.ker q.toLinearMap ≤ LinearMap.ker (mappedDecomposition A q) := by
  intro r hr
  ext i
  exact hkernel r hr i

/-- Two elements with the same image under `q` have the same mapped decomposition. -/
theorem mappedDecomposition_eq_of_eq
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    (hkernel : HomogeneousKernel A q) {r r' : R} (h : q r = q r') :
    mappedDecomposition A q r = mappedDecomposition A q r' := by
  have hmem : r - r' ∈ LinearMap.ker q.toLinearMap := by
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_sub, h, sub_self]
  have h0 := kernel_le_mappedDecomposition_kernel A q hkernel hmem
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0

/-- The decomposition of `S`, defined through a choice of preimages under `q`; it is
well defined and linear because the kernel of `q` is homogeneous. -/
noncomputable def imageDecomposition
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    (hsurjective : Function.Surjective q) (hkernel : HomogeneousKernel A q) :
    S →ₗ[K] DirectSum ℕ (fun i => imagePieces A q i) where
  toFun s := mappedDecomposition A q (Function.surjInv hsurjective s)
  map_add' s t := by
    rw [← map_add]
    apply mappedDecomposition_eq_of_eq A q hkernel
    rw [map_add, Function.surjInv_eq hsurjective, Function.surjInv_eq hsurjective,
      Function.surjInv_eq hsurjective]
  map_smul' c s := by
    rw [RingHom.id_apply, ← map_smul]
    apply mappedDecomposition_eq_of_eq A q hkernel
    rw [map_smul, Function.surjInv_eq hsurjective, Function.surjInv_eq hsurjective]

theorem imageDecomposition_apply_image
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    (hsurjective : Function.Surjective q) (hkernel : HomogeneousKernel A q) (r : R) :
    imageDecomposition A q hsurjective hkernel (q r) = mappedDecomposition A q r := by
  show mappedDecomposition A q (Function.surjInv hsurjective (q r)) = _
  exact mappedDecomposition_eq_of_eq A q hkernel (Function.surjInv_eq hsurjective (q r))

theorem imageDecomposition_left_inverse
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    (hsurjective : Function.Surjective q) (hkernel : HomogeneousKernel A q) :
    (DirectSum.coeLinearMap (imagePieces A q)).comp
      (imageDecomposition A q hsurjective hkernel) = LinearMap.id := by
  ext s
  obtain ⟨r, rfl⟩ := hsurjective s
  change DirectSum.coeLinearMap (imagePieces A q)
    (imageDecomposition A q hsurjective hkernel (q r)) = q r
  rw [imageDecomposition_apply_image]
  exact LinearMap.congr_fun (recompose_mappedDecomposition A q) r

theorem imageDecomposition_right_inverse
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    (hsurjective : Function.Surjective q) (hkernel : HomogeneousKernel A q) :
    (imageDecomposition A q hsurjective hkernel).comp
      (DirectSum.coeLinearMap (imagePieces A q)) = LinearMap.id := by
  apply DirectSum.linearMap_ext K
  intro i
  apply LinearMap.ext
  intro u
  obtain ⟨r, hr, hrq⟩ := u.property
  have hueq : u = pieceMap A q i (⟨r, hr⟩ : A i) := by
    apply Subtype.ext
    exact hrq.symm
  rw [hueq]
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.coeLinearMap_of,
    LinearMap.id_apply]
  change imageDecomposition A q hsurjective hkernel (q r) = _
  rw [imageDecomposition_apply_image]
  exact mappedDecomposition_of_mem A q ⟨r, hr⟩

noncomputable def imageGrading
    (A : ℕ → Submodule K R) [GradedAlgebra A] (q : R →ₐ[K] S)
    (hsurjective : Function.Surjective q) (hkernel : HomogeneousKernel A q) :
    GradedAlgebra (imagePieces A q) :=
  { (inferInstance : SetLike.GradedMonoid (imagePieces A q)) with
    toDecomposition := DirectSum.Decomposition.ofLinearMap (imagePieces A q)
      (imageDecomposition A q hsurjective hkernel)
      (imageDecomposition_left_inverse A q hsurjective hkernel)
      (imageDecomposition_right_inverse A q hsurjective hkernel) }

end EvenOrderMDS.GradedImage
