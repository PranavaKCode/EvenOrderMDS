module

public import EvenOrderMDS.GradedImage
public import EvenOrderMDS.GradedSocle
public import EvenOrderMDS.GradedPairing
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public noncomputable section

/-!
# The concrete annihilator quotient of a homogeneous element

The quotient ring and its grading are constructed here. For a nonzero
homogeneous element, its exact shifted top degree, one-dimensional socle, and
Hilbert symmetry are proved. Standard generation and the exact linear-principal
quotient sequence remain separate obligations.
-/

namespace EvenOrderMDS.ColonQuotient

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def annihilatorIdeal (c : R) : Ideal R where
  carrier := {r | c * r = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv; simp only [Set.mem_setOf_eq] at *; rw [mul_add, hu, hv, add_zero]
  smul_mem' := by
    intro a r hr
    change c * (a * r) = 0
    rw [mul_left_comm, hr, mul_zero]

def quotientMap (c : R) : R →ₐ[K] R ⧸ annihilatorIdeal c :=
  Ideal.Quotient.mkₐ K (annihilatorIdeal c)

theorem quotientMap_eq_zero_iff (c r : R) : quotientMap (K := K) c r = 0 ↔ c * r = 0 := by
  change Ideal.Quotient.mk (annihilatorIdeal c) r = 0 ↔ r ∈ annihilatorIdeal c
  exact Ideal.Quotient.eq_zero_iff_mem

theorem quotientMap_surjective (c : R) : Function.Surjective (quotientMap (K := K) c) :=
  Ideal.Quotient.mkₐ_surjective K (annihilatorIdeal c)

/-- The quotient has a faithful multiplication-by-c map into the original algebra. -/
def quotientMul (c : R) : (R ⧸ annihilatorIdeal c) →ₗ[K] R :=
  ((annihilatorIdeal c).restrictScalars K).liftQ (LinearMap.mulLeft K c)
    (by intro r hr; exact hr)

theorem quotientMul_apply_image (c r : R) :
    quotientMul (K := K) c (quotientMap (K := K) c r) = c * r := by
  rfl

theorem quotientMul_injective (c : R) : Function.Injective (quotientMul (K := K) c) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro r hr
  exact hr

theorem annihilator_kernel_homogeneous
    (A : ℕ → Submodule K R) [GradedAlgebra A] {d : ℕ} {c : R} (hc : c ∈ A d) :
    GradedImage.HomogeneousKernel A (quotientMap (K := K) c) := by
  intro r hr i
  apply (quotientMap_eq_zero_iff (K := K) c _).mpr
  have hcr : c * r = 0 := (quotientMap_eq_zero_iff (K := K) c r).mp hr
  have h := congrArg (fun z => (DirectSum.decompose A z (d + i) : R)) hcr
  try dsimp only at h
  rw [DirectSum.coe_decompose_mul_of_left_mem A (d + i) hc] at h
  rw [if_pos (show d ≤ d + i by omega)] at h
  have hindex : d + i - d = i := by omega
  rw [hindex] at h
  simpa using h

noncomputable def quotientGrading
    (A : ℕ → Submodule K R) [GradedAlgebra A] {d : ℕ} {c : R} (hc : c ∈ A d) :
    GradedAlgebra (GradedImage.imagePieces A (quotientMap (K := K) c)) :=
  GradedImage.imageGrading A (quotientMap (K := K) c) (quotientMap_surjective (K := K) c)
    (annihilator_kernel_homogeneous A hc)

theorem quotient_piece_above_top
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s d : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥) (hd : d ≤ s)
    {c : R} (hc : c ∈ A d) {i : ℕ} (hi : s - d < i) :
    GradedImage.imagePieces A (quotientMap (K := K) c) i = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  obtain ⟨r, hr, rfl⟩ := hu
  apply (quotientMap_eq_zero_iff (K := K) c r).mpr
  have hprod : c * r ∈ A (d + i) := SetLike.mul_mem_graded hc hr
  rw [aboveTop (d + i) (by omega)] at hprod
  exact hprod

theorem quotient_top_nonzero
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s d : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (GradedSocle.positiveSocle A) = 1)
    {c : R} (hc : c ∈ A d) (hc0 : c ≠ 0) :
    GradedImage.imagePieces A (quotientMap (K := K) c) (s - d) ≠ ⊥ := by
  obtain ⟨v, hv, hvc⟩ := GradedSocle.complementary_product_exists A
    aboveTop topNonzero socleDimension hc hc0
  apply (GradedImage.imagePieces A (quotientMap (K := K) c) (s - d)).ne_bot_iff.mpr
  refine ⟨quotientMap (K := K) c v, ⟨v, hv, rfl⟩, ?_⟩
  intro hz
  have hcv := (quotientMap_eq_zero_iff (K := K) c v).mp hz
  exact hvc (by simpa only [mul_comm] using hcv)

theorem quotientMul_compatible
    (c r : R) (u : R ⧸ annihilatorIdeal c) :
    quotientMul (K := K) c (quotientMap (K := K) c r * u) =
      r * quotientMul (K := K) c u := by
  obtain ⟨v, rfl⟩ := quotientMap_surjective (K := K) c u
  rw [← map_mul, quotientMul_apply_image, quotientMul_apply_image]
  exact mul_left_comm c r v

theorem quotientMul_sends_socle_to_socle
    (A : ℕ → Submodule K R) (c : R)
    {u : R ⧸ annihilatorIdeal c}
    (hu : u ∈ GradedSocle.positiveSocle
      (GradedImage.imagePieces A (quotientMap (K := K) c))) :
    quotientMul (K := K) c u ∈ GradedSocle.positiveSocle A := by
  intro j hj r hr
  have hprod : quotientMap (K := K) c r * u = 0 :=
    hu j hj _ ⟨r, hr, rfl⟩
  have hmapped := congrArg (quotientMul (K := K) c) hprod
  simpa only [quotientMul_compatible, map_zero] using hmapped

theorem quotient_socle_finrank_le
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) (c : R) :
    Module.finrank K (GradedSocle.positiveSocle
      (GradedImage.imagePieces A (quotientMap (K := K) c))) ≤
      Module.finrank K (GradedSocle.positiveSocle A) := by
  let W := GradedSocle.positiveSocle
    (GradedImage.imagePieces A (quotientMap (K := K) c))
  let f : W →ₗ[K] GradedSocle.positiveSocle A :=
    ((quotientMul (K := K) c).comp W.subtype).codRestrict
      (GradedSocle.positiveSocle A)
      (fun u => quotientMul_sends_socle_to_socle A c u.property)
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply quotientMul_injective (K := K) c
    exact congrArg Subtype.val huv
  exact LinearMap.finrank_le_finrank_of_injective hf

/-- Gorenstein socle preservation for a nonzero homogeneous colon element. -/
theorem quotient_socle_dimension
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s d : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (GradedSocle.positiveSocle A) = 1)
    (hd : d ≤ s) {c : R} (hc : c ∈ A d) (hc0 : c ≠ 0) :
    Module.finrank K (GradedSocle.positiveSocle
      (GradedImage.imagePieces A (quotientMap (K := K) c))) = 1 := by
  let B := GradedImage.imagePieces A (quotientMap (K := K) c)
  letI : GradedAlgebra B := quotientGrading A hc
  letI : FiniteDimensional K (R ⧸ annihilatorIdeal c) :=
    FiniteDimensional.of_injective (quotientMul (K := K) c)
      (quotientMul_injective (K := K) c)
  have htop : B (s - d) ≠ ⊥ :=
    quotient_top_nonzero A aboveTop topNonzero socleDimension hc hc0
  have habove : ∀ j : ℕ, s - d < j → B j = ⊥ :=
    fun _ hj => quotient_piece_above_top A aboveTop hd hc hj
  have hsocle : GradedSocle.positiveSocle B ≠ ⊥ := by
    intro hz
    have hle : B (s - d) ≤ ⊥ := by
      rw [← hz]
      exact GradedSocle.top_le_positiveSocle B habove
    exact htop (le_antisymm hle bot_le)
  have hpos : 1 ≤ Module.finrank K (GradedSocle.positiveSocle B) :=
    Submodule.one_le_finrank_iff.mpr hsocle
  have hle := quotient_socle_finrank_le A c
  rw [socleDimension] at hle
  exact Nat.le_antisymm hle hpos

theorem quotient_piece_finrank_le
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) (c : R) (i : ℕ) :
    Module.finrank K (GradedImage.imagePieces A (quotientMap (K := K) c) i) ≤
      Module.finrank K (A i) := by
  exact Submodule.finrank_map_le (quotientMap (K := K) c).toLinearMap (A i)

theorem quotient_hilbert_symmetry
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s d : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (GradedSocle.positiveSocle A) = 1)
    (hd : d ≤ s) {c : R} (hc : c ∈ A d) (hc0 : c ≠ 0)
    {i : ℕ} (hi : i ≤ s - d) :
    Module.finrank K (GradedImage.imagePieces A (quotientMap (K := K) c) i) =
      Module.finrank K (GradedImage.imagePieces A (quotientMap (K := K) c) (s - d - i)) := by
  let B := GradedImage.imagePieces A (quotientMap (K := K) c)
  letI : GradedAlgebra B := quotientGrading A hc
  letI : FiniteDimensional K (R ⧸ annihilatorIdeal c) :=
    FiniteDimensional.of_injective (quotientMul (K := K) c)
      (quotientMul_injective (K := K) c)
  exact GradedPairing.complementary_finrank_eq B
    (fun _ hj => quotient_piece_above_top A aboveTop hd hc hj)
    (quotient_top_nonzero A aboveTop topNonzero socleDimension hc hc0)
    (quotient_socle_dimension A aboveTop topNonzero socleDimension hd hc hc0) hi

end EvenOrderMDS.ColonQuotient
