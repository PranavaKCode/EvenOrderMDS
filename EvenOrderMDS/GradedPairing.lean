module

public import EvenOrderMDS.GradedSocle
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public noncomputable section

/-!
# Complementary graded pairings and Hilbert symmetry

The internally graded algebra, exact top degree, nonzero top, and actual
one-dimensional positive-degree socle are explicit. Perfect pairing and
Hilbert symmetry are proved here, not included in those hypotheses.
-/

namespace EvenOrderMDS.GradedPairing

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def topProjection (A : ℕ → Submodule K R) [GradedAlgebra A] (s : ℕ) :
    R →ₗ[K] A s :=
  (GradedAlgebra.proj A s).codRestrict (A s)
    (fun r => (DirectSum.decompose A r s).property)

theorem topProjection_apply_of_mem
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ} {u : R} (hu : u ∈ A s) :
    (topProjection A s u : R) = u := by
  exact DirectSum.decompose_of_mem_same A hu

theorem exists_top_detecting_functional
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (htop : Module.finrank K (A s) = 1) :
    ∃ trace : R →ₗ[K] K, ∀ u : R, u ∈ A s → trace u = 0 → u = 0 := by
  let e : A s ≃ₗ[K] K := LinearEquiv.ofFinrankEq (A s) K
    (htop.trans (Module.finrank_self K).symm)
  let trace : R →ₗ[K] K := e.toLinearMap.comp (topProjection A s)
  refine ⟨trace, ?_⟩
  intro u hu htrace
  have hzero : topProjection A s u = 0 := by
    apply e.injective
    simpa only [trace, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using htrace
  have hval := congrArg Subtype.val hzero
  rw [topProjection_apply_of_mem A hu] at hval
  exact hval

def piecePairing (A : ℕ → Submodule K R) (trace : R →ₗ[K] K) (i j : ℕ) :
    A i →ₗ[K] Module.Dual K (A j) :=
  LinearMap.mk₂ K (fun u v => trace ((u : R) * (v : R)))
    (by intro u₁ u₂ v; simp [add_mul])
    (by intro c u v; simp)
    (by intro u v₁ v₂; simp [mul_add])
    (by intro c u v; simp)

theorem complementary_pairing_injective
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (GradedSocle.positiveSocle A) = 1)
    (trace : R →ₗ[K] K)
    (detectsTop : ∀ u : R, u ∈ A s → trace u = 0 → u = 0)
    {i : ℕ} (hi : i ≤ s) :
    Function.Injective (piecePairing A trace i (s - i)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hzero
  apply Classical.byContradiction
  intro hu0
  have hval : (u : R) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨v, hv, hvu⟩ := GradedSocle.complementary_product_exists A
    aboveTop topNonzero socleDimension u.property hval
  have hsum : (s - i) + i = s := by omega
  have hprod : v * (u : R) ∈ A s := by
    simpa only [hsum] using SetLike.mul_mem_graded hv u.property
  have htracezero : trace (v * (u : R)) = 0 := by
    have h := LinearMap.congr_fun hzero (⟨v, hv⟩ : A (s - i))
    simpa [piecePairing, mul_comm] using h
  exact hvu (detectsTop _ hprod htracezero)

/-- Hilbert symmetry for an actual finite internally graded algebra. -/
theorem complementary_finrank_eq
    [FiniteDimensional K R]
    (A : ℕ → Submodule K R) [GradedAlgebra A] {s : ℕ}
    (aboveTop : ∀ j : ℕ, s < j → A j = ⊥)
    (topNonzero : A s ≠ ⊥)
    (socleDimension : Module.finrank K (GradedSocle.positiveSocle A) = 1)
    {i : ℕ} (hi : i ≤ s) :
    Module.finrank K (A i) = Module.finrank K (A (s - i)) := by
  have htop : Module.finrank K (A s) = 1 := by
    rw [GradedSocle.top_eq_positiveSocle A aboveTop topNonzero socleDimension]
    exact socleDimension
  obtain ⟨trace, htrace⟩ := exists_top_detecting_functional A htop
  have hleft := complementary_pairing_injective A aboveTop topNonzero
    socleDimension trace htrace hi
  have hright := complementary_pairing_injective A aboveTop topNonzero
    socleDimension trace htrace (Nat.sub_le s i)
  have hle := LinearMap.finrank_le_finrank_of_injective hleft
  have hge := LinearMap.finrank_le_finrank_of_injective hright
  have hindex : s - (s - i) = i := by omega
  rw [Subspace.dual_finrank_eq] at hle hge
  rw [hindex] at hge
  exact Nat.le_antisymm hle hge

end EvenOrderMDS.GradedPairing
