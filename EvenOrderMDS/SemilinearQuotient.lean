module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

/-!
# Quotient injection and dimensions under a field automorphism

This is the actual linear-algebra component of manuscript Lemma 5.1. It does
not construct the polynomial map or prove that its kernel is the shear space.
Those geometric hypotheses must be supplied explicitly.
-/

namespace EvenOrderMDS.SemilinearQuotient

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A field automorphism, rather than merely a scalar map, preserves independence. -/
theorem independent_map
    {ι : Type*} {v : ι → V} (hv : LinearIndependent K v)
    (σ : K ≃+* K) (f : V →ₛₗ[σ.toRingHom] W) (hf : Function.Injective f) :
    LinearIndependent K (fun i => f (v i)) := by
  exact hv.map_of_surjective_injectiveₛ (fun c => σ c) f.toAddMonoidHom
    σ.surjective hf (fun c x => f.map_smulₛₗ c x)

theorem finrank_le_of_injective_semilinear
    [FiniteDimensional K V] [FiniteDimensional K W]
    (σ : K ≃+* K) (f : V →ₛₗ[σ.toRingHom] W) (hf : Function.Injective f) :
    Module.finrank K V ≤ Module.finrank K W := by
  have h := independent_map (Module.finBasis K V).linearIndependent σ f hf
  simpa using h.fintype_card_le_finrank

/-- The induced map is defined only after proving the exact kernel identity. -/
def quotientMap
    (σ : K ≃+* K) (f : V →ₛₗ[σ.toRingHom] W)
    (S : Submodule K V) (hS : S = LinearMap.ker f) :
    (V ⧸ S) →ₛₗ[σ.toRingHom] W :=
  S.liftQ f hS.le

theorem quotientMap_apply
    (σ : K ≃+* K) (f : V →ₛₗ[σ.toRingHom] W)
    (S : Submodule K V) (hS : S = LinearMap.ker f) (v : V) :
    quotientMap σ f S hS (Submodule.Quotient.mk v) = f v := by
  rfl

theorem quotientMap_injective
    (σ : K ≃+* K) (f : V →ₛₗ[σ.toRingHom] W)
    (S : Submodule K V) (hS : S = LinearMap.ker f) :
    Function.Injective (quotientMap σ f S hS) := by
  apply LinearMap.ker_eq_bot.mp
  exact S.ker_liftQ_eq_bot' f hS

theorem quotient_finrank_le
    [FiniteDimensional K V] [FiniteDimensional K W]
    (σ : K ≃+* K) (f : V →ₛₗ[σ.toRingHom] W)
    (S : Submodule K V) (hS : S = LinearMap.ker f) :
    Module.finrank K (V ⧸ S) ≤ Module.finrank K W := by
  exact finrank_le_of_injective_semilinear σ (quotientMap σ f S hS)
    (quotientMap_injective σ f S hS)

/-- Concrete vector-space version of the final capacity contradiction. -/
theorem independent_quotient_rows_impossible
    [FiniteDimensional K V] [FiniteDimensional K W]
    (σ : K ≃+* K) (f : V →ₛₗ[σ.toRingHom] W)
    (S : Submodule K V) (hS : S = LinearMap.ker f)
    {t : ℕ} (ht : 1 ≤ t) (rows : Fin t → (V ⧸ S))
    (hrows : LinearIndependent K rows)
    (hcapacity : Module.finrank K W ≤ t - 1) : False := by
  have hlow : t ≤ Module.finrank K (V ⧸ S) := by
    simpa using hrows.fintype_card_le_finrank
  have hupp := quotient_finrank_le σ f S hS
  omega

end EvenOrderMDS.SemilinearQuotient
