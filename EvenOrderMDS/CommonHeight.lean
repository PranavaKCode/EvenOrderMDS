module

public import EvenOrderMDS.SemilinearQuotient

@[expose] public noncomputable section

/-!
# The common-height linear-algebra bridge

Compatibility is a subspace of height/auxiliary pairs. Injectivity of its
projection gives unique auxiliary data. An explicitly supplied shear-kernel
identity then gives the semilinear quotient injection. Appending independent
height rows supplies an independent family in the quotient.

No statement here asserts that compatible heights are actual arc lifts.
-/

namespace EvenOrderMDS.CommonHeight

variable {K H Q J : Type*} [Field K]
variable [AddCommGroup H] [Module K H]
variable [AddCommGroup Q] [Module K Q]
variable [AddCommGroup J] [Module K J]

def heightProjection (Γ : Submodule K (H × Q)) : Γ →ₗ[K] H :=
  (LinearMap.fst K H Q).comp Γ.subtype

def heightSpace (Γ : Submodule K (H × Q)) : Submodule K H :=
  LinearMap.range (heightProjection Γ)

noncomputable def heightEquiv (Γ : Submodule K (H × Q))
    (hprojection : Function.Injective (heightProjection Γ)) :
    Γ ≃ₗ[K] heightSpace Γ :=
  LinearEquiv.ofInjective (heightProjection Γ) hprojection

theorem unique_compatible_pair
    (Γ : Submodule K (H × Q))
    (hprojection : Function.Injective (heightProjection Γ)) (h : heightSpace Γ) :
    ∃! u : Γ, heightProjection Γ u = (h : H) := by
  refine ⟨(heightEquiv Γ hprojection).symm h, ?_, ?_⟩
  · exact LinearEquiv.ofInjective_symm_apply _ _
  · intro u hu
    apply hprojection
    exact hu.trans (LinearEquiv.ofInjective_symm_apply _ _).symm

/-- Move a supplied semilinear obstruction from pairs to their unique heights. -/
noncomputable def obstructionOnHeights
    (Γ : Submodule K (H × Q))
    (hprojection : Function.Injective (heightProjection Γ))
    (σ : K ≃+* K) (φ : Γ →ₛₗ[σ.toRingHom] J) :
    heightSpace Γ →ₛₗ[σ.toRingHom] J :=
  φ.comp (heightEquiv Γ hprojection).symm.toLinearMap

/-- Transport of the shear subspace; the kernel identity is not part of this definition. -/
noncomputable def shearHeights
    (Γ : Submodule K (H × Q))
    (hprojection : Function.Injective (heightProjection Γ))
    (shearPairs : Submodule K Γ) : Submodule K (heightSpace Γ) :=
  shearPairs.map (heightEquiv Γ hprojection).toLinearMap

theorem shearHeights_eq_kernel
    (Γ : Submodule K (H × Q))
    (hprojection : Function.Injective (heightProjection Γ))
    (σ : K ≃+* K) (φ : Γ →ₛₗ[σ.toRingHom] J)
    (shearPairs : Submodule K Γ) (hkernel : shearPairs = LinearMap.ker φ) :
    shearHeights Γ hprojection shearPairs =
      LinearMap.ker (obstructionOnHeights Γ hprojection σ φ) := by
  ext h
  simp only [shearHeights, Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu0 : φ u = 0 := by
      rw [hkernel] at hu
      exact hu
    simp only [obstructionOnHeights, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact hu0
  · intro hh
    refine ⟨(heightEquiv Γ hprojection).symm h, ?_, ?_⟩
    · rw [hkernel]
      exact hh
    · exact (heightEquiv Γ hprojection).apply_symm_apply h

theorem common_height_quotient_bound
    (Γ : Submodule K (H × Q)) [FiniteDimensional K Γ] [FiniteDimensional K J]
    (hprojection : Function.Injective (heightProjection Γ))
    (σ : K ≃+* K) (φ : Γ →ₛₗ[σ.toRingHom] J)
    (shearPairs : Submodule K Γ) (hkernel : shearPairs = LinearMap.ker φ) :
    Module.finrank K (heightSpace Γ ⧸ shearHeights Γ hprojection shearPairs) ≤
      Module.finrank K J := by
  letI : FiniteDimensional K (heightSpace Γ) :=
    (heightEquiv Γ hprojection).finiteDimensional
  exact SemilinearQuotient.quotient_finrank_le σ
    (obstructionOnHeights Γ hprojection σ φ)
    (shearHeights Γ hprojection shearPairs)
    (shearHeights_eq_kernel Γ hprojection σ φ shearPairs hkernel)

/-- Full independence of base and appended rows implies quotient independence. -/
theorem appended_rows_independent_mod_base
    {b t : ℕ} (base : Fin b → H) (rows : Fin t → H)
    (hstack : LinearIndependent K (Sum.elim base rows)) :
    LinearIndependent K
      (fun i => (Submodule.span K (Set.range base)).mkQ (rows i)) := by
  have hparts := linearIndependent_sum.mp hstack
  have hrows : LinearIndependent K rows := by simpa using hparts.2.1
  have hdis : Disjoint (Submodule.span K (Set.range rows))
      (Submodule.span K (Set.range base)) := by simpa using hparts.2.2.symm
  exact hrows.map (f := (Submodule.span K (Set.range base)).mkQ) (by
    simpa only [Submodule.ker_mkQ] using hdis)

theorem appended_rows_quotient_dimension
    [FiniteDimensional K H]
    {b t : ℕ} (base : Fin b → H) (rows : Fin t → H)
    (hstack : LinearIndependent K (Sum.elim base rows)) :
    t ≤ Module.finrank K (H ⧸ Submodule.span K (Set.range base)) := by
  have h := appended_rows_independent_mod_base base rows hstack
  simpa using h.fintype_card_le_finrank

end EvenOrderMDS.CommonHeight
