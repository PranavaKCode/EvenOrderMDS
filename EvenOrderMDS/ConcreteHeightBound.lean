module

public import EvenOrderMDS.ConcreteShearInjection

@[expose] public noncomputable section

/-! The literal shear dimension and the concrete common-height capacity. -/

namespace EvenOrderMDS.ConcreteHeightBound

open ConcreteShearInjection ShearPolynomials
open scoped Matrix

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

omit [CharP K 2] [Fintype K] in
theorem heights_injective {M : ℕ} (hM : 3 ≤ M) (a : Fin M → Fin 3 → K)
    (ha : Arc.IsArc (K := K) 3 a) : Function.Injective (heights a) := by
  intro s v h
  let e : Fin 3 ↪ Fin M := Fin.castLEEmb hM
  have hlin := ha e
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hlin
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  funext i
  exact congrFun h (e i)

noncomputable def heightShearMap (D : PlaneData K) : (Fin 3 → K) →ₗ[K] D.heightSpace :=
  (CommonHeight.heightEquiv D.compatible D.projection_injective).toLinearMap.comp D.shearMap

theorem heightShearMap_apply (D : PlaneData K) (s : Fin 3 → K) :
    (heightShearMap D s).val = heights D.columns s := rfl

theorem heightShearMap_injective (D : PlaneData K) : Function.Injective (heightShearMap D) := by
  intro s v h
  apply heights_injective D.enough_columns D.columns D.arc
  exact congrArg Subtype.val h

theorem shearHeights_eq_range (D : PlaneData K) : D.shearHeights = LinearMap.range (heightShearMap D) := by
  ext h
  rw [D.mem_shearHeights]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, Subtype.ext hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

theorem shearHeights_dimension (D : PlaneData K) : Module.finrank K D.shearHeights = 3 := by
  rw [shearHeights_eq_range, LinearMap.finrank_range_of_inj (heightShearMap_injective D)]
  simp

theorem half_power_of_two {n e : ℕ} (hexp : 2 ^ e = 2 * n) : ∃ f, n = 2 ^ f := by
  cases e with
  | zero => norm_num at hexp; omega
  | succ e =>
    refine ⟨e, ?_⟩
    rw [pow_succ, mul_comm] at hexp
    omega

omit [Fintype K] in
theorem colon_component_bound (f t M : ℕ) (ht : 2 ≤ t) (hnt : t ≤ 2 ^ f)
    (hsize : M + t = 2 * 2 ^ f + 2)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    Module.finrank K (CriticalColon.component (2 ^ f) (PlaneArcColon.lineProduct a) (t - 2)) ≤ t - 1 := by
  have hM : M = 2 * 2 ^ f - (t - 2) := by omega
  subst M
  have h := PlaneArcColon.critical_colon_bound_of_plane_arc f (t - 2) (by omega) (by omega) a ha
  omega

theorem data_colon_component_bound (D : PlaneData K) (ht : 2 ≤ D.t) :
    Module.finrank K (CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2)) ≤ D.t - 1 := by
  obtain ⟨f, hf⟩ := half_power_of_two D.exponent
  rw [hf]
  exact colon_component_bound f D.t D.M ht (by simpa only [← hf] using D.deficiency)
    (by simpa only [← hf] using D.size) D.columns D.arc

theorem quotient_capacity (D : PlaneData K) :
    Module.finrank K (D.heightSpace ⧸ D.shearHeights) ≤ D.t - 1 := by
  by_cases hlow : D.t ≤ 1
  · have hs : D.shearHeights = ⊤ := by
      apply top_unique
      intro h _
      exact D.low_degree_heights_are_shears hlow h
    letI : Subsingleton (D.heightSpace ⧸ D.shearHeights) :=
      Submodule.Quotient.subsingleton_iff.mpr hs
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  · exact (D.quotient_dimension_bound (by omega)).trans (data_colon_component_bound D (by omega))

theorem heightSpace_capacity (D : PlaneData K) (ht : 1 ≤ D.t) :
    Module.finrank K D.heightSpace ≤ D.t + 2 := by
  have hq := quotient_capacity D
  have hs := shearHeights_dimension D
  have hr := D.shearHeights.finrank_quotient_add_finrank
  omega

end EvenOrderMDS.ConcreteHeightBound
