module

public import EvenOrderMDS.PolynomialObstruction
public import EvenOrderMDS.ColonDivisionMap

@[expose] public noncomputable section

/-!
# Concrete compatible heights inject modulo literal shears into the colon component

Every field of this data structure is explicit mathematical input. Envelope
existence is already constructed upstream; no shear-kernel or divisibility
premise is stored in the structure.
-/

namespace EvenOrderMDS.ConcreteShearInjection

open CompatibleSpace SquareRootCoefficients ShearPolynomials
open scoped Matrix BigOperators

variable (K : Type*) [Field K] [CharP K 2] [Fintype K]

structure PlaneData where
  n : ℕ
  t : ℕ
  M : ℕ
  e : ℕ
  positive : 1 ≤ n
  deficiency : t ≤ n
  size : M + t = 2 * n + 2
  exponent : 2 ^ e = 2 * n
  card : Fintype.card K = 2 ^ e
  columns : Fin M → Fin 3 → K
  arc : Arc.IsArc (K := K) 3 columns
  envelope : MvPolynomial (Fin 3) K
  degree : envelope.IsHomogeneous t
  normalized : NormalizedPlaneHighest.HasNormalizedValues columns envelope

variable {K}

omit [CharP K 2] in
theorem PlaneData.enough_columns (D : PlaneData K) : 3 ≤ D.M := by
  have := D.positive
  have := D.deficiency
  have := D.size
  omega

noncomputable abbrev PlaneData.compatible (D : PlaneData K) := pairs D.t D.columns D.envelope

noncomputable def PlaneData.obstruction (D : PlaneData K) :
    D.compatible →ₛₗ[(squareRoot K).toRingHom] MvPolynomial (Fin 3) K :=
  PolynomialObstruction.obstructionMap (by have := D.enough_columns; omega) D.size D.columns D.envelope D.degree

noncomputable def rawShearMap {M : ℕ} (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    (Fin 3 → K) →ₗ[K] ((Fin M → K) × MvPolynomial (Fin 3) K) where
  toFun s := (heights a s, derivative s F)
  map_add' := by
    intro s v
    apply Prod.ext
    · funext i
      simp [heights, dotProduct_add]
    · simp [derivative, add_smul, add_assoc, add_left_comm]
  map_smul' := by
    intro c s
    apply Prod.ext
    · funext i
      simp [heights, dotProduct_smul]
    · simp [derivative, smul_smul, smul_add]

noncomputable def PlaneData.shearMap (D : PlaneData K) : (Fin 3 → K) →ₗ[K] D.compatible :=
  (rawShearMap D.columns D.envelope).codRestrict D.compatible (fun s => by
    obtain ⟨S, _, hCF⟩ := NormalizedPlaneHighest.highest_form_of_normalized_plane_envelope
      D.n D.t D.M D.positive D.deficiency D.size (D.card.trans D.exponent)
      D.columns D.arc D.envelope D.degree D.normalized
    exact shear_mem_pairs D.columns D.envelope D.degree S hCF s)

theorem PlaneData.obstruction_kernel (D : PlaneData K) :
    LinearMap.ker D.obstruction = LinearMap.range D.shearMap := by
  ext p
  change D.obstruction p = 0 ↔ ∃ s, D.shearMap s = p
  unfold PlaneData.obstruction
  rw [PolynomialObstruction.obstruction_zero_iff_shear D.positive D.deficiency D.size
    (D.card.trans D.exponent) D.columns D.arc D.envelope D.degree D.normalized]
  constructor
  · rintro ⟨s, hs, hQ⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact Prod.ext hs.symm hQ.symm
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl, rfl⟩

noncomputable def PlaneData.colonMap (D : PlaneData K) (ht : 2 ≤ D.t) :
    D.compatible →ₛₗ[(squareRoot K).toRingHom]
      CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2) :=
  ColonDivisionMap.divisionMap (PlaneArcColon.lineProduct D.columns)
    (PlaneArcColon.lineProduct_homogeneous D.columns)
    (PlaneCofactorGeometry.lineProduct_ne_zero D.enough_columns D.arc)
    (squareRoot K) D.obstruction
    (fun p => by
      have h := PolynomialObstruction.obstructionMap_homogeneous
        (by have := D.enough_columns; omega) D.size D.columns D.envelope D.degree p
      have hi : D.M + (D.t - 2) = 2 * D.n := by have := D.size; omega
      simpa only [hi, PlaneData.obstruction] using h)
    (fun p => PolynomialObstruction.obstructionMap_mem_powerIdeal
      (by have := D.enough_columns; omega) D.size D.columns D.envelope D.degree p)
    (fun p => PolynomialObstruction.oldProduct_dvd_obstructionMap D.positive D.deficiency D.size
      D.exponent D.card D.columns D.arc D.envelope D.degree D.normalized p)

theorem PlaneData.colonMap_eq_zero_iff (D : PlaneData K) (ht : 2 ≤ D.t) (p : D.compatible) :
    D.colonMap ht p = 0 ↔ D.obstruction p = 0 :=
  ColonDivisionMap.divisionMap_eq_zero_iff _ _ _ _ _ _ _ _ _

theorem PlaneData.colonMap_kernel (D : PlaneData K) (ht : 2 ≤ D.t) :
    LinearMap.ker (D.colonMap ht) = LinearMap.range D.shearMap := by
  rw [← D.obstruction_kernel]
  ext p
  exact D.colonMap_eq_zero_iff ht p

noncomputable def PlaneData.heightSpace (D : PlaneData K) : Submodule K (Fin D.M → K) :=
  CommonHeight.heightSpace D.compatible

theorem PlaneData.projection_injective (D : PlaneData K) :
    Function.Injective (CommonHeight.heightProjection D.compatible) :=
  heightProjection_injective D.positive D.deficiency D.size D.columns D.arc D.envelope

noncomputable def PlaneData.shearHeights (D : PlaneData K) : Submodule K D.heightSpace :=
  CommonHeight.shearHeights D.compatible D.projection_injective (LinearMap.range D.shearMap)

theorem PlaneData.mem_shearHeights (D : PlaneData K) (h : D.heightSpace) :
    h ∈ D.shearHeights ↔ ∃ s : Fin 3 → K, h.val = heights D.columns s := by
  constructor
  · rintro ⟨p, ⟨s, rfl⟩, hp⟩
    refine ⟨s, ?_⟩
    exact (congrArg Subtype.val hp).symm
  · rintro ⟨s, hs⟩
    refine ⟨D.shearMap s, ⟨s, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hs.symm

noncomputable def PlaneData.heightObstruction (D : PlaneData K) (ht : 2 ≤ D.t) :
    D.heightSpace →ₛₗ[(squareRoot K).toRingHom]
      CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2) :=
  CommonHeight.obstructionOnHeights (J := CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2)) D.compatible D.projection_injective (squareRoot K) (D.colonMap ht)

theorem PlaneData.shearHeights_eq_heightKernel (D : PlaneData K) (ht : 2 ≤ D.t) :
    D.shearHeights = LinearMap.ker (D.heightObstruction ht) := by
  exact CommonHeight.shearHeights_eq_kernel (J := CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2)) D.compatible D.projection_injective (squareRoot K)
    (D.colonMap ht) (LinearMap.range D.shearMap) (D.colonMap_kernel ht).symm

noncomputable def PlaneData.quotientInjection (D : PlaneData K) (ht : 2 ≤ D.t) :
    (D.heightSpace ⧸ D.shearHeights) →ₛₗ[(squareRoot K).toRingHom]
      CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2) :=
  SemilinearQuotient.quotientMap (W := CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2)) (squareRoot K) (D.heightObstruction ht) D.shearHeights
    (D.shearHeights_eq_heightKernel ht)

theorem PlaneData.quotientInjection_injective (D : PlaneData K) (ht : 2 ≤ D.t) :
    Function.Injective (D.quotientInjection ht) := by
  intro x y
  refine Submodule.Quotient.induction_on D.shearHeights x (fun u => ?_)
  refine Submodule.Quotient.induction_on D.shearHeights y (fun v => ?_)
  intro huv
  apply (Submodule.Quotient.eq D.shearHeights).mpr
  rw [D.shearHeights_eq_heightKernel ht]
  change D.heightObstruction ht (u - v) = 0
  rw [map_sub, sub_eq_zero]
  exact huv

theorem PlaneData.quotient_dimension_bound (D : PlaneData K) (ht : 2 ≤ D.t) :
    Module.finrank K (D.heightSpace ⧸ D.shearHeights) ≤
      Module.finrank K (CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2)) := by
  exact SemilinearQuotient.finrank_le_of_injective_semilinear (W := CriticalColon.component D.n (PlaneArcColon.lineProduct D.columns) (D.t - 2)) (squareRoot K)
    (D.quotientInjection ht) (D.quotientInjection_injective ht)

theorem PlaneData.low_degree_heights_are_shears (D : PlaneData K) (ht : D.t ≤ 1) (h : D.heightSpace) :
    h ∈ D.shearHeights := by
  obtain ⟨p, hp⟩ := h.property
  have hz := PolynomialObstruction.obstruction_zero_in_low_degree D.positive ht D.size D.exponent D.card
    D.columns D.arc D.envelope D.degree D.normalized p
  have hmem : p ∈ LinearMap.range D.shearMap := by
    rw [← D.obstruction_kernel]
    exact hz
  obtain ⟨s, hs⟩ := hmem
  apply (D.mem_shearHeights h).mpr
  exact ⟨s, by rw [← hp, ← hs]; rfl⟩

end EvenOrderMDS.ConcreteShearInjection
