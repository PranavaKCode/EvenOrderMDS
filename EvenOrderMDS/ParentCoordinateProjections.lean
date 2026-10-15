module

public import EvenOrderMDS.ArcFamilies
public import EvenOrderMDS.LiftGeometry

@[expose] public noncomputable section

/-! Exact coordinate projections and kernels for a common parent-coordinate system. -/

namespace EvenOrderMDS.ParentCoordinateProjections

open scoped BigOperators

variable {K : Type*} [Field K]

abbrev Space (K : Type*) (t : ℕ) := (Fin 3 ⊕ Fin t) → K

def center {t : ℕ} (j : Fin t) : Space K t := Pi.single (Sum.inr j) 1

def baseProjection (t : ℕ) : Space K t →ₗ[K] (Fin 3 → K) where
  toFun v i := v (Sum.inl i)
  map_add' := by intro v w; rfl
  map_smul' := by intro c v; rfl

def liftProjection {t : ℕ} (j : Fin t) : Space K t →ₗ[K] (Fin 4 → K) where
  toFun v := ![v (Sum.inl 0), v (Sum.inl 1), v (Sum.inl 2), v (Sum.inr j)]
  map_add' := by intro v w; funext i; fin_cases i <;> rfl
  map_smul' := by intro c v; funext i; fin_cases i <;> rfl

theorem baseProjection_center {t : ℕ} (j : Fin t) : baseProjection t (center (K := K) j) = 0 := by
  funext i
  simp [baseProjection, center]

theorem liftProjection_center_self {t : ℕ} (j : Fin t) :
    liftProjection j (center (K := K) j) = LiftGeometry.vertical := by
  funext i
  fin_cases i <;> simp [liftProjection, center, LiftGeometry.vertical]

theorem liftProjection_center_other {t : ℕ} (j l : Fin t) (hlj : l ≠ j) :
    liftProjection j (center (K := K) l) = 0 := by
  funext i
  fin_cases i <;> simp [liftProjection, center, hlj]

theorem liftProjection_column {t : ℕ} (j : Fin t) (v : Space K t) :
    liftProjection j v = LiftGeometry.column (baseProjection t v) (v (Sum.inr j)) := rfl

theorem sum_centers_of_base_zero {t : ℕ} (v : Space K t) (hv : baseProjection t v = 0) :
    (∑ j, v (Sum.inr j) • center j) = v := by
  have hz (i : Fin 3) : v (Sum.inl i) = 0 := congrFun hv i
  funext i
  cases i with
  | inl i => simp [center, hz]
  | inr j => simp [center, Pi.single_apply]

theorem baseProjection_kernel (t : ℕ) :
    LinearMap.ker (baseProjection (K := K) t) = Submodule.span K (Set.range center) := by
  classical
  apply le_antisymm
  · intro v hv
    rw [← sum_centers_of_base_zero v hv]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    exact baseProjection_center j

theorem liftProjection_kernel {t : ℕ} (j : Fin t) :
    LinearMap.ker (liftProjection (K := K) j) =
      Submodule.span K (Set.range (fun l : {l : Fin t // l ≠ j} => center l.val)) := by
  classical
  apply le_antisymm
  · intro v hv
    have hbase : baseProjection t v = 0 := by
      funext i
      fin_cases i
      · exact congrFun hv 0
      · exact congrFun hv 1
      · exact congrFun hv 2
    have hz : v (Sum.inr j) = 0 := congrFun hv 3
    have hsum := Finset.sum_erase_add Finset.univ (fun l => v (Sum.inr l) • center (K := K) l) (Finset.mem_univ j)
    try dsimp only at hsum
    rw [hz, zero_smul, add_zero, sum_centers_of_base_zero v hbase] at hsum
    have hsub : (∑ l : {l : Fin t // l ≠ j}, v (Sum.inr l.val) • center l.val) = v := by
      rw [← Finset.sum_subtype (p := fun l : Fin t => l ≠ j) (Finset.univ.erase j)
        (by simp) (fun l => v (Sum.inr l) • center (K := K) l)]
      exact hsum
    rw [← hsub]
    apply Submodule.sum_mem
    intro l _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))
  · apply Submodule.span_le.mpr
    rintro v ⟨l, rfl⟩
    exact liftProjection_center_other j l.val l.property

theorem other_centers_card {t : ℕ} (j : Fin t) : Fintype.card {l : Fin t // l ≠ j} = t - 1 := by
  rw [Fintype.card_subtype_compl]
  simp

end EvenOrderMDS.ParentCoordinateProjections
