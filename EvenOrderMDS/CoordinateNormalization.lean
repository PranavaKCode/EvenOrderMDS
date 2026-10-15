module

public import EvenOrderMDS.LinearCoordinates
public import Mathlib.Tactic.Ring

@[expose] public noncomputable section

/-! An explicit coordinate change and projection away from one nonzero column. -/

namespace EvenOrderMDS.CoordinateNormalization

variable {K ι : Type*} [Field K] [DecidableEq ι]

noncomputable def normalize (a : ι → K) (p : ι) (ha : a p ≠ 0) :
    (ι → K) ≃ₗ[K] (ι → K) where
  toFun v i := if i = p then v p / a p else v i - (v p / a p) * a i
  invFun w i := if i = p then w p * a p else w i + w p * a i
  left_inv v := by
    funext i
    by_cases hi : i = p <;> simp [hi, ha]
  right_inv w := by
    funext i
    by_cases hi : i = p <;> simp [hi, ha]
  map_add' v w := by
    funext i
    by_cases hi : i = p <;> simp [hi, add_div, add_mul]
    ring
  map_smul' c v := by
    funext i
    by_cases hi : i = p <;> simp [hi, div_eq_mul_inv, mul_sub] <;> ring

theorem normalize_pivot (a : ι → K) (p : ι) (ha : a p ≠ 0) (v : ι → K) :
    normalize a p ha v p = v p / a p := by simp [normalize]

theorem normalize_column (a : ι → K) (p : ι) (ha : a p ≠ 0) :
    normalize a p ha a = Pi.single p (1 : K) := by
  funext i
  by_cases hi : i = p <;> simp [normalize, hi, ha, Pi.single_apply]

def dropAt (p : ι) : (ι → K) →ₗ[K] ({i : ι // i ≠ p} → K) where
  toFun v i := v i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem dropAt_axis (p : ι) : dropAt (K := K) p (Pi.single p 1) = 0 := by
  funext i
  simp [dropAt, Ne.symm i.property]

theorem dropAt_surjective (p : ι) : Function.Surjective (dropAt (K := K) p) := by
  intro w
  refine ⟨fun i => if hi : i = p then 0 else w ⟨i, hi⟩, ?_⟩
  funext i
  simp [dropAt, i.property]

theorem ker_dropAt (p : ι) :
    LinearMap.ker (dropAt (K := K) p) = Submodule.span K {Pi.single p (1 : K)} := by
  apply le_antisymm
  · intro v hv
    have heq : v p • (Pi.single p (1 : K) : ι → K) = v := by
      funext i
      by_cases hi : i = p
      · subst i
        simp
      · have hz := congrFun hv (⟨i, hi⟩ : {i : ι // i ≠ p})
        change v i = 0 at hz
        simp [Ne.symm hi, hz]
    exact Submodule.mem_span_singleton.mpr ⟨v p, heq⟩
  · rw [Submodule.span_le]
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact dropAt_axis p

noncomputable def projectAway (a : ι → K) (p : ι) (ha : a p ≠ 0) :
    (ι → K) →ₗ[K] ({i : ι // i ≠ p} → K) :=
  (dropAt p).comp (normalize a p ha).toLinearMap

theorem projectAway_surjective (a : ι → K) (p : ι) (ha : a p ≠ 0) :
    Function.Surjective (projectAway a p ha) :=
  (dropAt_surjective p).comp (normalize a p ha).surjective

theorem projectAway_column_zero (a : ι → K) (p : ι) (ha : a p ≠ 0) :
    projectAway a p ha a = 0 := by
  change dropAt p (normalize a p ha a) = 0
  rw [normalize_column, dropAt_axis]

theorem ker_projectAway (a : ι → K) (p : ι) (ha : a p ≠ 0) :
    LinearMap.ker (projectAway a p ha) = Submodule.span K {a} := by
  apply le_antisymm
  · intro v hv
    have hmem : normalize a p ha v ∈ LinearMap.ker (dropAt p) := hv
    rw [ker_dropAt] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply (normalize a p ha).injective
    rw [map_smul, normalize_column]
    exact hc
  · rw [Submodule.span_le]
    intro v hv
    have heq : v = a := Set.mem_singleton_iff.mp hv
    subst v
    exact projectAway_column_zero a p ha

end EvenOrderMDS.CoordinateNormalization
