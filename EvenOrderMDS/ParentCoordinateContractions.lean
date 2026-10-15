module

public import EvenOrderMDS.ParentCoordinateProjections
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public noncomputable section

/-! Every one-center survivor of a literal parent gives an actual lift of the same base columns. -/

namespace EvenOrderMDS.ParentCoordinateContractions

open ArcFamilies ParentCoordinateProjections

variable {K : Type*} [Field K]

def parent {t M : ℕ} (v : Fin M → Space K t) : Fin t ⊕ Fin M → Space K t := Sum.elim center v

def liftLabels {t M : ℕ} (j : Fin t) : ({l : Fin t // l ≠ j} ⊕ Option (Fin M)) ↪ (Fin t ⊕ Fin M) where
  toFun := Sum.elim (fun l => Sum.inl l.val) (fun k => k.elim (Sum.inl j) Sum.inr)
  inj' := by
    intro u v h
    rcases u with u | u <;> rcases v with v | v
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    · cases v with
      | none => exact (u.property (Sum.inl.inj h)).elim
      | some v => cases h
    · cases u with
      | none => exact (v.property (Sum.inl.inj h).symm).elim
      | some u => cases h
    · cases u <;> cases v <;> simp_all

theorem base_columns_arc {t M : ℕ} (v : Fin M → Space K t)
    (ha : IsArcOn (K := K) (t + 3) (parent v)) :
    Arc.IsArc (K := K) 3 (fun i => baseProjection t (v i)) := by
  apply contract_centers (center (K := K) (t := t)) v _ (baseProjection t) (baseProjection_kernel t)
  simpa only [parent, Fintype.card_fin] using ha

theorem lift_columns_arc {t M : ℕ} (v : Fin M → Space K t)
    (ha : IsArcOn (K := K) (t + 3) (parent v)) (j : Fin t) :
    Arc.IsArc (K := K) 4 (LiftGeometry.columns (fun i => baseProjection t (v i)) (fun i => v i (Sum.inr j))) := by
  let survivors : Option (Fin M) → Space K t := fun k => k.elim (center j) v
  have hselected : IsArcOn (K := K) (Fintype.card {l : Fin t // l ≠ j} + 4)
      (Sum.elim (fun l : {l : Fin t // l ≠ j} => center l.val) survivors) := by
    rw [other_centers_card]
    have hnum : t - 1 + 4 = t + 3 := by have := j.isLt; omega
    rw [hnum]
    convert ArcFamilies.restrict ha (liftLabels (M := M) j) using 1
    funext k
    rcases k with k | k
    · rfl
    · cases k <;> rfl
  have hc := contract_centers (fun l : {l : Fin t // l ≠ j} => center (K := K) l.val)
    survivors hselected (liftProjection j) (liftProjection_kernel j)
  have hfin := ArcFamilies.restrict hc (finSuccEquiv' (0 : Fin (M + 1))).toEmbedding
  rw [← ArcFamilies.isArcOn_fin_iff]
  convert hfin using 1
  funext k
  cases k using Fin.cases with
  | zero => simp [LiftGeometry.columns, survivors, liftProjection_center_self]
  | succ k =>
    have heq : finSuccEquiv' (0 : Fin (M + 1)) k.succ = some k := by
      simp
    simp [LiftGeometry.columns, survivors, heq, liftProjection_column]

end EvenOrderMDS.ParentCoordinateContractions
