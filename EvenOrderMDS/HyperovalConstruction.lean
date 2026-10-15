module

public import EvenOrderMDS.ArcDuality
public import EvenOrderMDS.ArcFamilies
public import Mathlib.Algebra.CharP.Two

@[expose] public noncomputable section

/-! The literal regular hyperoval and its actual dual arc. -/

namespace EvenOrderMDS.HyperovalConstruction

open scoped Matrix

variable {K : Type*} [Field K]

def column : K ⊕ Fin 2 → Fin 3 → K
  | Sum.inl a => ![1, a, a ^ 2]
  | Sum.inr i => if i = 0 then ![0, 0, 1] else ![0, 1, 0]

theorem determinant_finite (a b c : K) :
    Matrix.det ![column (Sum.inl a), column (Sum.inl b), column (Sum.inl c)] =
      (b - a) * (c - a) * (c - b) := by
  erw [Matrix.det_fin_three]
  simp [column]
  ring

theorem determinant_ne_zero [CharP K 2] (x y z : K ⊕ Fin 2)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Matrix.det ![column x, column y, column z] ≠ 0 := by
  rcases x with a | i <;> rcases y with b | j <;> rcases z with c | k
  · rw [determinant_finite]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (by simpa using hxy.symm))
      (sub_ne_zero.mpr (by simpa using hxz.symm))) (sub_ne_zero.mpr (by simpa using hyz.symm))
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals try fin_cases k
  all_goals erw [Matrix.det_fin_three]
  all_goals simp_all [column, CharTwo.sub_eq_add,
    ← CharTwo.add_sq, add_eq_zero_iff_eq_neg, CharTwo.neg_eq, ne_comm]

theorem columns_are_arc [CharP K 2] : ArcFamilies.IsArcOn (K := K) 3 (column (K := K)) := by
  intro f
  have hd := determinant_ne_zero (f 0) (f 1) (f 2)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (f.injective h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (f.injective h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (f.injective h))
  convert Matrix.linearIndependent_rows_of_det_ne_zero hd using 1
  funext i
  fin_cases i <;> rfl

theorem exists_hyperoval_arc [CharP K 2] [Fintype K] : Arc.ExistsArc K 3 (Fintype.card K + 2) := by
  have h : Arc.ExistsArc K 3 (Fintype.card (K ⊕ Fin 2)) := by
    let e := (Fintype.equivFin (K ⊕ Fin 2)).symm
    exact ⟨fun i => column (e i), ArcFamilies.restrict columns_are_arc e.toEmbedding⟩
  simpa using h

theorem exists_dual_hyperoval_arc [CharP K 2] [Fintype K] :
    Arc.ExistsArc K (Fintype.card K - 1) (Fintype.card K + 2) := by
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have h := ArcDuality.existsArc_dual (by omega : 3 ≤ Fintype.card K + 2) (exists_hyperoval_arc (K := K))
  have heq : Fintype.card K + 2 - 3 = Fintype.card K - 1 := by omega
  simpa only [heq] using h

end EvenOrderMDS.HyperovalConstruction
