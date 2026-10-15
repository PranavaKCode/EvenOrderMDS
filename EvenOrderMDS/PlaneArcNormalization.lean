module

public import EvenOrderMDS.Arc
public import EvenOrderMDS.CrossArrangement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public noncomputable section

/-!
# Literal plane arcs supply nonzero normalized line charts

The cardinality guard M≥3 is retained when extracting nonzero columns.
Normalization records its nonzero scalar for every literal column.
-/

namespace EvenOrderMDS.PlaneArcNormalization

open PlaneLineChart ChartFrobenius CrossArrangement

variable {K : Type*} [Field K]

theorem three_labels_injective {M : ℕ} (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (![i, j, k] : Fin 3 → Fin M) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

theorem arc_three_independent {M : ℕ} {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent K ![a i, a j, a k] := by
  have h := ha ⟨![i, j, k], three_labels_injective i j k hij hik hjk⟩
  convert h using 1
  funext t
  fin_cases t <;> rfl

theorem arc_column_ne_zero {M : ℕ} (hM : 3 ≤ M) {a : Fin M → Fin 3 → K}
    (ha : Arc.IsArc (K := K) 3 a) (i : Fin M) : a i ≠ 0 := by
  obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  exact (arc_three_independent ha i j k hji.symm hki.symm hkj.symm).ne_zero 0

theorem exists_chart_normalization (v : Fin 3 → K) (hv : v ≠ 0) :
    ∃ c : Chart K, ∃ u : K, u ≠ 0 ∧ v = u • normal c := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, v z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap 2 z
  let c : Chart K := ⟨σ, v (σ 0) / v z, v (σ 1) / v z⟩
  refine ⟨c, v z, hz, ?_⟩
  funext i
  obtain ⟨k, rfl⟩ := σ.surjective i
  fin_cases k <;> simp [normal, c, σ] <;> exact (mul_div_cancel₀ _ hz).symm

theorem normalized_charts_preserve_arc {M : ℕ} (a : Fin M → Fin 3 → K)
    (ha : Arc.IsArc (K := K) 3 a) (c : Fin M → Chart K) (u : Fin M → K)
    (hu : ∀ i, u i ≠ 0) (heq : ∀ i, a i = u i • normal (c i)) :
    Arc.IsArc (K := K) 3 (fun i => normal (c i)) := by
  intro f
  apply (LinearIndependent.units_smul_iff (fun j => normal (c (f j)))
    (fun j => Units.mk0 (u (f j)) (hu (f j)))).mp
  change LinearIndependent K (fun j => u (f j) • normal (c (f j)))
  simpa only [heq] using ha f

theorem generalPosition_of_normal_arc {M : ℕ} (c : Fin M → Chart K)
    (ha : Arc.IsArc (K := K) 3 (fun i => normal (c i))) : GeneralPosition c := by
  intro i j k hij hik hjk
  have hlin := arc_three_independent ha k i j hik.symm hjk.symm hij
  exact ((Matrix.isUnit_iff_isUnit_det ![normal (c k), normal (c i), normal (c j)]).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hlin)).ne_zero

theorem exists_generalPosition_charts_of_arc {M : ℕ} (hM : 3 ≤ M)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    ∃ c : Fin M → Chart K, ∃ u : Fin M → K,
      (∀ i, u i ≠ 0) ∧ (∀ i, a i = u i • normal (c i)) ∧ GeneralPosition c := by
  choose c u hu heq using fun i => exists_chart_normalization (a i) (arc_column_ne_zero hM ha i)
  exact ⟨c, u, hu, heq, generalPosition_of_normal_arc c
    (normalized_charts_preserve_arc a ha c u hu heq)⟩

end EvenOrderMDS.PlaneArcNormalization
