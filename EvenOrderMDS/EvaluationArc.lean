module

public import EvenOrderMDS.ArcFamilies
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public noncomputable section

/-! A basis and injective coordinate evaluations produce literal arc columns. -/

namespace EvenOrderMDS.EvaluationArc

open Module
open scoped Matrix BigOperators

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def columns {k : ℕ} (b : Basis (Fin k) K V) (ev : ι → V →ₗ[K] K) : ι → Fin k → K :=
  fun j i => ev j (b i)

theorem evaluation_basis_eq_vecMul {k : ℕ} (b : Basis (Fin k) K V) (ev : ι → V →ₗ[K] K)
    (f : Fin k ↪ ι) (u : Fin k → K) (j : Fin k) :
    ev (f j) (b.equivFun.symm u) = (u ᵥ* (fun i j => columns b ev (f j) i)) j := by
  simp [Basis.equivFun_symm_apply, Matrix.vecMul, dotProduct, columns]

theorem isArcOn_of_evaluation_injective {k : ℕ} (b : Basis (Fin k) K V) (ev : ι → V →ₗ[K] K)
    (hinj : ∀ f : Fin k ↪ ι, Function.Injective (fun v : V => fun j => ev (f j) v)) :
    ArcFamilies.IsArcOn (K := K) k (columns b ev) := by
  intro f
  let A : Matrix (Fin k) (Fin k) K := fun i j => columns b ev (f j) i
  have hA : Function.Injective (fun u : Fin k → K => u ᵥ* A) := by
    intro u v huv
    apply b.equivFun.symm.injective
    apply hinj f
    funext j
    dsimp only
    rw [evaluation_basis_eq_vecMul, evaluation_basis_eq_vecMul]
    exact congrFun huv j
  exact Matrix.linearIndependent_cols_iff_isUnit.mpr (Matrix.vecMul_injective_iff_isUnit.mp hA)

end EvenOrderMDS.EvaluationArc
