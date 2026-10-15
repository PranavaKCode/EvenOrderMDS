module

public import EvenOrderMDS.ArcColumnRelations
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public noncomputable section

/-! Actual arc duality, constructed from a basis of the literal relation kernel. -/

namespace EvenOrderMDS.ArcDuality

open Module ArcColumnRelations
open scoped Matrix BigOperators

variable {K : Type*} [Field K]

noncomputable def dualColumns {k N r : ℕ} (a : Fin N → Fin k → K)
    (b : Basis (Fin r) K (LinearMap.ker (columnMap a))) : Fin N → Fin r → K :=
  fun j i => (b i).val j

theorem evaluation_basis_eq_vecMul {k N r : ℕ} (a : Fin N → Fin k → K)
    (b : Basis (Fin r) K (LinearMap.ker (columnMap a))) (f : Fin r ↪ Fin N)
    (u : Fin r → K) (j : Fin r) :
    (b.equivFun.symm u).val (f j) = (u ᵥ* (fun i j => dualColumns a b (f j) i)) j := by
  simp [Basis.equivFun_symm_apply, Matrix.vecMul, dotProduct, dualColumns, Finset.sum_apply]

theorem dualColumns_arc {k N r : ℕ} (hcount : k + r = N)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a)
    (b : Basis (Fin r) K (LinearMap.ker (columnMap a))) : Arc.IsArc (K := K) r (dualColumns a b) := by
  intro f
  let A : Matrix (Fin r) (Fin r) K := fun i j => dualColumns a b (f j) i
  have hinj : Function.Injective (fun u : Fin r → K => u ᵥ* A) := by
    intro u v huv
    apply b.equivFun.symm.injective
    apply relationEvaluation_injective hcount a ha f
    funext j
    change (b.equivFun.symm u).val (f j) = (b.equivFun.symm v).val (f j)
    rw [evaluation_basis_eq_vecMul, evaluation_basis_eq_vecMul]
    exact congrFun huv j
  have hu := Matrix.vecMul_injective_iff_isUnit.mp hinj
  exact Matrix.linearIndependent_cols_iff_isUnit.mpr hu

theorem exists_dual_arc {k N : ℕ} (hkn : k ≤ N)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) :
    ∃ b : Fin N → Fin (N - k) → K, Arc.IsArc (K := K) (N - k) b := by
  let D := LinearMap.ker (columnMap a)
  have hdim : Module.finrank K D = N - k := relationKernel_finrank hkn a ha
  let b : Basis (Fin (N - k)) K D := (Module.finBasis K D).reindex (finCongr hdim)
  exact ⟨dualColumns a b, dualColumns_arc (by omega) a ha b⟩

theorem existsArc_dual {k N : ℕ} (hkn : k ≤ N) (ha : Arc.ExistsArc K k N) :
    Arc.ExistsArc K (N - k) N := by
  obtain ⟨a, ha⟩ := ha
  exact exists_dual_arc hkn a ha

end EvenOrderMDS.ArcDuality
