module

public import EvenOrderMDS.Arc
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Data.Fin.Embedding
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

/-! Genuine contraction of a literal arc through a proved one-dimensional kernel. -/

namespace EvenOrderMDS.ArcContraction

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem independent_after_projection {n : ℕ} {v₀ : V} {v : Fin n → V}
    (f : V →ₗ[K] W) (hker : LinearMap.ker f = Submodule.span K {v₀})
    (hv : LinearIndependent K (Fin.cons v₀ v)) :
    LinearIndependent K (fun i => f (v i)) := by
  obtain ⟨htail, hnot⟩ := linearIndependent_fin_cons.mp hv
  apply htail.map (f := f)
  rw [hker]
  exact Submodule.disjoint_span_singleton_of_notMem hnot

theorem center_embedding_injective {k N : ℕ} (i : Fin (N + 1)) (e : Fin k ↪ Fin N) :
    Function.Injective (Fin.cons i (fun j => i.succAbove (e j))) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨j, hj⟩
    exact Fin.succAbove_ne i (e j) hj
  · exact Fin.succAbove_right_injective.comp e.injective

theorem contract {k N : ℕ} {a : Fin (N + 1) → V}
    (ha : Arc.IsArc (K := K) (k + 1) a) (i : Fin (N + 1))
    (f : V →ₗ[K] W) (hker : LinearMap.ker f = Submodule.span K {a i}) :
    Arc.IsArc (K := K) k (fun j : Fin N => f (a (i.succAbove j))) := by
  intro e
  let g : Fin (k + 1) ↪ Fin (N + 1) :=
    ⟨Fin.cons i (fun j => i.succAbove (e j)), center_embedding_injective i e⟩
  have h := ha g
  have hfamily : (fun j => a (g j)) = Fin.cons (a i) (fun j => a (i.succAbove (e j))) := by
    funext j
    cases j using Fin.cases <;> rfl
  rw [hfamily] at h
  exact independent_after_projection f hker h

theorem map_of_injective {k N : ℕ} {a : Fin N → V}
    (ha : Arc.IsArc (K := K) k a) (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Arc.IsArc (K := K) k (fun i => f (a i)) := by
  intro e
  exact (ha e).map' f (LinearMap.ker_eq_bot.mpr hf)

theorem column_ne_zero_of_enough_columns {k N : ℕ} (hk : 1 ≤ k) (hkn : k ≤ N)
    {a : Fin N → V} (ha : Arc.IsArc (K := K) k a) (i : Fin N) : a i ≠ 0 := by
  cases k with
  | zero => omega
  | succ k =>
    cases N with
    | zero => exact Fin.elim0 i
    | succ N =>
      let e : Fin k ↪ Fin N := Fin.castLEEmb (by omega)
      let g : Fin (k + 1) ↪ Fin (N + 1) :=
        ⟨Fin.cons i (fun j => i.succAbove (e j)), center_embedding_injective i e⟩
      exact (ha g).ne_zero 0

end EvenOrderMDS.ArcContraction
