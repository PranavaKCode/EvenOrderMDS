module

public import EvenOrderMDS.ArcContraction
public import Mathlib.Logic.Embedding.Basic

@[expose] public noncomputable section

/-! Finite-label-invariant arcs and contraction through any independent center family. -/

namespace EvenOrderMDS.ArcFamilies

variable {K V W ι κ : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def IsArcOn (k : ℕ) (a : ι → V) : Prop :=
  ∀ f : Fin k ↪ ι, LinearIndependent K (fun j => a (f j))

theorem isArcOn_fin_iff {k N : ℕ} (a : Fin N → V) :
    IsArcOn (K := K) k a ↔ Arc.IsArc (K := K) k a := Iff.rfl

theorem restrict {k : ℕ} {a : ι → V} (ha : IsArcOn (K := K) k a) (e : κ ↪ ι) :
    IsArcOn (K := K) k (fun i => a (e i)) := by
  intro f
  exact ha (f.trans e)

theorem map_of_injective {k : ℕ} {a : ι → V} (ha : IsArcOn (K := K) k a)
    (f : V →ₗ[K] W) (hf : Function.Injective f) : IsArcOn (K := K) k (fun i => f (a i)) := by
  intro e
  exact (ha e).map' f (LinearMap.ker_eq_bot.mpr hf)

theorem independent_of_embedding [Fintype κ] {k : ℕ} {a : ι → V}
    (ha : IsArcOn (K := K) k a) (hcard : Fintype.card κ = k) (e : κ ↪ ι) :
    LinearIndependent K (fun i => a (e i)) := by
  subst k
  have h := ha ((Fintype.equivFin κ).symm.toEmbedding.trans e)
  simpa [Function.comp_def] using h.comp (Fintype.equivFin κ) (Fintype.equivFin κ).injective

theorem independent_after_many_centers {ν : Type*} (c : κ → V) (v : ν → V)
    (f : V →ₗ[K] W) (hker : LinearMap.ker f = Submodule.span K (Set.range c))
    (hlin : LinearIndependent K (Sum.elim c v)) :
    LinearIndependent K (fun i => f (v i)) := by
  have hparts := linearIndependent_sum.mp hlin
  have hv : LinearIndependent K v := by simpa using hparts.2.1
  apply hv.map (f := f)
  rw [hker]
  simpa using hparts.2.2.symm

theorem contract_centers [Fintype κ] {k : ℕ} (c : κ → V) (v : ι → V)
    (ha : IsArcOn (K := K) (Fintype.card κ + k) (Sum.elim c v))
    (f : V →ₗ[K] W) (hker : LinearMap.ker f = Submodule.span K (Set.range c)) :
    IsArcOn (K := K) k (fun i => f (v i)) := by
  intro e
  let selected : κ ⊕ Fin k ↪ κ ⊕ ι := (Function.Embedding.refl κ).sumMap e
  have hlin := independent_of_embedding ha
    (show Fintype.card (κ ⊕ Fin k) = Fintype.card κ + k by simp) selected
  have heq : (fun i => Sum.elim c v (selected i)) = Sum.elim c (fun i => v (e i)) := by
    funext i
    cases i <;> rfl
  rw [heq] at hlin
  exact independent_after_many_centers c (fun i => v (e i)) f hker hlin

end EvenOrderMDS.ArcFamilies
