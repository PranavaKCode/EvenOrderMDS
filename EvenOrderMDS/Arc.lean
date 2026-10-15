module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public noncomputable section

/-!
# Literal-column arc predicate

The ambient space and the rank parameter are explicit. The final geometric
theorem will specialize V to Fin k → K. Restriction is genuine puncturing;
dimension, duality, and quotient contraction remain separate obligations.
-/

namespace EvenOrderMDS.Arc

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Every k distinct columns are independent. -/
def IsArc {N : ℕ} (k : ℕ) (a : Fin N → V) : Prop :=
  ∀ f : Fin k ↪ Fin N, LinearIndependent K (fun j => a (f j))

/-- Column deletion preserves every independence condition that remains meaningful. -/
theorem restrict {k N M : ℕ} {a : Fin N → V}
    (ha : IsArc (K := K) k a) (e : Fin M ↪ Fin N) :
    IsArc (K := K) k (fun i => a (e i)) := by
  intro f
  exact ha (f.trans e)

theorem reindex {k N : ℕ} {a : Fin N → V} (e : Fin N ≃ Fin N) :
    IsArc (K := K) k (fun i => a (e i)) ↔ IsArc (K := K) k a := by
  constructor
  · intro h f
    have h' := h (f.trans e.symm.toEmbedding)
    simpa using h'
  · intro h
    exact restrict h e.toEmbedding

/-- A proof-facing existence predicate with the correct ambient dimension. -/
def ExistsArc (K : Type*) [Field K] (k N : ℕ) : Prop :=
  ∃ a : Fin N → (Fin k → K), IsArc (K := K) k a

end EvenOrderMDS.Arc
