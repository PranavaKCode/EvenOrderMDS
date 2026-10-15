module

public import EvenOrderMDS.CoordinateRestriction

@[expose] public noncomputable section

/-!
# Actual point embeddings dual to the constructed polynomial restrictions

Evaluation commutes with the literal restriction. Surjectivity of its degree-one
column projection proves injectivity and preservation of nonzero points.
-/

namespace EvenOrderMDS.RestrictionPoints

open LinearCoordinates CoordinateRestriction

variable {K : Type*} [Field K]

noncomputable def pullbackPoint {σ τ : Type*}
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (x : τ → K) : σ → K :=
  fun i => MvPolynomial.eval x (f (MvPolynomial.X i))

theorem eval_pullbackPoint {σ τ : Type*}
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (x : τ → K) (p : MvPolynomial σ K) :
    MvPolynomial.eval (pullbackPoint f x) p = MvPolynomial.eval x (f p) := by
  change (MvPolynomial.aeval (pullbackPoint f x)) p = ((MvPolynomial.aeval x).comp f) p
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp [pullbackPoint]

theorem pullbackPoint_zero {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (L : (σ → K) →ₗ[K] (τ → K))
    (hL : ∀ a, f (linearForm a) = linearForm (L a)) : pullbackPoint f 0 = 0 := by
  funext i
  change MvPolynomial.eval 0 (f (MvPolynomial.X i)) = 0
  rw [← linearForm_single i, hL]
  simp [linearForm_apply]

theorem pullbackPoint_injective {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (L : (σ → K) →ₗ[K] (τ → K)) (hLs : Function.Surjective L)
    (hL : ∀ a, f (linearForm a) = linearForm (L a)) : Function.Injective (pullbackPoint f) := by
  intro x y hxy
  funext j
  obtain ⟨a, ha⟩ := hLs (Pi.single j (1 : K))
  have h := congrArg (fun z => MvPolynomial.eval z (linearForm a)) hxy
  rw [eval_pullbackPoint, eval_pullbackPoint, hL, ha, linearForm_single] at h
  simpa using h

theorem restrictionPoint_injective {n : ℕ} (a : Fin (n + 1) → K)
    (p : Fin (n + 1)) (ha : a p ≠ 0) :
    Function.Injective (pullbackPoint (restrictAlong a p ha)) :=
  pullbackPoint_injective _ (StandardArcProjection.projection a p ha)
    (StandardArcProjection.projection_surjective a p ha) (restrictAlong_linearForm a p ha)

theorem restrictionPoint_zero {n : ℕ} (a : Fin (n + 1) → K)
    (p : Fin (n + 1)) (ha : a p ≠ 0) : pullbackPoint (restrictAlong a p ha) 0 = 0 :=
  pullbackPoint_zero _ (StandardArcProjection.projection a p ha) (restrictAlong_linearForm a p ha)

theorem restrictionPoint_ne_zero {n : ℕ} (a : Fin (n + 1) → K)
    (p : Fin (n + 1)) (ha : a p ≠ 0) {x : Fin n → K} (hx : x ≠ 0) :
    pullbackPoint (restrictAlong a p ha) x ≠ 0 := by
  intro h
  apply hx
  apply restrictionPoint_injective a p ha
  rw [h, restrictionPoint_zero]

theorem restrictionPoint_on_center {n : ℕ} (a : Fin (n + 1) → K)
    (p : Fin (n + 1)) (ha : a p ≠ 0) (x : Fin n → K) :
    MvPolynomial.eval (pullbackPoint (restrictAlong a p ha) x) (linearForm a) = 0 := by
  rw [eval_pullbackPoint, restrictAlong_linearForm, StandardArcProjection.projection_column_zero,
    map_zero, map_zero]

theorem restrictionPoint_evaluation {n : ℕ} (a : Fin (n + 1) → K)
    (p : Fin (n + 1)) (ha : a p ≠ 0) (x : Fin n → K) (b : Fin (n + 1) → K) :
    MvPolynomial.eval (pullbackPoint (restrictAlong a p ha) x) (linearForm b) =
      MvPolynomial.eval x (linearForm (StandardArcProjection.projection a p ha b)) := by
  rw [eval_pullbackPoint, restrictAlong_linearForm]

end EvenOrderMDS.RestrictionPoints
