module

public import EvenOrderMDS.CoordinateNormalization
public import EvenOrderMDS.ArcContraction

@[expose] public noncomputable section

/-!
# Literal arc contraction in standard finite-coordinate spaces

The projection is constructed, is surjective, and has exactly the chosen
column's span as its kernel. Existence retains the enough-columns guard.
-/

namespace EvenOrderMDS.StandardArcProjection

open CoordinateNormalization

variable {K : Type*} [Field K]

noncomputable def eraseEquiv {n : ℕ} (p : Fin (n + 1)) : Fin n ≃ {i : Fin (n + 1) // i ≠ p} :=
  Equiv.ofBijective (fun j => ⟨p.succAbove j, Fin.succAbove_ne p j⟩)
    ⟨fun _ _ h => Fin.succAbove_right_injective (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq i.property
      exact ⟨j, Subtype.ext hj⟩⟩

noncomputable def projection {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0) :
    (Fin (n + 1) → K) →ₗ[K] (Fin n → K) :=
  (LinearEquiv.funCongrLeft K K (eraseEquiv p)).toLinearMap.comp (projectAway a p ha)

theorem projection_apply {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0)
    (v : Fin (n + 1) → K) (j : Fin n) :
    projection a p ha v j = normalize a p ha v (p.succAbove j) := rfl

theorem projection_surjective {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0) :
    Function.Surjective (projection a p ha) :=
  (LinearEquiv.funCongrLeft K K (eraseEquiv p)).surjective.comp (projectAway_surjective a p ha)

theorem projection_column_zero {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0) :
    projection a p ha a = 0 := by
  change LinearEquiv.funCongrLeft K K (eraseEquiv p) (projectAway a p ha a) = 0
  rw [projectAway_column_zero, map_zero]

theorem ker_projection {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0) :
    LinearMap.ker (projection a p ha) = Submodule.span K {a} := by
  have heq : LinearMap.ker (projection a p ha) = LinearMap.ker (projectAway a p ha) := by
    ext v
    change LinearEquiv.funCongrLeft K K (eraseEquiv p) (projectAway a p ha v) = 0 ↔
      projectAway a p ha v = 0
    exact (LinearEquiv.funCongrLeft K K (eraseEquiv p)).map_eq_zero_iff
  rw [heq, ker_projectAway]

theorem projected_columns_are_arc {k N : ℕ} (a : Fin (N + 1) → Fin (k + 1) → K)
    (ha : Arc.IsArc (K := K) (k + 1) a) (i : Fin (N + 1))
    (p : Fin (k + 1)) (hp : a i p ≠ 0) :
    Arc.IsArc (K := K) k (fun j : Fin N => projection (a i) p hp (a (i.succAbove j))) :=
  ArcContraction.contract ha i (projection (a i) p hp) (ker_projection (a i) p hp)

theorem exists_contracted_arc {k N : ℕ} (hkn : k + 1 ≤ N + 1)
    (a : Fin (N + 1) → Fin (k + 1) → K) (ha : Arc.IsArc (K := K) (k + 1) a)
    (i : Fin (N + 1)) : Arc.ExistsArc K k N := by
  have hne := ArcContraction.column_ne_zero_of_enough_columns (by omega) hkn ha i
  obtain ⟨p, hp⟩ : ∃ p, a i p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  exact ⟨_, projected_columns_are_arc a ha i p hp⟩

end EvenOrderMDS.StandardArcProjection
