module

public import EvenOrderMDS.ParentCoordinateContractions
public import EvenOrderMDS.CommonHeightCapacity

@[expose] public noncomputable section

/-! Remaining parent columns supply genuinely independent common-height rows. -/

namespace EvenOrderMDS.ParentCoordinateRank

open ArcFamilies ParentCoordinateProjections ParentCoordinateContractions

variable {K : Type*} [Field K]

def rows {t M : ℕ} (v : Fin M → Space K t) : (Fin 3 ⊕ Fin t) → Fin M → K := fun r i => v i r

theorem remaining_rows_independent {t M : ℕ} (hM : t + 3 ≤ M)
    (v : Fin M → Space K t) (ha : IsArcOn (K := K) (t + 3) (parent v)) :
    LinearIndependent K (rows v) := by
  let select : (Fin 3 ⊕ Fin t) ↪ Fin M :=
    (Fintype.equivFin (Fin 3 ⊕ Fin t)).toEmbedding.trans (Fin.castLEEmb (by simp; omega))
  have hrest : IsArcOn (K := K) (t + 3) v :=
    ArcFamilies.restrict ha ⟨Sum.inr, Sum.inr_injective⟩
  have hlin := independent_of_embedding hrest
    (show Fintype.card (Fin 3 ⊕ Fin t) = t + 3 by simp; omega) select
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hlin
  have hcols := Matrix.linearIndependent_cols_iff_isUnit.mpr hu
  let restrictRows : (Fin M → K) →ₗ[K] ((Fin 3 ⊕ Fin t) → K) :=
    { toFun := fun w i => w (select i)
      map_add' := by intro w z; rfl
      map_smul' := by intro c w; rfl }
  exact LinearIndependent.of_comp restrictRows hcols

theorem impossible_normalized_parent [CharP K 2] [Fintype K]
    {n t M : ℕ} (hn : 2 ≤ n) (ht1 : 1 ≤ t) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (hM : t + 3 ≤ M) (v : Fin M → Space K t)
    (ha : IsArcOn (K := K) (t + 3) (parent v)) : False := by
  let a := fun i => baseProjection t (v i)
  have ha3 := base_columns_arc v ha
  obtain ⟨H, hcap, hshear, hlifts⟩ := CommonHeightCapacity.exists_bounded_common_height_space
    hn ht1 ht hsize hcard a ha3
  have hm (r : Fin 3 ⊕ Fin t) : rows v r ∈ H := by
    cases r with
    | inl r =>
      have heq : rows v (Sum.inl r) = ShearPolynomials.heights a (Pi.single r 1) := by
        funext i
        simp [rows, ShearPolynomials.heights, a, baseProjection]
      rw [heq]
      exact hshear _
    | inr j => exact hlifts _ (lift_columns_arc v ha j)
  have hlin : LinearIndependent K (fun r : Fin 3 ⊕ Fin t => (⟨rows v r, hm r⟩ : H)) :=
    LinearIndependent.of_comp H.subtype (remaining_rows_independent hM v ha)
  have hlow := hlin.fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_fin] at hlow
  omega

end EvenOrderMDS.ParentCoordinateRank
