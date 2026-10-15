module

public import EvenOrderMDS.ParentCoordinateRank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public noncomputable section

/-! An arbitrary literal parent is put into one common simultaneous coordinate system. -/

namespace EvenOrderMDS.ParentNormalization

open Module FiniteDimensional ArcFamilies ParentCoordinateProjections ParentCoordinateContractions ParentCoordinateRank

variable {K : Type*} [Field K]

theorem exists_normalized_parent {t M : ℕ} (hM : t + 3 ≤ M)
    (a : Fin t ⊕ Fin M → Fin (t + 3) → K) (ha : IsArcOn (K := K) (t + 3) a) :
    ∃ v : Fin M → Space K t, IsArcOn (K := K) (t + 3) (parent v) := by
  let selected : (Fin 3 ⊕ Fin t) ↪ (Fin t ⊕ Fin M) :=
    ((Fin.castLEEmb (by omega : 3 ≤ M)).sumMap (Function.Embedding.refl (Fin t))).trans
      (Equiv.sumComm (Fin M) (Fin t)).toEmbedding
  have hlin := independent_of_embedding ha
    (show Fintype.card (Fin 3 ⊕ Fin t) = t + 3 by simp; omega) selected
  let b : Basis (Fin 3 ⊕ Fin t) K (Fin (t + 3) → K) :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by simp; omega)
  have hb (r : Fin 3 ⊕ Fin t) : b r = a (selected r) := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin (by simp; omega)) r
  have hcenter (j : Fin t) : b.equivFun (a (Sum.inl j)) = center j := by
    have hbj : b (Sum.inr j) = a (Sum.inl j) := hb (Sum.inr j)
    rw [← hbj]
    funext r
    rw [Basis.equivFun_self]
    simp [center, Pi.single_apply, eq_comm]
  let v := fun i : Fin M => b.equivFun (a (Sum.inr i))
  refine ⟨v, ?_⟩
  have hmap := ArcFamilies.map_of_injective ha b.equivFun.toLinearMap b.equivFun.injective
  convert hmap using 1
  funext i
  cases i with
  | inl j => exact (hcenter j).symm
  | inr i => rfl

theorem impossible_parent [CharP K 2] [Fintype K]
    {n t M N : ℕ} (hn : 2 ≤ n) (ht1 : 1 ≤ t) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (hM : t + 3 ≤ M) (hN : N = t + M)
    (a : Fin N → Fin (t + 3) → K) (ha : Arc.IsArc (K := K) (t + 3) a) : False := by
  subst N
  have hfamily := ArcFamilies.restrict ha (finSumFinEquiv (m := t) (n := M)).toEmbedding
  obtain ⟨v, hv⟩ := exists_normalized_parent hM _ hfamily
  exact impossible_normalized_parent hn ht1 ht hsize hcard hM v hv

theorem no_middle_rank_arc_q_plus_two [CharP K 2] [Fintype K]
    {n k : ℕ} (hn : 2 ≤ n) (hk : 4 ≤ k) (hmid : k ≤ n + 1)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin (2 * n + 2) → Fin k → K) (ha : Arc.IsArc (K := K) k a) : False := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 3 := ⟨k - 3, by omega⟩
  exact impossible_parent hn (by omega) (by omega)
    (M := 2 * n + 2 - t) (by omega) hcard (by omega) (by omega) a ha

theorem no_rank_four_arc_q_plus_two [CharP K 2] [Fintype K]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card K = 2 * n)
    (a : Fin (2 * n + 2) → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a) : False :=
  impossible_parent (t := 1) (M := 2 * n + 1) hn (by decide) (by omega)
    (by omega) hcard (by omega) (by omega) a ha

theorem no_rank_four_arc_q_plus_three [CharP K 2] [Fintype K]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card K = 2 * n)
    (a : Fin (2 * n + 3) → Fin 4 → K) (ha : Arc.IsArc (K := K) 4 a) : False := by
  let e : Fin (2 * n + 2) ↪ Fin (2 * n + 3) := Fin.castLEEmb (by omega)
  exact no_rank_four_arc_q_plus_two hn hcard (fun i => a (e i)) (Arc.restrict ha e)

end EvenOrderMDS.ParentNormalization
