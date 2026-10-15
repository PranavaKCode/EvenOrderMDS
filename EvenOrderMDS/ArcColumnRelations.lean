module

public import EvenOrderMDS.ArcFamilies
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public noncomputable section

/-! The literal column relation kernel and its coordinate-information property. -/

namespace EvenOrderMDS.ArcColumnRelations

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def columnMap {k N : ℕ} (a : Fin N → Fin k → K) :
    (Fin N → K) →ₗ[K] (Fin k → K) where
  toFun x := ∑ j, x j • a j
  map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c x; simp [smul_smul, Finset.smul_sum]

theorem columnMap_single {k N : ℕ} (a : Fin N → Fin k → K) (j : Fin N) (c : K) :
    columnMap a (Pi.single j c) = c • a j := by
  simp [columnMap, Pi.single_apply]

theorem columnMap_surjective {k N : ℕ} (hkn : k ≤ N)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) : Function.Surjective (columnMap a) := by
  by_cases hk : k = 0
  · subst k
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let e : Fin k ↪ Fin N := Fin.castLEEmb hkn
  have hlin := ha e
  have hspan : Submodule.span K (Set.range (fun i => a (e i))) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank (by simp)
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  exact ⟨Pi.single (e i) 1, by simp [columnMap_single]⟩

theorem relationKernel_finrank {k N : ℕ} (hkn : k ≤ N)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) :
    Module.finrank K (LinearMap.ker (columnMap a)) = N - k := by
  have h := (columnMap a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (columnMap_surjective hkn a ha)] at h
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
  omega

theorem relation_zero_of_selected_zero {k r N : ℕ} (hcount : k + r = N)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) (f : Fin r ↪ Fin N)
    (x : Fin N → K) (hx : columnMap a x = 0) (hzero : ∀ i, x (f i) = 0) : x = 0 := by
  classical
  let S : Finset (Fin N) := Finset.univ.map f
  let T : Finset (Fin N) := Sᶜ
  have hcard : T.card = k := by
    simp only [T, Finset.card_compl, S, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    omega
  have hlin : LinearIndependent K (fun j : T => a j.val) :=
    ArcFamilies.independent_of_embedding ha (by simpa using hcard) ⟨Subtype.val, Subtype.val_injective⟩
  have hout (j : Fin N) (hj : j ∉ T) : x j = 0 := by
    have hjS : j ∈ S := by simpa [T] using hj
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hjS
    rw [← hi]
    exact hzero i
  have hsum : (∑ j ∈ T, x j • a j) = 0 := by
    calc
      _ = ∑ j, x j • a j := Finset.sum_subset (Finset.subset_univ T) (fun j _ hj => by rw [hout j hj, zero_smul])
      _ = 0 := hx
  have hsubsum : (∑ j : T, x j.val • a j.val) = 0 := by
    rw [← Finset.sum_subtype (p := fun j : Fin N => j ∈ T) T (by simp) (fun j => x j • a j)]
    exact hsum
  funext j
  by_cases hj : j ∈ T
  · exact linearIndependent_iff'.mp hlin Finset.univ (fun j : T => x j.val) hsubsum ⟨j, hj⟩ (Finset.mem_univ _)
  · exact hout j hj

def relationEvaluation {k N r : ℕ} (a : Fin N → Fin k → K) (f : Fin r ↪ Fin N) :
    LinearMap.ker (columnMap a) →ₗ[K] (Fin r → K) where
  toFun x i := x.val (f i)
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

theorem relationEvaluation_injective {k r N : ℕ} (hcount : k + r = N)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) (f : Fin r ↪ Fin N) :
    Function.Injective (relationEvaluation a f) := by
  intro x y heq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply relation_zero_of_selected_zero hcount a ha f (x.val - y.val)
  · rw [map_sub]
    have hx0 : columnMap a x.val = 0 := x.property
    have hy0 : columnMap a y.val = 0 := y.property
    rw [hx0, hy0, sub_self]
  · intro i
    exact sub_eq_zero.mpr (congrFun heq i)

end EvenOrderMDS.ArcColumnRelations
