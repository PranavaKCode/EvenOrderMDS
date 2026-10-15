module

public import EvenOrderMDS.LinearMDSCode
public import EvenOrderMDS.EvaluationArc
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public noncomputable section

/-! Actual full-rank generator matrices are arcs exactly when their row codes are MDS. -/

namespace EvenOrderMDS.CodeGeneratorEquivalence

open Module LinearMDSCode
open scoped Matrix BigOperators

variable {K : Type*} [Field K]

noncomputable def encode {k N : ℕ} (a : Fin N → Fin k → K) : (Fin k → K) →ₗ[K] (Fin N → K) where
  toFun s j := a j ⬝ᵥ s
  map_add' := by intro s t; funext j; simp [dotProduct_add]
  map_smul' := by intro c s; funext j; simp [dotProduct_smul]

noncomputable def rowCode {k N : ℕ} (a : Fin N → Fin k → K) : Submodule K (Fin N → K) :=
  LinearMap.range (encode a)

theorem selected_encode_injective {k N : ℕ} (a : Fin N → Fin k → K)
    (ha : Arc.IsArc (K := K) k a) (f : Fin k ↪ Fin N) :
    Function.Injective (fun s : Fin k → K => fun i => encode a s (f i)) := by
  intro s t h
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp (ha f)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  funext i
  exact congrFun h i

theorem encode_injective_of_arc {k N : ℕ} (hkn : k ≤ N) (a : Fin N → Fin k → K)
    (ha : Arc.IsArc (K := K) k a) : Function.Injective (encode a) := by
  intro s t h
  apply selected_encode_injective a ha (Fin.castLEEmb hkn)
  funext i
  exact congrFun h (Fin.castLEEmb hkn i)

theorem rowCode_finrank {k N : ℕ} (hkn : k ≤ N) (a : Fin N → Fin k → K)
    (ha : Arc.IsArc (K := K) k a) : Module.finrank K (rowCode a) = k := by
  rw [rowCode, LinearMap.finrank_range_of_inj (encode_injective_of_arc hkn a ha)]
  simp

theorem rowCode_evaluation_injective {k N : ℕ} (a : Fin N → Fin k → K)
    (ha : Arc.IsArc (K := K) k a) (f : Fin k ↪ Fin N) :
    Function.Injective (coordinateEvaluation (rowCode a) f) := by
  intro v w heq
  obtain ⟨s, hs⟩ := v.property
  obtain ⟨t, ht⟩ := w.property
  have hst : s = t := by
    apply selected_encode_injective a ha f
    funext i
    have h := congrFun heq i
    change v.val (f i) = w.val (f i) at h
    rw [← hs, ← ht] at h
    exact h
  apply Subtype.ext
  rw [← hs, ← ht, hst]

theorem rowCode_isMDS_of_arc {k N : ℕ} (hk : 1 ≤ k) (hkn : k ≤ N)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) : IsMDS (rowCode a) := by
  have hdim := rowCode_finrank hkn a ha
  unfold IsMDS
  rw [hdim]
  exact hasMinimumDistance_of_weight_bound (rowCode a) hk hdim
    (weight_bound_of_evaluation_injective hkn (rowCode a) (rowCode_evaluation_injective a ha))

noncomputable def columnsOfBasis {k N : ℕ} (C : Submodule K (Fin N → K))
    (b : Basis (Fin k) K C) : Fin N → Fin k → K := fun j i => (b i).val j

theorem encode_columnsOfBasis {k N : ℕ} (C : Submodule K (Fin N → K))
    (b : Basis (Fin k) K C) (s : Fin k → K) :
    encode (columnsOfBasis C b) s = (b.equivFun.symm s).val := by
  funext j
  simp [encode, columnsOfBasis, dotProduct, Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]

theorem rowCode_columnsOfBasis {k N : ℕ} (C : Submodule K (Fin N → K))
    (b : Basis (Fin k) K C) : rowCode (columnsOfBasis C b) = C := by
  ext v
  constructor
  · rintro ⟨s, rfl⟩
    rw [encode_columnsOfBasis]
    exact (b.equivFun.symm s).property
  · intro hv
    refine ⟨b.equivFun ⟨v, hv⟩, ?_⟩
    rw [encode_columnsOfBasis, b.equivFun.symm_apply_apply]

theorem columnsOfBasis_arc_of_mds {k N : ℕ} (C : Submodule K (Fin N → K))
    (hdim : Module.finrank K C = k) (hMDS : IsMDS C) (b : Basis (Fin k) K C) :
    Arc.IsArc (K := K) k (columnsOfBasis C b) := by
  let ev : Fin N → C →ₗ[K] K := fun j => (LinearMap.proj j).comp C.subtype
  apply EvaluationArc.isArcOn_of_evaluation_injective b ev
  intro f
  change Function.Injective (coordinateEvaluation C f)
  apply evaluation_injective_of_weight_bound C _ f
  simpa only [hdim] using hMDS.1

theorem exists_arc_generator_of_mds {k N : ℕ} (C : Submodule K (Fin N → K))
    (hdim : Module.finrank K C = k) (hMDS : IsMDS C) :
    ∃ a : Fin N → Fin k → K, Arc.IsArc (K := K) k a ∧ rowCode a = C := by
  let b : Basis (Fin k) K C := (Module.finBasis K C).reindex (finCongr hdim)
  exact ⟨columnsOfBasis C b, columnsOfBasis_arc_of_mds C hdim hMDS b, rowCode_columnsOfBasis C b⟩

theorem arc_of_full_rank_mds {k N : ℕ} (a : Fin N → Fin k → K)
    (henc : Function.Injective (encode a)) (hMDS : IsMDS (rowCode a)) : Arc.IsArc (K := K) k a := by
  have hdim : Module.finrank K (rowCode a) = k := by
    rw [rowCode, LinearMap.finrank_range_of_inj henc]
    simp
  intro f
  have heval := evaluation_injective_of_weight_bound (rowCode a)
    (by simpa only [hdim] using hMDS.1) f
  have hinj : Function.Injective (fun s : Fin k → K => fun i => encode a s (f i)) := by
    intro s t h
    apply henc
    have hsub : (⟨encode a s, LinearMap.mem_range_self _ s⟩ : rowCode a) =
        ⟨encode a t, LinearMap.mem_range_self _ t⟩ := heval h
    exact congrArg Subtype.val hsub
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)

theorem arc_iff_full_rank_mds {k N : ℕ} (hk : 1 ≤ k) (hkn : k ≤ N)
    (a : Fin N → Fin k → K) :
    Arc.IsArc (K := K) k a ↔ Function.Injective (encode a) ∧ IsMDS (rowCode a) := by
  exact ⟨fun ha => ⟨encode_injective_of_arc hkn a ha, rowCode_isMDS_of_arc hk hkn a ha⟩,
    fun h => arc_of_full_rank_mds a h.1 h.2⟩

end EvenOrderMDS.CodeGeneratorEquivalence
