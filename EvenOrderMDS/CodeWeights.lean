module

public import EvenOrderMDS.ArcFamilies
public import Mathlib.Data.Fintype.EquivFin

@[expose] public noncomputable section

/-! Literal Hamming weights, zero coordinates and finite information sets. -/

namespace EvenOrderMDS.CodeWeights

variable {K : Type*} [Field K]

noncomputable def support {N : ℕ} (v : Fin N → K) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => v i ≠ 0)

noncomputable def weight {N : ℕ} (v : Fin N → K) : ℕ := (support v).card

noncomputable def zeroCoordinates {N : ℕ} (v : Fin N → K) : Finset (Fin N) := (support v)ᶜ

noncomputable def distance {N : ℕ} (v w : Fin N → K) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => v i ≠ w i)).card

theorem mem_support {N : ℕ} (v : Fin N → K) (i : Fin N) : i ∈ support v ↔ v i ≠ 0 := by
  classical
  simp [support]

theorem mem_zeroCoordinates {N : ℕ} (v : Fin N → K) (i : Fin N) : i ∈ zeroCoordinates v ↔ v i = 0 := by
  classical
  simp [zeroCoordinates, mem_support]

theorem weight_le_length {N : ℕ} (v : Fin N → K) : weight v ≤ N := by
  have h := Finset.card_le_card (Finset.subset_univ (support v))
  simpa only [weight, Finset.card_univ, Fintype.card_fin] using h

theorem zeroCoordinates_card {N : ℕ} (v : Fin N → K) : (zeroCoordinates v).card = N - weight v := by
  classical
  simp [zeroCoordinates, Finset.card_compl, weight]

theorem weight_sub_eq_distance {N : ℕ} (v w : Fin N → K) : weight (v - w) = distance v w := by
  classical
  simp [weight, support, distance, sub_eq_zero]

theorem weight_le_of_selected_zero {N r : ℕ} (v : Fin N → K) (f : Fin r ↪ Fin N)
    (hzero : ∀ i, v (f i) = 0) : weight v ≤ N - r := by
  classical
  have hsub : Finset.univ.map f ⊆ zeroCoordinates v := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact (mem_zeroCoordinates v (f i)).mpr (hzero i)
  have hcard : r ≤ (zeroCoordinates v).card := by simpa using Finset.card_le_card hsub
  rw [zeroCoordinates_card] at hcard
  have hw := weight_le_length v
  omega

theorem exists_selected_zero_of_weight_le {N k : ℕ} (hkn : k ≤ N) (v : Fin N → K)
    (hv : weight v ≤ N - k) : ∃ f : Fin k ↪ Fin N, ∀ i, v (f i) = 0 := by
  classical
  have hcard : k ≤ (zeroCoordinates v).card := by rw [zeroCoordinates_card]; omega
  obtain ⟨E, hE, hcardE⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin k ≃ E := (Finset.equivFinOfCardEq hcardE).symm
  let f : Fin k ↪ Fin N := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨f, ?_⟩
  intro i
  exact (mem_zeroCoordinates v (f i)).mp (hE (e i).property)

end EvenOrderMDS.CodeWeights
