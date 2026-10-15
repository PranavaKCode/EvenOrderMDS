module

public import EvenOrderMDS.CodeWeights
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public noncomputable section

/-!
# Actual linear codes and attained minimum Hamming distance

A code is a submodule of K^N. Minimum distance includes an attaining nonzero
word, and is proved equivalent to the minimum over distinct codeword pairs.
-/

namespace EvenOrderMDS.LinearMDSCode

open CodeWeights

variable {K : Type*} [Field K]

def HasMinimumDistance {N : ℕ} (C : Submodule K (Fin N → K)) (d : ℕ) : Prop :=
  (∀ v ∈ C, v ≠ 0 → d ≤ weight v) ∧ ∃ v ∈ C, v ≠ 0 ∧ weight v = d

def IsMDS {N : ℕ} (C : Submodule K (Fin N → K)) : Prop :=
  HasMinimumDistance C (N - Module.finrank K C + 1)

theorem hasMinimumDistance_iff_distinct_pairs {N d : ℕ} (C : Submodule K (Fin N → K)) :
    HasMinimumDistance C d ↔
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ distance x y) ∧
        ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ distance x y = d := by
  constructor
  · rintro ⟨hbound, v, hv, hv0, hdist⟩
    refine ⟨?_, v, hv, 0, C.zero_mem, hv0, ?_⟩
    · intro x hx y hy hxy
      rw [← weight_sub_eq_distance]
      exact hbound (x - y) (C.sub_mem hx hy) (sub_ne_zero.mpr hxy)
    · simpa only [← weight_sub_eq_distance, sub_zero] using hdist
  · rintro ⟨hbound, x, hx, y, hy, hxy, hdist⟩
    refine ⟨?_, x - y, C.sub_mem hx hy, sub_ne_zero.mpr hxy, ?_⟩
    · intro v hv hv0
      simpa only [← weight_sub_eq_distance, sub_zero] using hbound v hv 0 C.zero_mem hv0
    · simpa only [weight_sub_eq_distance] using hdist

def coordinateEvaluation {N k : ℕ} (C : Submodule K (Fin N → K)) (f : Fin k ↪ Fin N) :
    C →ₗ[K] (Fin k → K) where
  toFun v i := v.val (f i)
  map_add' := by intro v w; rfl
  map_smul' := by intro c v; rfl

theorem dimension_le_length {N : ℕ} (C : Submodule K (Fin N → K)) : Module.finrank K C ≤ N := by
  simpa using Submodule.finrank_le C

theorem evaluation_injective_of_weight_bound {N k : ℕ} (C : Submodule K (Fin N → K))
    (hbound : ∀ v ∈ C, v ≠ 0 → N - k + 1 ≤ weight v) (f : Fin k ↪ Fin N) :
    Function.Injective (coordinateEvaluation C f) := by
  intro v w h
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra hne
  have hlo := hbound (v.val - w.val) (C.sub_mem v.property w.property) hne
  have hup := weight_le_of_selected_zero (v.val - w.val) f (fun i => sub_eq_zero.mpr (congrFun h i))
  omega

theorem weight_bound_of_evaluation_injective {N k : ℕ} (hkn : k ≤ N)
    (C : Submodule K (Fin N → K)) (hinj : ∀ f : Fin k ↪ Fin N, Function.Injective (coordinateEvaluation C f)) :
    ∀ v ∈ C, v ≠ 0 → N - k + 1 ≤ weight v := by
  intro v hv hv0
  by_contra hsmall
  obtain ⟨f, hf⟩ := exists_selected_zero_of_weight_le hkn v (by omega)
  have heq : coordinateEvaluation C f ⟨v, hv⟩ = coordinateEvaluation C f 0 := by
    funext i
    exact hf i
  exact hv0 (congrArg Subtype.val (hinj f heq))

theorem exists_singleton_word {N k : ℕ} (C : Submodule K (Fin N → K))
    (hk : 1 ≤ k) (hdim : Module.finrank K C = k) :
    ∃ v ∈ C, v ≠ 0 ∧ weight v ≤ N - k + 1 := by
  have hkn : k ≤ N := by rw [← hdim]; exact dimension_le_length C
  let f : Fin (k - 1) ↪ Fin N := Fin.castLEEmb (by omega)
  let L := coordinateEvaluation C f
  have hnot : ¬ Function.Injective L := by
    intro hi
    have h := LinearMap.finrank_le_finrank_of_injective hi
    simp only [hdim, Module.finrank_pi, Fintype.card_fin] at h
    omega
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro h
    exact hnot (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v, hv, hv0⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  have hz (i : Fin (k - 1)) : v.val (f i) = 0 := congrFun hv i
  have hw := weight_le_of_selected_zero v.val f hz
  refine ⟨v.val, v.property, ?_, ?_⟩
  · intro hzero
    exact hv0 (Subtype.ext hzero)
  · omega

theorem hasMinimumDistance_of_weight_bound {N k : ℕ} (C : Submodule K (Fin N → K))
    (hk : 1 ≤ k) (hdim : Module.finrank K C = k)
    (hbound : ∀ v ∈ C, v ≠ 0 → N - k + 1 ≤ weight v) : HasMinimumDistance C (N - k + 1) := by
  obtain ⟨v, hv, hv0, hle⟩ := exists_singleton_word C hk hdim
  exact ⟨hbound, v, hv, hv0, Nat.le_antisymm hle (hbound v hv hv0)⟩

theorem isMDS_iff_weight_bound {N : ℕ} (C : Submodule K (Fin N → K))
    (hpos : 1 ≤ Module.finrank K C) :
    IsMDS C ↔ ∀ v ∈ C, v ≠ 0 → N - Module.finrank K C + 1 ≤ weight v := by
  exact ⟨fun h => h.1, fun h => hasMinimumDistance_of_weight_bound C hpos rfl h⟩

end EvenOrderMDS.LinearMDSCode
