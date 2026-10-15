module

public import EvenOrderMDS.AllEvenArcSharp
public import EvenOrderMDS.CodeGeneratorEquivalence

@[expose] public noncomputable section

/-!
# The sharp all-even linear-MDS-code theorem

Codes are actual submodules of K^N, dimension is actual vector-space finrank,
and minimum distance is the attained minimum literal Hamming distance. Both
upper bounds and attaining codes are constructed in the stated k-range.
-/

namespace EvenOrderMDS.AllEvenLinearMDS

open LinearMDSCode CodeGeneratorEquivalence

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

theorem code_length_le_bound {k N : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K)
    (C : Submodule K (Fin N → K)) (hdim : Module.finrank K C = k) (hMDS : IsMDS C) :
    N ≤ EndpointReduction.evenUpperBound (Fintype.card K) k := by
  obtain ⟨a, ha, _⟩ := exists_arc_generator_of_mds C hdim hMDS
  exact AllEvenArcUpperBound.arc_size_le hk hkq a ha

theorem code_length_le_explicit {k N : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K)
    (C : Submodule K (Fin N → K)) (hdim : Module.finrank K C = k)
    (hminimum : HasMinimumDistance C (N - k + 1)) :
    N ≤ if k = 3 ∨ k = Fintype.card K - 1 then Fintype.card K + 2 else Fintype.card K + 1 := by
  apply code_length_le_bound hk hkq C hdim
  simpa only [IsMDS, hdim] using hminimum

theorem exists_code_at_upper_bound {k : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    ∃ C : Submodule K (Fin (EndpointReduction.evenUpperBound (Fintype.card K) k) → K),
      Module.finrank K C = k ∧ IsMDS C := by
  obtain ⟨a, ha⟩ := AllEvenArcSharp.exists_arc_at_upper_bound hk hkq
  have hkn : k ≤ EndpointReduction.evenUpperBound (Fintype.card K) k := by
    unfold EndpointReduction.evenUpperBound
    split_ifs <;> omega
  exact ⟨rowCode a, rowCode_finrank hkn a ha, rowCode_isMDS_of_arc (by omega) hkn a ha⟩

theorem sharp_bound {k : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    (∀ N, ∀ C : Submodule K (Fin N → K), Module.finrank K C = k → IsMDS C →
      N ≤ EndpointReduction.evenUpperBound (Fintype.card K) k) ∧
    ∃ C : Submodule K (Fin (EndpointReduction.evenUpperBound (Fintype.card K) k) → K),
      Module.finrank K C = k ∧ IsMDS C := by
  exact ⟨fun _ C hdim hMDS => code_length_le_bound hk hkq C hdim hMDS,
    exists_code_at_upper_bound hk hkq⟩

theorem sharp_bound_explicit {k : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    let B := if k = 3 ∨ k = Fintype.card K - 1 then Fintype.card K + 2 else Fintype.card K + 1
    (∀ N, ∀ C : Submodule K (Fin N → K), Module.finrank K C = k →
      HasMinimumDistance C (N - k + 1) → N ≤ B) ∧
    ∃ C : Submodule K (Fin B → K), Module.finrank K C = k ∧ HasMinimumDistance C (B - k + 1) := by
  constructor
  · exact fun _ C hdim hmin => code_length_le_explicit hk hkq C hdim hmin
  · obtain ⟨C, hdim, hMDS⟩ := exists_code_at_upper_bound hk hkq
    rw [IsMDS, hdim] at hMDS
    exact ⟨C, hdim, hMDS⟩

def IsMaximumLength (K : Type*) [Field K] (k L : ℕ) : Prop :=
  (∃ C : Submodule K (Fin L → K), Module.finrank K C = k ∧ IsMDS C) ∧
    ∀ N, ∀ C : Submodule K (Fin N → K), Module.finrank K C = k → IsMDS C → N ≤ L

theorem isMaximumLength_iff {k L : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    IsMaximumLength K k L ↔ L = EndpointReduction.evenUpperBound (Fintype.card K) k := by
  constructor
  · rintro ⟨⟨C, hdim, hMDS⟩, hmax⟩
    have hle := code_length_le_bound hk hkq C hdim hMDS
    obtain ⟨D, hDdim, hDMDS⟩ := exists_code_at_upper_bound hk hkq
    exact Nat.le_antisymm hle (hmax _ D hDdim hDMDS)
  · rintro rfl
    exact ⟨exists_code_at_upper_bound hk hkq,
      fun _ C hdim hMDS => code_length_le_bound hk hkq C hdim hMDS⟩

omit [CharP K 2] in
theorem maximum_length_of_even_card {k : ℕ} (heven : Fintype.card K % 2 = 0)
    (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    IsMaximumLength K k
      (if k = 3 ∨ k = Fintype.card K - 1 then Fintype.card K + 2 else Fintype.card K + 1) := by
  letI : CharP K 2 := ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr heven)
  exact (isMaximumLength_iff hk hkq).mpr rfl

end EvenOrderMDS.AllEvenLinearMDS
