module

public import EvenOrderMDS.AllEvenArcUpperBound
public import EvenOrderMDS.ExtendedReedSolomon
public import EvenOrderMDS.HyperovalConstruction

@[expose] public noncomputable section

/-! The all-even arc upper caps are attained by literal constructed arcs. -/

namespace EvenOrderMDS.AllEvenArcSharp

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

theorem exists_arc_at_upper_bound {k : ℕ} (_hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    Arc.ExistsArc K k (EndpointReduction.evenUpperBound (Fintype.card K) k) := by
  by_cases hex : EndpointReduction.Exceptional (Fintype.card K) k
  · rw [EndpointReduction.evenUpperBound, if_pos hex]
    rcases hex with h3 | hdual
    · rw [h3]
      exact HyperovalConstruction.exists_hyperoval_arc
    · rw [hdual]
      exact HyperovalConstruction.exists_dual_hyperoval_arc
  · rw [EndpointReduction.evenUpperBound, if_neg hex]
    exact ExtendedReedSolomon.exists_extended_rs_arc k (by omega)

theorem sharp_arc_bound {k : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K) :
    (∀ N, Arc.ExistsArc K k N → N ≤ EndpointReduction.evenUpperBound (Fintype.card K) k) ∧
      Arc.ExistsArc K k (EndpointReduction.evenUpperBound (Fintype.card K) k) := by
  exact ⟨fun _ ha => AllEvenArcUpperBound.existsArc_size_le hk hkq ha, exists_arc_at_upper_bound hk hkq⟩

end EvenOrderMDS.AllEvenArcSharp
