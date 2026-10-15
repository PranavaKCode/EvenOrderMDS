module

public import EvenOrderMDS.ArcDuality
public import EvenOrderMDS.ParentNormalization
public import EvenOrderMDS.EndpointReduction
public import EvenOrderMDS.SmallRankArcBounds

@[expose] public noncomputable section

/-!
# The all-even arc upper bound with all geometric inputs supplied

This theorem is about actual literal arcs over a finite characteristic-two
field. It supplies, rather than assumes, the earlier endpoint interface.
Sharp constructions and the linear-code/minimum-distance equivalence are
separate subsequent deliverables.
-/

namespace EvenOrderMDS.AllEvenArcUpperBound

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

theorem exists_half_card : ∃ n : ℕ, 1 ≤ n ∧ Fintype.card K = 2 * n := by
  obtain ⟨e, _, he⟩ := FiniteField.card K 2
  obtain ⟨d, hd⟩ : ∃ d : ℕ, e.val = d + 1 := ⟨e.val - 1, by have := e.pos; omega⟩
  refine ⟨2 ^ d, ?_, ?_⟩
  · have hp : 0 < 2 ^ d := by positivity
    omega
  · rw [he, hd, pow_succ, mul_comm]

theorem actual_arc_inputs (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card K = 2 * n) :
    EndpointReduction.ArcBoundInputs (2 * n) (Arc.ExistsArc K) where
  puncture := by
    intro k N M _ hMN hArc
    obtain ⟨a, ha⟩ := hArc
    exact ⟨fun i => a (Fin.castLEEmb hMN i), Arc.restrict ha (Fin.castLEEmb hMN)⟩
  dual := by
    intro k N hkn hArc
    exact ArcDuality.existsArc_dual hkn hArc
  rankTwo := by
    intro N hArc
    simpa only [hcard] using SmallRankArcBounds.rank_two_exists_bound hArc
  rankThree := by
    intro N hArc
    simpa only [hcard] using SmallRankArcBounds.rank_three_exists_bound hArc
  middle := by
    intro k hk hmid hArc
    obtain ⟨a, ha⟩ := hArc
    by_cases hn2 : 2 ≤ n
    · exact ParentNormalization.no_middle_rank_arc_q_plus_two hn2 hk (by omega) hcard a ha
    · omega
  rankFourLong := by
    intro hq hArc
    obtain ⟨a, ha⟩ := hArc
    exact ParentNormalization.no_rank_four_arc_q_plus_three (by omega) hcard a ha

theorem arc_size_le {k N : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) :
    N ≤ EndpointReduction.evenUpperBound (Fintype.card K) k := by
  obtain ⟨n, hn, hcard⟩ := exists_half_card (K := K)
  have h := EndpointReduction.even_bound_of_arc_inputs (actual_arc_inputs n hn hcard)
    hk (show k ≤ 2 * n by omega) (show Arc.ExistsArc K k N from ⟨a, ha⟩)
  simpa only [← hcard] using h

theorem arc_size_le_explicit {k N : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K)
    (a : Fin N → Fin k → K) (ha : Arc.IsArc (K := K) k a) :
    N ≤ if k = 3 ∨ k = Fintype.card K - 1 then Fintype.card K + 2 else Fintype.card K + 1 :=
  arc_size_le hk hkq a ha

theorem existsArc_size_le {k N : ℕ} (hk : 2 ≤ k) (hkq : k ≤ Fintype.card K)
    (ha : Arc.ExistsArc K k N) : N ≤ EndpointReduction.evenUpperBound (Fintype.card K) k := by
  obtain ⟨a, ha⟩ := ha
  exact arc_size_le hk hkq a ha

end EvenOrderMDS.AllEvenArcUpperBound
