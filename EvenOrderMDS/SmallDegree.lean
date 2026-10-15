module

public import Lean

@[expose] public noncomputable section

/-!
# Small-degree branches with no Gorenstein premises

These are separate entry points for the potentially zero d=0 quotient and
the elementary d=1 argument. The full Hilbert-sequence interface is not needed.
-/

namespace EvenOrderMDS.SmallDegree

theorem critical_degree_zero {κ h₀ : Nat} (hdim : κ + h₀ = 1) : κ ≤ 1 := by
  omega

theorem critical_degree_one {κ h₁ : Nat} (hdim : κ + h₁ = 3) (hpos : 1 ≤ h₁) :
    κ ≤ 2 := by
  omega

theorem bound_of_length_below_rank {N k q : Nat} (hNk : N < k) (hkq : k ≤ q) :
    N ≤ q + 1 := by
  omega

end EvenOrderMDS.SmallDegree
