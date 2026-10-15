module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.ByContra
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

/-!
# Conditional arithmetic reduction of the even-field bounds

`ExistsArc` is deliberately an arbitrary predicate on rank and length. This
module checks the endpoint logic given explicit puncturing, duality, counting,
and middle-rank hypotheses. It is not the unconditional geometric theorem.
-/

namespace EvenOrderMDS.EndpointReduction

/-- The exact exceptional-rank predicate, used only under 2 ≤ k ≤ q. -/
def Exceptional (q k : ℕ) : Prop := k = 3 ∨ k = q - 1

instance (q k : ℕ) : Decidable (Exceptional q k) :=
  inferInstanceAs (Decidable (k = 3 ∨ k = q - 1))

def evenUpperBound (q k : ℕ) : ℕ :=
  if Exceptional q k then q + 2 else q + 1

/-- Numerical guards for deleting k-3 centers from a reduced critical parent. -/
theorem parent_coordinate_guards
    {q n k : ℕ} (hq : q = 2 * n) (hk : 4 ≤ k) (hhalf : 2 * k ≤ q + 2) :
    let t := k - 3
    let m := q + 2 - t
    1 ≤ t ∧ t + 2 ≤ n ∧ k + 3 ≤ m ∧ m + t = q + 2 := by
  dsimp
  omega

/-- The dual-reduced rank remains ≥2, lies in the half range, and preserves exceptions. -/
theorem reduced_rank_guards
    {q k : ℕ} (hk : 2 ≤ k) (hkq : k ≤ q) :
    let r := min k (q + 2 - k)
    2 ≤ r ∧ 2 * r ≤ q + 2 ∧ (r = 3 → Exceptional q k) := by
  dsimp
  unfold Exceptional
  omega

/--
An explicit endpoint interface. Proving that the actual arc predicate has
these properties is a separate geometric obligation.
-/
structure ArcBoundInputs (q : ℕ) (ExistsArc : ℕ → ℕ → Prop) : Prop where
  puncture : ∀ k N M, k ≤ M → M ≤ N → ExistsArc k N → ExistsArc k M
  dual : ∀ k N, k ≤ N → ExistsArc k N → ExistsArc (N - k) N
  rankTwo : ∀ N, ExistsArc 2 N → N ≤ q + 1
  rankThree : ∀ N, ExistsArc 3 N → N ≤ q + 2
  middle : ∀ k, 4 ≤ k → 2 * k ≤ q + 2 → ¬ ExistsArc k (q + 2)
  rankFourLong : 4 ≤ q → ¬ ExistsArc 4 (q + 3)

theorem nonexceptional_bound_of_arc_inputs
    {q k N : ℕ} {ExistsArc : ℕ → ℕ → Prop}
    (inputs : ArcBoundInputs q ExistsArc)
    (hk : 2 ≤ k) (hkq : k ≤ q) (hex : ¬ Exceptional q k)
    (hArc : ExistsArc k N) : N ≤ q + 1 := by
  by_contra hlarge
  have hN : q + 2 ≤ N := by omega
  have hcrit : ExistsArc k (q + 2) := inputs.puncture k N (q + 2) (by omega) hN hArc
  have hdual : ExistsArc (q + 2 - k) (q + 2) :=
    inputs.dual k (q + 2) (by omega) hcrit
  let r := min k (q + 2 - k)
  have hrArc : ExistsArc r (q + 2) := by
    dsimp [r]
    by_cases hle : k ≤ q + 2 - k
    · simpa only [min_eq_left hle] using hcrit
    · rw [min_eq_right (show q + 2 - k ≤ k by omega)]
      exact hdual
  have guards := reduced_rank_guards hk hkq
  change 2 ≤ r ∧ 2 * r ≤ q + 2 ∧ (r = 3 → Exceptional q k) at guards
  rcases guards with ⟨hr, hrhalf, hrex⟩
  by_cases hr2 : r = 2
  · rw [hr2] at hrArc
    have := inputs.rankTwo (q + 2) hrArc
    omega
  have hr3 : r ≠ 3 := fun heq => hex (hrex heq)
  exact inputs.middle r (by omega) hrhalf hrArc

theorem exceptional_bound_of_arc_inputs
    {q k N : ℕ} {ExistsArc : ℕ → ℕ → Prop}
    (inputs : ArcBoundInputs q ExistsArc)
    (hk : 2 ≤ k) (hkq : k ≤ q) (hex : Exceptional q k)
    (hArc : ExistsArc k N) : N ≤ q + 2 := by
  rcases hex with hk3 | hkq1
  · subst k
    exact inputs.rankThree N hArc
  by_cases hqsmall : q ≤ 3
  · have hk2 : k = 2 := by omega
    rw [hk2] at hArc
    have := inputs.rankTwo N hArc
    omega
  have hq4 : 4 ≤ q := by omega
  by_contra hlarge
  have hN : q + 3 ≤ N := by omega
  have hcrit := inputs.puncture k N (q + 3) (by omega) hN hArc
  have hdual := inputs.dual k (q + 3) (by omega) hcrit
  have hdualRank : q + 3 - k = 4 := by omega
  rw [hdualRank] at hdual
  exact inputs.rankFourLong hq4 hdual

/-- Complete endpoint bookkeeping, conditional on all geometric inputs above. -/
theorem even_bound_of_arc_inputs
    {q k N : ℕ} {ExistsArc : ℕ → ℕ → Prop}
    (inputs : ArcBoundInputs q ExistsArc)
    (hk : 2 ≤ k) (hkq : k ≤ q) (hArc : ExistsArc k N) :
    N ≤ evenUpperBound q k := by
  by_cases hex : Exceptional q k
  · simpa only [evenUpperBound, if_pos hex] using
      exceptional_bound_of_arc_inputs inputs hk hkq hex hArc
  · simpa only [evenUpperBound, if_neg hex] using
      nonexceptional_bound_of_arc_inputs inputs hk hkq hex hArc

end EvenOrderMDS.EndpointReduction
