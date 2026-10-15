module

public import EvenOrderMDS.StandardArcProjection
public import EvenOrderMDS.ChartGeometry

@[expose] public noncomputable section

/-!
# Concrete rank-two and rank-three arc bounds

Projective normalization embeds a rank-two arc into K plus one infinity point.
Actual contraction then gives the plane-arc bound. Both work in every field
of finite cardinality and include the below-rank vacuous cases honestly.
-/

namespace EvenOrderMDS.SmallRankArcBounds

variable {K : Type*} [Field K]

theorem rank_two_minor_ne_zero {N : ℕ} (a : Fin N → Fin 2 → K)
    (ha : Arc.IsArc (K := K) 2 a) (i j : Fin N) (hij : i ≠ j) :
    a i 0 * a j 1 ≠ a j 0 * a i 1 := by
  let e : Fin 2 ↪ Fin N := ⟨![i, j], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all⟩
  have hlin : LinearIndependent K ![a i, a j] := by
    convert ha e using 1
    funext t
    fin_cases t <;> rfl
  have hne : a i ≠ 0 := hlin.ne_zero 0
  have hv : a i 0 ≠ 0 ∨ a i 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    funext t
    fin_cases t <;> simp [h.1, h.2]
  intro hdet
  obtain ⟨s, hs⟩ := ChartGeometry.proportional_of_binary_det_zero (a i) (a j) hv hdet
  exact (LinearIndependent.pair_iff' hne).mp hlin s hs.symm

noncomputable def pointCode (v : Fin 2 → K) : Option K := by
  classical
  exact if v 1 = 0 then none else some (v 0 / v 1)

theorem pointCode_injective_of_minors {ι : Type*} (a : ι → Fin 2 → K)
    (hminor : ∀ i j, i ≠ j → a i 0 * a j 1 ≠ a j 0 * a i 1) :
    Function.Injective (fun i => pointCode (a i)) := by
  classical
  intro i j heq
  by_contra hij
  by_cases hi : a i 1 = 0
  · by_cases hj : a j 1 = 0
    · exact hminor i j hij (by simp [hi, hj])
    · simp [pointCode, hi, hj] at heq
  · by_cases hj : a j 1 = 0
    · simp [pointCode, hi, hj] at heq
    · simp only [pointCode, if_neg hi, if_neg hj, Option.some.injEq] at heq
      exact hminor i j hij ((div_eq_div_iff hi hj).mp heq)

theorem rank_two_bound [Fintype K] {N : ℕ} (a : Fin N → Fin 2 → K)
    (ha : Arc.IsArc (K := K) 2 a) : N ≤ Fintype.card K + 1 := by
  have h := Fintype.card_le_of_injective (fun i => pointCode (a i))
    (pointCode_injective_of_minors a (rank_two_minor_ne_zero a ha))
  simpa using h

theorem rank_three_bound [Fintype K] {N : ℕ} (a : Fin N → Fin 3 → K)
    (ha : Arc.IsArc (K := K) 3 a) : N ≤ Fintype.card K + 2 := by
  by_cases hN : 3 ≤ N
  · cases N with
    | zero => omega
    | succ n =>
      obtain ⟨b, hb⟩ := StandardArcProjection.exists_contracted_arc hN a ha 0
      have h := rank_two_bound b hb
      omega
  · omega

theorem rank_two_exists_bound [Fintype K] {N : ℕ} (h : Arc.ExistsArc K 2 N) :
    N ≤ Fintype.card K + 1 := by
  obtain ⟨a, ha⟩ := h
  exact rank_two_bound a ha

theorem rank_three_exists_bound [Fintype K] {N : ℕ} (h : Arc.ExistsArc K 3 N) :
    N ≤ Fintype.card K + 2 := by
  obtain ⟨a, ha⟩ := h
  exact rank_three_bound a ha

end EvenOrderMDS.SmallRankArcBounds
