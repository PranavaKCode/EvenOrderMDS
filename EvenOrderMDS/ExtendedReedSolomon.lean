module

public import EvenOrderMDS.EvaluationArc
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Option

@[expose] public noncomputable section

/-! Extended polynomial evaluation constructs the q+1 literal arc. -/

namespace EvenOrderMDS.ExtendedReedSolomon

open Module Polynomial

variable {K : Type*} [Field K]

def value (k : ℕ) (x : Option K) (p : Polynomial K) : K :=
  match x with
  | none => p.coeff (k - 1)
  | some a => p.eval a

noncomputable def evaluation (k : ℕ) (x : Option K) : degreeLT K k →ₗ[K] K where
  toFun p := value k x p.val
  map_add' := by intro p q; cases x <;> simp [value]
  map_smul' := by intro c p; cases x <;> simp [value, Polynomial.smul_eq_C_mul]

theorem zero_of_selected_values {k : ℕ} (f : Fin k ↪ Option K)
    (p : Polynomial K) (hp : p ∈ degreeLT K k) (hz : ∀ i, value k (f i) p = 0) : p = 0 := by
  classical
  by_cases hp0 : p = 0
  · exact hp0
  have hdeg : p.natDegree < k := by
    simpa only [degree_eq_natDegree hp0, Nat.cast_lt] using mem_degreeLT.mp hp
  let S : Finset (Option K) := Finset.univ.map f
  have hS : S.card = k := by simp [S]
  have hroots (x : K) (hx : x ∈ S.eraseNone) : p.eval x = 0 := by
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp (Finset.mem_eraseNone.mp hx)
    have h := hz i
    rw [hi] at h
    exact h
  by_cases hinfty : none ∈ S
  · have hcoeff : p.coeff (k - 1) = 0 := by
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hinfty
      have h := hz i
      rw [hi] at h
      exact h
    have hstrict : p.natDegree < k - 1 := by
      apply lt_of_le_of_ne (by omega)
      intro heq
      rw [← heq, coeff_natDegree, leadingCoeff_eq_zero] at hcoeff
      exact hp0 hcoeff
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S.eraseNone hroots
    rw [Finset.card_eraseNone_of_mem hinfty, hS]
    exact hstrict
  · apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S.eraseNone hroots
    rw [Finset.card_eraseNone_of_not_mem hinfty, hS]
    exact hdeg

theorem selected_evaluation_injective {k : ℕ} (f : Fin k ↪ Option K) :
    Function.Injective (fun p : degreeLT K k => fun i => evaluation k (f i) p) := by
  intro p q h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply zero_of_selected_values f (p.val - q.val) ((degreeLT K k).sub_mem p.property q.property)
  intro i
  have hi := congrFun h i
  try dsimp only at hi
  change evaluation k (f i) (p - q) = 0
  rw [map_sub, hi, sub_self]

noncomputable def basis (k : ℕ) : Basis (Fin k) K (degreeLT K k) :=
  Basis.ofEquivFun (degreeLTEquiv K k)

noncomputable def columns (k : ℕ) : Option K → Fin k → K :=
  EvaluationArc.columns (basis k) (evaluation k)

theorem columns_are_arc (k : ℕ) : ArcFamilies.IsArcOn (K := K) k (columns (K := K) k) :=
  EvaluationArc.isArcOn_of_evaluation_injective (basis k) (evaluation k) selected_evaluation_injective

/-- The dimension guard is retained so this construction is never advertised through arc vacuity. -/
theorem exists_extended_rs_arc [Fintype K] (k : ℕ) (_hk : k ≤ Fintype.card K + 1) :
    Arc.ExistsArc K k (Fintype.card K + 1) := by
  have h : Arc.ExistsArc K k (Fintype.card (Option K)) := by
    let e := (Fintype.equivFin (Option K)).symm
    exact ⟨fun i => columns k (e i), ArcFamilies.restrict (columns_are_arc k) e.toEmbedding⟩
  simpa using h

end EvenOrderMDS.ExtendedReedSolomon
