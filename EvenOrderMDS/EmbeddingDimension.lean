module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

namespace EvenOrderMDS.EmbeddingDimension

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Pad a finite basis with zero vectors, retaining an exact spanning equality. -/
theorem exists_spanning_family
    (W : Submodule K V) [FiniteDimensional K W] {n : ℕ}
    (hdim : Module.finrank K W ≤ n) :
    ∃ f : Fin n → V, W = Submodule.span K (Set.range f) := by
  classical
  let b := Module.finBasis K W
  let f : Fin n → V := fun i =>
    if hi : (i : ℕ) < Module.finrank K W then (b ⟨i, hi⟩ : V) else 0
  refine ⟨f, le_antisymm ?_ ?_⟩
  · intro x hx
    have hspan : Submodule.span K (Set.range b) ≤
        (Submodule.span K (Set.range f)).comap W.subtype := by
      apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      change (b i : V) ∈ Submodule.span K (Set.range f)
      apply Submodule.subset_span
      refine ⟨(⟨i, lt_of_lt_of_le i.is_lt hdim⟩ : Fin n), ?_⟩
      simp [f, i.is_lt]
    rw [b.span_eq] at hspan
    exact hspan (show (⟨x, hx⟩ : W) ∈ (⊤ : Submodule K W) from Submodule.mem_top)
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    by_cases hi : (i : ℕ) < Module.finrank K W
    · simp [f, hi]
    · simp [f, hi]

theorem range_fin_three {T : Type*} (f : Fin 3 → T) : Set.range f = {f 0, f 1, f 2} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
    rcases hi with hi | hi | hi
    · have heq : i = 0 := Fin.ext hi
      simp [heq]
    · have heq : i = 1 := Fin.ext hi
      simp [heq]
    · have heq : i = 2 := Fin.ext hi
      simp [heq]
  · intro hz
    have hz' : z = f 0 ∨ z = f 1 ∨ z = f 2 := by simpa using hz
    rcases hz' with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem exists_three_generators
    (W : Submodule K V) [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 3) :
    ∃ x y z : V, W = Submodule.span K ({x, y, z} : Set V) := by
  obtain ⟨f, hf⟩ := exists_spanning_family W hdim
  exact ⟨f 0, f 1, f 2, hf.trans (congrArg (Submodule.span K) (range_fin_three f))⟩

end EvenOrderMDS.EmbeddingDimension
