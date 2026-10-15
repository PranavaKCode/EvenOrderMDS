module

public import EvenOrderMDS.BinaryEvaluation
public import EvenOrderMDS.GradedImage
public import Mathlib.Algebra.Algebra.Operations

@[expose] public noncomputable section

/-!
# Standard generation and binary homogeneous pieces

Standard generation is represented concretely by A_j = (A_1)^j as submodules
of the algebra. Quotient generation is proved through the actual image map.
-/

namespace EvenOrderMDS.StandardGeneration

open scoped Pointwise

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]

def StandardGenerated (A : ℕ → Submodule K R) : Prop :=
  ∀ j : ℕ, A j = (A 1) ^ j

theorem image_standard_generated
    (A : ℕ → Submodule K R) (hA : StandardGenerated A) (q : R →ₐ[K] S) :
    StandardGenerated (GradedImage.imagePieces A q) := by
  intro j
  unfold GradedImage.imagePieces
  rw [hA j]
  exact Submodule.map_pow (A 1) q j

theorem degree_one_nonzero
    (A : ℕ → Submodule K R) (hA : StandardGenerated A)
    {s : ℕ} (hs : 0 < s) (htop : A s ≠ ⊥) : A 1 ≠ ⊥ := by
  intro hzero
  apply htop
  rw [hA s, hzero]
  exact zero_pow (by omega)

theorem mem_pair_power (x y z : R) (n : ℕ) :
    z ∈ ({x, y} : Set R) ^ n ↔ ∃ i : ℕ, i ≤ n ∧ z = x ^ i * y ^ (n - i) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Set.mem_mul]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        obtain ⟨i, hi, rfl⟩ := (ih b).mp hb
        have ha' : a = x ∨ a = y := by simpa using ha
        rcases ha' with rfl | rfl
        · refine ⟨i + 1, by omega, ?_⟩
          rw [show n + 1 - (i + 1) = n - i by omega, pow_succ']
          ac_rfl
        · refine ⟨i, by omega, ?_⟩
          rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
          ac_rfl
      · rintro ⟨i, hi, rfl⟩
        by_cases hi0 : i = 0
        · subst i
          refine ⟨y, by simp, y ^ n, ?_, ?_⟩
          · exact (ih _).mpr ⟨0, Nat.zero_le _, by simp⟩
          · simp [pow_succ, mul_comm]
        · refine ⟨x, by simp, x ^ (i - 1) * y ^ (n - (i - 1)), ?_, ?_⟩
          · exact (ih _).mpr ⟨i - 1, by omega, rfl⟩
          · have hfirst : i - 1 + 1 = i := by omega
            have hsecond : n - (i - 1) = n + 1 - i := by omega
            rw [← mul_assoc, ← pow_succ', hfirst, hsecond]

theorem span_pair_power (x y : R) (j : ℕ) :
    (Submodule.span K ({x, y} : Set R)) ^ j = BinaryEvaluation.binaryPiece (K := K) x y j := by
  rw [Submodule.span_pow]
  unfold BinaryEvaluation.binaryPiece
  congr 1
  ext z
  rw [mem_pair_power]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(⟨i, by omega⟩ : Fin (j + 1)), rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by omega, rfl⟩

theorem binary_piece_of_standard_generation
    (A : ℕ → Submodule K R) (hA : StandardGenerated A)
    (x y : R) (hgenerators : A 1 = Submodule.span K ({x, y} : Set R)) (j : ℕ) :
    A j = BinaryEvaluation.binaryPiece (K := K) x y j := by
  rw [hA j, hgenerators, span_pair_power]

theorem binary_hilbert_bound
    (A : ℕ → Submodule K R) (hA : StandardGenerated A)
    (x y : R) (hgenerators : A 1 = Submodule.span K ({x, y} : Set R)) (j : ℕ) :
    Module.finrank K (A j) ≤ j + 1 := by
  have heq := congrArg (fun V : Submodule K R => Module.finrank K V)
    (binary_piece_of_standard_generation A hA x y hgenerators j)
  rw [heq]
  exact BinaryEvaluation.binary_piece_dimension_bound x y j

theorem binary_hilbert_no_rise
    (A : ℕ → Submodule K R) (hA : StandardGenerated A)
    (x y : R) (hgenerators : A 1 = Submodule.span K ({x, y} : Set R))
    {j : ℕ} (hdeficit : Module.finrank K (A j) < j + 1) :
    Module.finrank K (A (j + 1)) ≤ Module.finrank K (A j) := by
  have heq : ∀ i, Module.finrank K (A i) =
      Module.finrank K (BinaryEvaluation.binaryPiece (K := K) x y i) :=
    fun i => congrArg (fun V : Submodule K R => Module.finrank K V)
      (binary_piece_of_standard_generation A hA x y hgenerators i)
  rw [heq j] at hdeficit
  rw [heq (j + 1), heq j]
  exact BinaryEvaluation.binary_piece_no_rise x y hdeficit

end EvenOrderMDS.StandardGeneration
