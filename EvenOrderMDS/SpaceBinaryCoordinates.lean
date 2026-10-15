module

public import EvenOrderMDS.BinaryParameterization
public import EvenOrderMDS.FourCofactor
public import EvenOrderMDS.BinaryLocalQuotient

@[expose] public noncomputable section

/-! Literal binary coordinates on the intersection of two old space-arc planes. -/

namespace EvenOrderMDS.SpaceBinaryCoordinates

open BinaryParameterization FourCofactor
open scoped Matrix

variable {K : Type*} [Field K] [CharP K 2]

theorem det_swap_rows {r : ℕ} (M : Matrix (Fin r) (Fin r) K) (i j : Fin r) (hij : i ≠ j) :
    Matrix.det (Matrix.submatrix M (Equiv.swap i j) id) = Matrix.det M := by
  rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]
  simp [CharTwo.neg_eq]

theorem det_swap_last (a b c d : Fin 4 → K) :
    Matrix.det ![a, b, d, c] = Matrix.det ![a, b, c, d] := by
  have h := det_swap_rows ![a, b, c, d] 2 3 (by decide)
  have hm : Matrix.submatrix ![a, b, c, d] (Equiv.swap (2 : Fin 4) 3) id = ![a, b, d, c] := by
    ext i j
    fin_cases i <;> rfl
  simpa only [hm] using h

theorem dot_cofactor_swap (a b c z : Fin 4 → K) :
    z ⬝ᵥ cofactor a b c = c ⬝ᵥ cofactor a b z := by
  rw [dotProduct_comm z, cofactor_dot, dotProduct_comm c, cofactor_dot, det_swap_last]

omit [CharP K 2] in
theorem right_pairing (a b c d : Fin 4 → K) :
    d ⬝ᵥ cofactor a b c = Matrix.det ![a, b, c, d] := by
  rw [dotProduct_comm, cofactor_dot]

theorem left_pairing (a b c d : Fin 4 → K) :
    c ⬝ᵥ cofactor a b d = Matrix.det ![a, b, c, d] := by
  rw [dot_cofactor_swap, right_pairing]

def coordinates (a b c d v : Fin 4 → K) : Fin 2 → K :=
  ![(d ⬝ᵥ v) / Matrix.det ![a, b, c, d], (c ⬝ᵥ v) / Matrix.det ![a, b, c, d]]

theorem point_coordinates (a b c d v : Fin 4 → K)
    (hd : Matrix.det ![a, b, c, d] ≠ 0) (ha : a ⬝ᵥ v = 0) (hb : b ⬝ᵥ v = 0) :
    point (cofactor a b c) (cofactor a b d) (coordinates a b c d v) = v := by
  have hu := (Matrix.isUnit_iff_isUnit_det ![a, b, c, d]).mpr (isUnit_iff_ne_zero.mpr hd)
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  funext i
  fin_cases i
  · simpa [Matrix.mulVec, point, coordinates, dotProduct_add, dotProduct_smul,
      cofactor_on_first] using ha.symm
  · simpa [Matrix.mulVec, point, coordinates, dotProduct_add, dotProduct_smul,
      cofactor_on_second] using hb.symm
  · change c ⬝ᵥ point (cofactor a b c) (cofactor a b d) (coordinates a b c d v) = c ⬝ᵥ v
    rw [point, dotProduct_add, dotProduct_smul, dotProduct_smul, cofactor_on_third,
      smul_zero, zero_add, left_pairing]
    exact div_mul_cancel₀ _ hd
  · change d ⬝ᵥ point (cofactor a b c) (cofactor a b d) (coordinates a b c d v) = d ⬝ᵥ v
    rw [point, dotProduct_add, dotProduct_smul, dotProduct_smul, cofactor_on_third,
      smul_zero, add_zero, right_pairing]
    exact div_mul_cancel₀ _ hd

theorem cofactor_coordinates (a b c d z : Fin 4 → K) (hd : Matrix.det ![a, b, c, d] ≠ 0) :
    point (cofactor a b c) (cofactor a b d) (coordinates a b c d (cofactor a b z)) = cofactor a b z := by
  apply point_coordinates a b c d _ hd
  · exact cofactor_on_first _ _ _
  · exact cofactor_on_second _ _ _

theorem cofactor_relation (a b c d z : Fin 4 → K) (hd : Matrix.det ![a, b, c, d] ≠ 0) :
    rowMap (cofactor a b c) (cofactor a b d) z =
      Matrix.det ![a, b, c, d] • ![coordinates a b c d (cofactor a b z) 1,
        coordinates a b c d (cofactor a b z) 0] := by
  funext i
  fin_cases i <;>
    simp [rowMap, coordinates, Pi.smul_apply, smul_eq_mul, mul_div_cancel₀ _ hd, dot_cofactor_swap]

theorem projected_determinant (a b c d z w : Fin 4 → K) (hd : Matrix.det ![a, b, c, d] ≠ 0) :
    Matrix.det ![rowMap (cofactor a b c) (cofactor a b d) z,
      rowMap (cofactor a b c) (cofactor a b d) w] =
      Matrix.det ![a, b, c, d] * Matrix.det ![a, b, z, w] := by
  have heval := congrArg (fun v => w ⬝ᵥ v) (cofactor_coordinates a b c d z hd)
  try dsimp only at heval
  rw [pairing_identity, dotProduct_comm w, cofactor_dot] at heval
  rw [← heval]
  have hrel := cofactor_relation a b c d z hd
  rw [hrel]
  erw [Matrix.det_fin_two]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    dotProduct, Fin.sum_univ_two, CharTwo.sub_eq_add]
  ring

end EvenOrderMDS.SpaceBinaryCoordinates
