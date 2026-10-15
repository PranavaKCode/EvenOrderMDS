module

public import EvenOrderMDS.BinaryParameterization
public import EvenOrderMDS.PlaneCofactorGeometry
public import EvenOrderMDS.BinaryLocalQuotient

@[expose] public noncomputable section

/-! Literal binary coordinates on an old plane-arc line. -/

namespace EvenOrderMDS.PlaneBinaryCoordinates

open BinaryParameterization
open scoped Matrix

variable {K : Type*} [Field K] [CharP K 2]

theorem dot_cross_swap (a b z : Fin 3 → K) : z ⬝ᵥ crossProduct a b = b ⬝ᵥ crossProduct a z := by
  rw [triple_product_permutation z a b, triple_product_permutation a b z,
    ← cross_anticomm a z, dotProduct_neg, CharTwo.neg_eq]

omit [CharP K 2] in
theorem right_pairing (a b c : Fin 3 → K) :
    c ⬝ᵥ crossProduct a b = Matrix.det ![a, b, c] := by
  rw [triple_product_permutation c a b, triple_product_eq_det]

theorem left_pairing (a b c : Fin 3 → K) :
    b ⬝ᵥ crossProduct a c = Matrix.det ![a, b, c] := by
  rw [dot_cross_swap a c b, right_pairing]

def coordinates (a b c v : Fin 3 → K) : Fin 2 → K :=
  ![(c ⬝ᵥ v) / Matrix.det ![a, b, c], (b ⬝ᵥ v) / Matrix.det ![a, b, c]]

theorem point_coordinates (a b c v : Fin 3 → K)
    (hd : Matrix.det ![a, b, c] ≠ 0) (hv : a ⬝ᵥ v = 0) :
    point (crossProduct a b) (crossProduct a c) (coordinates a b c v) = v := by
  have hu := (Matrix.isUnit_iff_isUnit_det ![a, b, c]).mpr (isUnit_iff_ne_zero.mpr hd)
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  funext i
  fin_cases i
  · simpa [Matrix.mulVec, point, coordinates, dotProduct_add, dotProduct_smul] using hv.symm
  · simp [Matrix.mulVec, point, coordinates, dotProduct_add, dotProduct_smul,
      left_pairing, div_mul_cancel₀ _ hd]
  · simp [Matrix.mulVec, point, coordinates, dotProduct_add, dotProduct_smul,
      right_pairing, div_mul_cancel₀ _ hd]

theorem cofactor_coordinates (a b c z : Fin 3 → K) (hd : Matrix.det ![a, b, c] ≠ 0) :
    point (crossProduct a b) (crossProduct a c) (coordinates a b c (crossProduct a z)) =
      crossProduct a z :=
  point_coordinates a b c _ hd (dot_self_cross _ _)

theorem cofactor_relation (a b c z : Fin 3 → K) (hd : Matrix.det ![a, b, c] ≠ 0) :
    rowMap (crossProduct a b) (crossProduct a c) z =
      Matrix.det ![a, b, c] • ![coordinates a b c (crossProduct a z) 1,
        coordinates a b c (crossProduct a z) 0] := by
  funext i
  fin_cases i <;>
    simp [rowMap, coordinates, Pi.smul_apply, smul_eq_mul, mul_div_cancel₀ _ hd, dot_cross_swap]

theorem cross_basis (a b c : Fin 3 → K) :
    crossProduct (crossProduct a b) (crossProduct a c) = Matrix.det ![a, b, c] • a := by
  rw [cross_cross_eq_smul_sub_smul, dot_self_cross, left_pairing, zero_smul, zero_sub,
    ← neg_smul, CharTwo.neg_eq]

theorem rowMap_kernel (a b c : Fin 3 → K) (hd : Matrix.det ![a, b, c] ≠ 0) :
    LinearMap.ker (rowMap (crossProduct a b) (crossProduct a c)) = Submodule.span K {a} := by
  have ha : a ≠ 0 := by
    have hlin := Matrix.linearIndependent_rows_of_det_ne_zero hd
    exact hlin.ne_zero 0
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hz
    have hx : z ⬝ᵥ crossProduct a b = 0 := congrFun hz 0
    have hy : z ⬝ᵥ crossProduct a c = 0 := congrFun hz 1
    have hcross : crossProduct a z = 0 := by
      have h := cross_cross_eq_smul_sub_smul (crossProduct a b) (crossProduct a c) z
      rw [cross_basis, LinearMap.map_smul, LinearMap.smul_apply,
        dotProduct_comm (crossProduct a b), dotProduct_comm (crossProduct a c),
        hx, hy, zero_smul, zero_smul, sub_zero] at h
      exact (smul_eq_zero.mp h).resolve_left hd
    have hn : ¬ LinearIndependent K ![a, z] := by
      rw [← crossProduct_ne_zero_iff_linearIndependent]
      exact not_not.mpr hcross
    rw [LinearIndependent.pair_iff' ha, not_forall_not] at hn
    obtain ⟨s, hs⟩ := hn
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    simp [rowMap]

end EvenOrderMDS.PlaneBinaryCoordinates
