module

public import EvenOrderMDS.NormalizedLine
public import Mathlib.Algebra.Prime.Lemmas

@[expose] public noncomputable section

/-!
# Coordinate-permuted charts for projective plane lines

Each chart describes an actual prime linear polynomial, its literal binary
restriction, and its point parametrization. A scalar multiple represents the
same geometric line, but is not silently identified with the polynomial.
-/

namespace EvenOrderMDS.PlaneLineChart

variable {K : Type*} [Field K]

structure Chart (K : Type*) where
  perm : Fin 3 ≃ Fin 3
  a : K
  b : K

noncomputable def polynomial (c : Chart K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.renameEquiv K c.perm (NormalizedLine.equation c.a c.b)

noncomputable def restrict (c : Chart K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K :=
  (LineRestriction.lineMap c.a c.b).comp
    (MvPolynomial.renameEquiv K c.perm.symm).toAlgHom

def point (c : Chart K) (v : Fin 2 → K) : Fin 3 → K :=
  fun i => ![v 0, v 1, c.a * v 0 + c.b * v 1] (c.perm.symm i)

theorem polynomial_homogeneous (c : Chart K) : (polynomial c).IsHomogeneous 1 :=
  (NormalizedLine.equation_homogeneous c.a c.b).rename_isHomogeneous

theorem polynomial_prime (c : Chart K) : Prime (polynomial c) :=
  (MulEquiv.prime_iff (MvPolynomial.renameEquiv K c.perm)).mpr
    (NormalizedLine.equation_prime c.a c.b)

theorem polynomial_ne_zero (c : Chart K) : polynomial c ≠ 0 :=
  (polynomial_prime c).ne_zero

theorem restrict_homogeneous (c : Chart K) {p : MvPolynomial (Fin 3) K} {j : ℕ}
    (hp : p.IsHomogeneous j) : (restrict c p).IsHomogeneous j :=
  LineRestriction.lineMap_homogeneous c.a c.b hp.rename_isHomogeneous

theorem restrict_zero_iff_divisible (c : Chart K) (p : MvPolynomial (Fin 3) K) :
    restrict c p = 0 ↔ polynomial c ∣ p := by
  change LineRestriction.lineMap c.a c.b
    (MvPolynomial.renameEquiv K c.perm.symm p) = 0 ↔ polynomial c ∣ p
  rw [LineKernel.lineMap_eq_zero_iff_divisible_equation]
  constructor
  · intro h
    have hd := map_dvd (MvPolynomial.renameEquiv K c.perm) h
    simpa only [polynomial, NormalizedLine.equation, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id,
      AlgHom.id_apply] using hd
  · intro h
    have hd := map_dvd (MvPolynomial.renameEquiv K c.perm.symm) h
    simpa only [polynomial, NormalizedLine.equation, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id,
      AlgHom.id_apply] using hd

theorem eval_restrict (c : Chart K) (v : Fin 2 → K) (p : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval v (restrict c p) = MvPolynomial.eval (point c v) p := by
  change ((MvPolynomial.aeval v).comp (restrict c)) p = (MvPolynomial.aeval (point c v)) p
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  obtain ⟨j, rfl⟩ := c.perm.surjective i
  fin_cases j <;> simp [restrict, point, LineRestriction.lineMap]

end EvenOrderMDS.PlaneLineChart
