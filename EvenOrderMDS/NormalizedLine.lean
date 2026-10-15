module

public import EvenOrderMDS.LineKernel
public import Mathlib.RingTheory.Ideal.Maximal

@[expose] public noncomputable section

/-!
# Prime normalized linear factors

Each equation Z-aX-bY is a nonzero homogeneous prime polynomial. Distinct
parameter pairs give nondividing factors; no geometric general-position
assumption is silently included here.
-/

namespace EvenOrderMDS.NormalizedLine

open LineRestriction LineKernel

variable {K : Type*} [Field K]

noncomputable def equation (a b : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 2 - a • MvPolynomial.X 0 - b • MvPolynomial.X 1

theorem equation_homogeneous (a b : K) : (equation a b).IsHomogeneous 1 := by
  exact ((MvPolynomial.homogeneousSubmodule (Fin 3) K 1).sub_mem
    (MvPolynomial.isHomogeneous_X K 2)
    ((MvPolynomial.homogeneousSubmodule (Fin 3) K 1).smul_mem a
      (MvPolynomial.isHomogeneous_X K 0))) |> fun h =>
        (MvPolynomial.homogeneousSubmodule (Fin 3) K 1).sub_mem h
          ((MvPolynomial.homogeneousSubmodule (Fin 3) K 1).smul_mem b
            (MvPolynomial.isHomogeneous_X K 1))

theorem equation_coefficient_two (a b : K) :
    (equation a b).coeff (Finsupp.single 2 1) = 1 := by
  simp [equation, MvPolynomial.coeff_X', Finsupp.single_eq_single_iff]

theorem equation_ne_zero (a b : K) : equation a b ≠ 0 := by
  intro h
  have hc := equation_coefficient_two a b
  rw [h, MvPolynomial.coeff_zero] at hc
  exact zero_ne_one hc

theorem equation_prime (a b : K) : Prime (equation a b) := by
  apply (Ideal.span_singleton_prime (equation_ne_zero a b)).mp
  have hker : Ideal.span {equation a b} = RingHom.ker (lineMap a b).toRingHom := by
    ext p
    exact (Ideal.mem_span_singleton.trans
      (lineMap_eq_zero_iff_divisible_equation a b p).symm)
  rw [hker]
  exact RingHom.ker_isPrime (lineMap a b)

theorem equation_not_dvd_of_ne (a b c d : K) (hne : (a, b) ≠ (c, d)) :
    ¬ equation a b ∣ equation c d := by
  intro hdiv
  have hz := (lineMap_eq_zero_iff_divisible_equation a b (equation c d)).mpr hdiv
  have h0 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single (0 : Fin 2) 1)) hz
  have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single (1 : Fin 2) 1)) hz
  simp [equation, map_sub, map_smul, lineMap_X_zero, lineMap_X_one, lineMap_X_two,
    MvPolynomial.coeff_X', Finsupp.single_eq_single_iff] at h0 h1
  apply hne
  exact Prod.ext (sub_eq_zero.mp h0) (sub_eq_zero.mp h1)

end EvenOrderMDS.NormalizedLine
