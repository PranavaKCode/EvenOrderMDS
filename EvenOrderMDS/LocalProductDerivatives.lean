module

public import EvenOrderMDS.ParityDerivation
public import EvenOrderMDS.LinearCoordinates

@[expose] public noncomputable section

/-!
# Local mixed derivatives at a transverse product zero

When two or three factors vanish at a point, only the terms differentiating
each vanishing factor survive. These are literal product-rule identities.
-/

namespace EvenOrderMDS.LocalProductDerivatives

variable {K ι : Type*} [Field K]

theorem two_vanishing_factors (f g H : MvPolynomial ι K) (x : ι → K) (i j : ι)
    (hf : MvPolynomial.eval x f = 0) (hg : MvPolynomial.eval x g = 0) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j (f * g * H))) =
      (MvPolynomial.eval x (MvPolynomial.pderiv i f) * MvPolynomial.eval x (MvPolynomial.pderiv j g) +
        MvPolynomial.eval x (MvPolynomial.pderiv j f) * MvPolynomial.eval x (MvPolynomial.pderiv i g)) *
        MvPolynomial.eval x H := by
  simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hf, hg,
    mul_zero, zero_mul, add_zero, zero_add, add_mul]
  ac_rfl

theorem three_vanishing_factors (f g h H : MvPolynomial ι K) (x : ι → K) (i j k : ι)
    (hf : MvPolynomial.eval x f = 0) (hg : MvPolynomial.eval x g = 0)
    (hh : MvPolynomial.eval x h = 0) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j
      (MvPolynomial.pderiv k (f * g * h * H)))) =
      (MvPolynomial.eval x (MvPolynomial.pderiv i f) * MvPolynomial.eval x (MvPolynomial.pderiv j g) * MvPolynomial.eval x (MvPolynomial.pderiv k h) +
       MvPolynomial.eval x (MvPolynomial.pderiv i f) * MvPolynomial.eval x (MvPolynomial.pderiv k g) * MvPolynomial.eval x (MvPolynomial.pderiv j h) +
       MvPolynomial.eval x (MvPolynomial.pderiv j f) * MvPolynomial.eval x (MvPolynomial.pderiv i g) * MvPolynomial.eval x (MvPolynomial.pderiv k h) +
       MvPolynomial.eval x (MvPolynomial.pderiv j f) * MvPolynomial.eval x (MvPolynomial.pderiv k g) * MvPolynomial.eval x (MvPolynomial.pderiv i h) +
       MvPolynomial.eval x (MvPolynomial.pderiv k f) * MvPolynomial.eval x (MvPolynomial.pderiv i g) * MvPolynomial.eval x (MvPolynomial.pderiv j h) +
       MvPolynomial.eval x (MvPolynomial.pderiv k f) * MvPolynomial.eval x (MvPolynomial.pderiv j g) * MvPolynomial.eval x (MvPolynomial.pderiv i h)) * MvPolynomial.eval x H := by
  simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hf, hg, hh,
    mul_zero, zero_mul, add_zero, zero_add, add_mul]
  ac_rfl

variable [Fintype ι] [DecidableEq ι]

theorem pderiv_linearForm (a : ι → K) (i : ι) :
    MvPolynomial.pderiv i (LinearCoordinates.linearForm a) = MvPolynomial.C (a i) := by
  rw [LinearCoordinates.linearForm_apply, map_sum]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp

theorem eval_pderiv_linearForm (a : ι → K) (x : ι → K) (i : ι) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (LinearCoordinates.linearForm a)) = a i := by
  rw [pderiv_linearForm]
  simp

theorem two_linear_factors (a b : ι → K) (H : MvPolynomial ι K) (x : ι → K) (i j : ι)
    (ha : MvPolynomial.eval x (LinearCoordinates.linearForm a) = 0)
    (hb : MvPolynomial.eval x (LinearCoordinates.linearForm b) = 0) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j
      (LinearCoordinates.linearForm a * LinearCoordinates.linearForm b * H))) =
      (a i * b j + a j * b i) * MvPolynomial.eval x H := by
  rw [two_vanishing_factors _ _ _ _ _ _ ha hb]
  simp only [eval_pderiv_linearForm]

end EvenOrderMDS.LocalProductDerivatives
