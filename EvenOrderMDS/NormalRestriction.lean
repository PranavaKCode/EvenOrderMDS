module

public import EvenOrderMDS.CoordinateRestriction
public import EvenOrderMDS.MixedParity
public import EvenOrderMDS.FourCofactorDerivatives
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public noncomputable section

/-! Literal restriction to z=0, commuting derivatives, and exact normal degree guards. -/

namespace EvenOrderMDS.NormalRestriction

variable {K : Type*} [Field K]

theorem pderiv_commute {σ : Type*} (i j : σ) (p : MvPolynomial σ K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k h =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [MvPolynomial.pderiv_X, add_comm]

noncomputable def restriction : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0]

def point (v : Fin 3 → K) : Fin 4 → K := ![v 0, v 1, v 2, 0]

theorem restriction_X (i : Fin 3) : restriction (MvPolynomial.X i.castSucc : MvPolynomial (Fin 4) K) =
    MvPolynomial.X i := by
  fin_cases i <;> simp [restriction]

theorem restriction_z : restriction (MvPolynomial.X 3 : MvPolynomial (Fin 4) K) = 0 := by
  simp [restriction]

theorem restriction_homogeneous {p : MvPolynomial (Fin 4) K} {d : ℕ} (hp : p.IsHomogeneous d) :
    (restriction p).IsHomogeneous d := by
  apply CoordinateRestriction.algHom_homogeneous restriction _ hp
  intro i
  fin_cases i
  · simpa [restriction] using MvPolynomial.isHomogeneous_X K (0 : Fin 3)
  · simpa [restriction] using MvPolynomial.isHomogeneous_X K (1 : Fin 3)
  · simpa [restriction] using MvPolynomial.isHomogeneous_X K (2 : Fin 3)
  · simpa [restriction] using MvPolynomial.isHomogeneous_zero (Fin 3) K 1

theorem eval_restriction (v : Fin 3 → K) (p : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval v (restriction p) = MvPolynomial.eval (point v) p := by
  change ((MvPolynomial.aeval v).comp restriction) p = (MvPolynomial.aeval (point v)) p
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [restriction, point]

theorem restriction_pderiv (i : Fin 3) (p : MvPolynomial (Fin 4) K) :
    restriction (MvPolynomial.pderiv i.castSucc p) = MvPolynomial.pderiv i (restriction p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [restriction]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k h =>
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, h]
    fin_cases k <;> fin_cases i <;> simp [restriction, MvPolynomial.pderiv_X]

noncomputable def mixed (p : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))

theorem mixed_eq_thirdDerivative (p : MvPolynomial (Fin 4) K) :
    mixed p = FourCofactorDerivatives.thirdDerivative p 3 := rfl

theorem restriction_mixed (p : MvPolynomial (Fin 4) K) :
    restriction (mixed p) = MixedParity.mixedThird (restriction p) := by
  change restriction (MvPolynomial.pderiv (0 : Fin 3).castSucc
    (MvPolynomial.pderiv (1 : Fin 3).castSucc (MvPolynomial.pderiv (2 : Fin 3).castSucc p))) = _
  rw [restriction_pderiv, restriction_pderiv, restriction_pderiv]
  rfl

theorem normal_pderiv_mixed (p : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 3 (mixed p) = mixed (MvPolynomial.pderiv 3 p) := by
  unfold mixed
  rw [pderiv_commute 3 0, pderiv_commute 3 1, pderiv_commute 3 2]

theorem mixed_z_mul (p : MvPolynomial (Fin 4) K) :
    mixed (MvPolynomial.X 3 * p) = MvPolynomial.X 3 * mixed p := by
  simp [mixed, MvPolynomial.pderiv_X]

theorem normal_derivative_homogeneous {p : MvPolynomial (Fin 4) K} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (restriction (MvPolynomial.pderiv 3 p)).IsHomogeneous (d - 1) :=
  restriction_homogeneous hp.pderiv

theorem normal_derivative_zero_degree {p : MvPolynomial (Fin 4) K}
    (hp : p.IsHomogeneous 0) : restriction (MvPolynomial.pderiv 3 p) = 0 := by
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
  rw [hp, MvPolynomial.pderiv_C, map_zero]

theorem first_normal_mixed_zero {n : ℕ} (hn : 2 ≤ n) (p : MvPolynomial (Fin 4) K)
    (hhighest : mixed (MvPolynomial.X 3 * p) = MvPolynomial.X 3 ^ (2 * n)) :
    MixedParity.mixedThird (restriction (MvPolynomial.pderiv 3 p)) = 0 := by
  have hpow : (MvPolynomial.X 3 : MvPolynomial (Fin 4) K) ^ (2 * n) =
      MvPolynomial.X 3 * MvPolynomial.X 3 ^ (2 * n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [mixed_z_mul, hpow] at hhighest
  have h := mul_left_cancel₀ (MvPolynomial.X_ne_zero (3 : Fin 4)) hhighest
  have hd := congrArg (fun f => restriction (MvPolynomial.pderiv 3 f)) h
  try dsimp only at hd
  rw [normal_pderiv_mixed, restriction_mixed] at hd
  rw [hd, MvPolynomial.pderiv_pow]
  simp [restriction, show 2 * n - 1 - 1 ≠ 0 by omega]

end EvenOrderMDS.NormalRestriction
