module

public import EvenOrderMDS.StandardArcProjection
public import EvenOrderMDS.LineKernel
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Algebra.Prime.Lemmas

@[expose] public noncomputable section

/-!
# Literal polynomial restriction along the constructed column projection

The induced algebra map has exactly the original linear form as its principal
kernel and sends every other literal linear form to its projected column.
-/

namespace EvenOrderMDS.CoordinateRestriction

open LinearCoordinates CoordinateNormalization
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def coordinateDrop {n : ℕ} (p : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.killCompl (f := p.succAbove) Fin.succAbove_right_injective

theorem coordinateDrop_X_center {n : ℕ} (p : Fin (n + 1)) :
    coordinateDrop (K := K) p (MvPolynomial.X p) = 0 := by
  have hnot : p ∉ Set.range p.succAbove := by
    rintro ⟨j, hj⟩
    exact Fin.succAbove_ne p j hj
  simp only [coordinateDrop, MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hnot]

theorem coordinateDrop_X_other {n : ℕ} (p : Fin (n + 1)) (j : Fin n) :
    coordinateDrop (K := K) p (MvPolynomial.X (p.succAbove j)) = MvPolynomial.X j := by
  rw [← MvPolynomial.rename_X p.succAbove j]
  exact MvPolynomial.killCompl_rename_app Fin.succAbove_right_injective _

theorem coordinateDrop_surjective {n : ℕ} (p : Fin (n + 1)) :
    Function.Surjective (coordinateDrop (K := K) p) := by
  intro q
  exact ⟨MvPolynomial.rename p.succAbove q,
    MvPolynomial.killCompl_rename_app Fin.succAbove_right_injective q⟩

theorem coordinateDrop_linearForm {n : ℕ} (p : Fin (n + 1)) (a : Fin (n + 1) → K) :
    coordinateDrop p (linearForm a) = linearForm (fun j : Fin n => a (p.succAbove j)) := by
  rw [linearForm_apply, Fin.sum_univ_succAbove _ p, map_add, map_smul,
    coordinateDrop_X_center, smul_zero, zero_add, map_sum]
  simp only [map_smul, coordinateDrop_X_other, linearForm_apply]

theorem coordinateDrop_zero_iff {n : ℕ} (p : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) K) :
    coordinateDrop p f = 0 ↔ MvPolynomial.X p ∣ f := by
  let I : Ideal (MvPolynomial (Fin (n + 1)) K) := Ideal.span {MvPolynomial.X p}
  let Q := Ideal.Quotient.mkₐ K I
  have hXp : Q (MvPolynomial.X p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  have hcomp : Q.comp ((MvPolynomial.rename p.succAbove).comp (coordinateDrop p)) = Q := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = p
    · subst i
      simp only [AlgHom.comp_apply, coordinateDrop_X_center, map_zero]
      exact hXp.symm
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simp only [AlgHom.comp_apply, coordinateDrop_X_other, MvPolynomial.rename_X]
  constructor
  · intro hf
    have hz : Q f = 0 := by
      rw [← hcomp]
      simp only [AlgHom.comp_apply, hf, map_zero]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  · rintro ⟨g, rfl⟩
    rw [map_mul, coordinateDrop_X_center, zero_mul]

theorem algHom_homogeneous {σ τ : Type*}
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hX : ∀ i, (f (MvPolynomial.X i)).IsHomogeneous 1)
    {p : MvPolynomial σ K} {j : ℕ} (hp : p.IsHomogeneous j) : (f p).IsHomogeneous j := by
  rw [MvPolynomial.aeval_unique f]
  simpa only [one_mul] using hp.aeval (f ∘ MvPolynomial.X) hX

theorem coordinateDrop_homogeneous {n : ℕ} (p : Fin (n + 1))
    {f : MvPolynomial (Fin (n + 1)) K} {j : ℕ} (hf : f.IsHomogeneous j) :
    (coordinateDrop p f).IsHomogeneous j := by
  apply algHom_homogeneous (coordinateDrop p) _ hf
  intro i
  by_cases hi : i = p
  · subst i
    rw [coordinateDrop_X_center]
    exact MvPolynomial.isHomogeneous_zero (Fin n) K 1
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [coordinateDrop_X_other]
    exact MvPolynomial.isHomogeneous_X K k

theorem changeCoordinates_homogeneous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : (ι → K) ≃ₗ[K] (ι → K)) {f : MvPolynomial ι K} {j : ℕ} (hf : f.IsHomogeneous j) :
    (changeCoordinates e f).IsHomogeneous j := by
  apply algHom_homogeneous (changeCoordinates e).toAlgHom _ hf
  intro i
  change (substitute e (MvPolynomial.X i)).IsHomogeneous 1
  rw [substitute_X]
  exact linearForm_homogeneous _

noncomputable def restrictAlong {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  (coordinateDrop p).comp (changeCoordinates (normalize a p ha)).toAlgHom

theorem restrictAlong_linearForm {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0)
    (b : Fin (n + 1) → K) :
    restrictAlong a p ha (linearForm b) = linearForm (StandardArcProjection.projection a p ha b) := by
  change coordinateDrop p (changeCoordinates (normalize a p ha) (linearForm b)) = _
  rw [changeCoordinates_linearForm, coordinateDrop_linearForm]
  rfl

theorem restrictAlong_surjective {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0) :
    Function.Surjective (restrictAlong a p ha) :=
  (coordinateDrop_surjective p).comp (changeCoordinates (normalize a p ha)).surjective

theorem restrictAlong_homogeneous {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0)
    {f : MvPolynomial (Fin (n + 1)) K} {j : ℕ} (hf : f.IsHomogeneous j) :
    (restrictAlong a p ha f).IsHomogeneous j :=
  coordinateDrop_homogeneous p (changeCoordinates_homogeneous (normalize a p ha) hf)

theorem restrictAlong_zero_iff {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0)
    (f : MvPolynomial (Fin (n + 1)) K) : restrictAlong a p ha f = 0 ↔ linearForm a ∣ f := by
  change coordinateDrop p (changeCoordinates (normalize a p ha) f) = 0 ↔ _
  rw [coordinateDrop_zero_iff]
  have hX : changeCoordinates (normalize a p ha) (linearForm a) = MvPolynomial.X p := by
    rw [changeCoordinates_linearForm, normalize_column, linearForm_single]
  rw [← hX, map_dvd_iff]

theorem coordinate_variable_prime {n : ℕ} (p : Fin (n + 1)) :
    Prime (MvPolynomial.X p : MvPolynomial (Fin (n + 1)) K) := by
  apply (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero p)).mp
  have hker : Ideal.span {MvPolynomial.X p} = RingHom.ker (coordinateDrop (K := K) p).toRingHom := by
    ext f
    exact Ideal.mem_span_singleton.trans (coordinateDrop_zero_iff p f).symm
  rw [hker]
  exact RingHom.ker_isPrime (coordinateDrop (K := K) p)

theorem linearForm_prime {n : ℕ} (a : Fin (n + 1) → K) (p : Fin (n + 1)) (ha : a p ≠ 0) :
    Prime (linearForm a) := by
  apply (MulEquiv.prime_iff (changeCoordinates (normalize a p ha))).mp
  rw [changeCoordinates_linearForm, normalize_column, linearForm_single]
  exact coordinate_variable_prime p

end EvenOrderMDS.CoordinateRestriction
