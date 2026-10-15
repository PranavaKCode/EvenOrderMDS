module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Polynomial.Roots
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

/-!
# Binary homogeneous forms: the projective root bound in one affine chart

The point at infinity is counted separately from the distinct affine roots.
All identities concern literal homogeneous polynomials over an arbitrary field.
-/

namespace EvenOrderMDS.BinaryRootBound

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def dehomogenize :
    MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, 1]

theorem dehomogenize_degree {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) : (dehomogenize q).natDegree ≤ j := by
  classical
  rw [q.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hdeg : d 0 + d 1 = j := by
    have h := hq (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using h
  change (MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial K)]
    (MvPolynomial.monomial d (q.coeff d))).natDegree ≤ j
  rw [MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, mul_one, ← Polynomial.C_eq_algebraMap,
    Polynomial.C_mul_X_pow_eq_monomial]
  exact (Polynomial.natDegree_monomial_le (q.coeff d)).trans
    (show d 0 ≤ j by omega)

theorem homogenize_dehomogenize {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) : (dehomogenize q).homogenize j = q :=
  Polynomial.homogenize_eq_of_isHomogeneous hq rfl

theorem dehomogenize_zero_iff {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) : dehomogenize q = 0 ↔ q = 0 := by
  constructor
  · intro h
    rw [← homogenize_dehomogenize hq, h, Polynomial.homogenize_zero]
  · intro h
    rw [h, map_zero]

theorem eval_affine (q : MvPolynomial (Fin 2) K) (t : K) :
    (dehomogenize q).eval t = MvPolynomial.eval ![t, 1] q := by
  change ((Polynomial.aeval t).comp dehomogenize) q = (MvPolynomial.aeval ![t, 1]) q
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [dehomogenize]

theorem zero_of_affine_roots {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) (S : Finset K)
    (hroots : ∀ t ∈ S, MvPolynomial.eval ![t, 1] q = 0)
    (hcard : j < S.card) : q = 0 := by
  apply (dehomogenize_zero_iff hq).mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (dehomogenize q) S
  · intro t ht
    rw [eval_affine]
    exact hroots t ht
  · exact lt_of_le_of_lt (dehomogenize_degree hq) hcard

theorem eval_homogenize_infinity (p : Polynomial K) (j : ℕ) :
    MvPolynomial.eval ![1, 0] (p.homogenize j) = p.coeff j := by
  classical
  rw [Polynomial.homogenize, MvPolynomial.eval_sum]
  rw [Finset.sum_eq_single (j, 0)]
  · simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  · intro kl hkl hne
    have hsum := Finset.mem_antidiagonal.mp hkl
    have hpos : kl.2 ≠ 0 := by
      intro hzero
      apply hne
      ext <;> omega
    simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
      hpos]
  · simp

theorem eval_infinity {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) :
    MvPolynomial.eval ![1, 0] q = (dehomogenize q).coeff j := by
  calc
    _ = MvPolynomial.eval ![1, 0] ((dehomogenize q).homogenize j) :=
      congrArg (MvPolynomial.eval ![1, 0]) (homogenize_dehomogenize hq).symm
    _ = _ := eval_homogenize_infinity _ _

theorem zero_of_affine_roots_and_infinity {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) (S : Finset K)
    (hroots : ∀ t ∈ S, MvPolynomial.eval ![t, 1] q = 0)
    (hinfinity : MvPolynomial.eval ![1, 0] q = 0)
    (hcard : j < S.card + 1) : q = 0 := by
  apply (dehomogenize_zero_iff hq).mp
  by_cases hp : dehomogenize q = 0
  · exact hp
  have hdeg := dehomogenize_degree hq
  have hcoeff : (dehomogenize q).coeff j = 0 := by
    rw [← eval_infinity hq]
    exact hinfinity
  have hstrict : (dehomogenize q).natDegree < j := by
    apply lt_of_le_of_ne hdeg
    intro heq
    have hz := hcoeff
    rw [← heq, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero] at hz
    exact hp hz
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (dehomogenize q) S
  · intro t ht
    rw [eval_affine]
    exact hroots t ht
  · omega

theorem affine_zero_of_projective_zero {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) (v : Fin 2 → K) (hy : v 1 ≠ 0)
    (hv : MvPolynomial.eval v q = 0) :
    MvPolynomial.eval ![v 0 / v 1, 1] q = 0 := by
  rw [← eval_affine]
  have h := Polynomial.eval_homogenize (dehomogenize_degree hq) v hy
  rw [homogenize_dehomogenize hq, hv] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ hy)

theorem eval_homogenize_horizontal (p : Polynomial K) (j : ℕ) (x : K) :
    MvPolynomial.eval ![x, 0] (p.homogenize j) = p.coeff j * x ^ j := by
  classical
  rw [Polynomial.homogenize, MvPolynomial.eval_sum]
  rw [Finset.sum_eq_single (j, 0)]
  · simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  · intro kl hkl hne
    have hsum := Finset.mem_antidiagonal.mp hkl
    have hpos : kl.2 ≠ 0 := by
      intro hzero
      apply hne
      ext <;> omega
    simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, hpos]
  · simp

theorem infinity_zero_of_projective_zero {q : MvPolynomial (Fin 2) K} {j : ℕ}
    (hq : q.IsHomogeneous j) (x : K) (hx : x ≠ 0)
    (hv : MvPolynomial.eval ![x, 0] q = 0) :
    MvPolynomial.eval ![1, 0] q = 0 := by
  have h := eval_homogenize_horizontal (dehomogenize q) j x
  rw [homogenize_dehomogenize hq, hv] at h
  rw [eval_infinity hq]
  exact (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ hx)

theorem zero_of_projective_roots {ι : Type*} [Fintype ι]
    {q : MvPolynomial (Fin 2) K} {j : ℕ} (hq : q.IsHomogeneous j)
    (v : ι → Fin 2 → K) (hne : ∀ i, v i 0 ≠ 0 ∨ v i 1 ≠ 0)
    (hsep : ∀ i k, i ≠ k → v i 0 * v k 1 ≠ v k 0 * v i 1)
    (hroots : ∀ i, MvPolynomial.eval (v i) q = 0)
    (hcard : j < Fintype.card ι) : q = 0 := by
  classical
  let ratio : ι → K := fun i => v i 0 / v i 1
  have hinj : ∀ i k, v i 1 ≠ 0 → v k 1 ≠ 0 → ratio i = ratio k → i = k := by
    intro i k hi hk heq
    by_contra hik
    exact hsep i k hik ((div_eq_div_iff hi hk).mp heq)
  by_cases hy : ∀ i, v i 1 ≠ 0
  · let S := Finset.univ.image ratio
    apply zero_of_affine_roots hq S
    · intro t ht
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      exact affine_zero_of_projective_zero hq (v i) (hy i) (hroots i)
    · have hc : S.card = Fintype.card ι := by
        apply Finset.card_image_of_injective
        intro i k h
        exact hinj i k (hy i) (hy k) h
      omega
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hy
    have hi₀ : v i₀ 1 = 0 := Classical.not_not.mp hi₀
    have hx₀ : v i₀ 0 ≠ 0 := (hne i₀).resolve_right (by simp [hi₀])
    have hy' : ∀ i, i ≠ i₀ → v i 1 ≠ 0 := by
      intro i hi hzero
      exact hsep i i₀ hi (by simp [hi₀, hzero])
    let S := (Finset.univ.erase i₀).image ratio
    apply zero_of_affine_roots_and_infinity hq S
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      exact affine_zero_of_projective_zero hq (v i)
        (hy' i (Finset.mem_erase.mp hi).1) (hroots i)
    · apply infinity_zero_of_projective_zero hq (v i₀ 0) hx₀
      have hv : v i₀ = ![v i₀ 0, 0] := by
        funext k
        fin_cases k <;> simp [hi₀]
      simpa only [← hv] using hroots i₀
    · have hc : S.card = (Finset.univ.erase i₀).card := by
        apply Finset.card_image_iff.mpr
        intro i hi k hk h
        exact hinj i k (hy' i (Finset.mem_erase.mp hi).1)
          (hy' k (Finset.mem_erase.mp hk).1) h
      have he := Finset.card_erase_add_one (Finset.mem_univ i₀)
      rw [Finset.card_univ] at he
      omega

end EvenOrderMDS.BinaryRootBound
