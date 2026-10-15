module

public import EvenOrderMDS.CoordinateRestriction
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public noncomputable section

/-! Prime, pairwise nondividing literal linear factors of an actual arc. -/

namespace EvenOrderMDS.ArcPolynomialFactors

open LinearCoordinates StandardArcProjection CoordinateRestriction
open scoped BigOperators

theorem prime_product_dvd {R ι : Type*} [CommMonoidWithZero R] [Fintype ι]
    (f : ι → R) (hprime : ∀ i, Prime (f i))
    (hdistinct : ∀ i j, i ≠ j → ¬ f i ∣ f j) (a : R) (hdiv : ∀ i, f i ∣ a) :
    (∏ i, f i) ∣ a := by
  classical
  have hprod (s : Finset ι) : (∏ i ∈ s, f i) ∣ a := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      obtain ⟨r, hr⟩ := ih
      have hpi := hdiv i
      rw [hr] at hpi
      have hnot : ¬ f i ∣ ∏ k ∈ s, f k := by
        intro h
        obtain ⟨k, hk, hdiv'⟩ := (hprime i).dvd_finset_prod_iff _ |>.mp h
        exact hdistinct i k (by intro heq; subst k; exact hi hk) hdiv'
      obtain ⟨t, ht⟩ := ((hprime i).dvd_or_dvd hpi).resolve_left hnot
      refine ⟨t, ?_⟩
      rw [hr, ht]
      ac_rfl
  exact hprod Finset.univ

variable {K : Type*} [Field K]

noncomputable def allFactors {r N : ℕ} (a : Fin N → Fin r → K) : MvPolynomial (Fin r) K :=
  ∏ i, linearForm (a i)

theorem allFactors_homogeneous {r N : ℕ} (a : Fin N → Fin r → K) :
    (allFactors a).IsHomogeneous N := by
  simpa [allFactors] using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => linearForm (a i)) (fun _ => 1) (fun i _ => linearForm_homogeneous (a i))

theorem old_line_prime {k N : ℕ} (hkn : k + 1 ≤ N + 1)
    (a : Fin (N + 1) → Fin (k + 1) → K) (ha : Arc.IsArc (K := K) (k + 1) a)
    (i : Fin (N + 1)) : Prime (linearForm (a i)) := by
  have hne := ArcContraction.column_ne_zero_of_enough_columns (by omega) hkn ha i
  obtain ⟨p, hp⟩ : ∃ p, a i p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  exact linearForm_prime (a i) p hp

theorem old_lines_nondividing {k N : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ N + 1)
    (a : Fin (N + 1) → Fin (k + 1) → K) (ha : Arc.IsArc (K := K) (k + 1) a)
    (i j : Fin (N + 1)) (hij : i ≠ j) : ¬ linearForm (a i) ∣ linearForm (a j) := by
  have hne := ArcContraction.column_ne_zero_of_enough_columns (by omega) hkn ha i
  obtain ⟨p, hp⟩ : ∃ p, a i p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
  have hproj := projected_columns_are_arc a ha i p hp
  have hnonzero := ArcContraction.column_ne_zero_of_enough_columns hk (by omega) hproj j'
  intro hdiv
  have hz := (restrictAlong_zero_iff (a i) p hp (linearForm (a j))).mpr hdiv
  rw [restrictAlong_linearForm] at hz
  apply hnonzero
  apply linearForm_injective
  simpa only [hj', map_zero] using hz

theorem allFactors_dvd_of_each {k N : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ N + 1)
    (a : Fin (N + 1) → Fin (k + 1) → K) (ha : Arc.IsArc (K := K) (k + 1) a)
    (f : MvPolynomial (Fin (k + 1)) K) (hdiv : ∀ i, linearForm (a i) ∣ f) : allFactors a ∣ f :=
  prime_product_dvd (fun i => linearForm (a i)) (old_line_prime hkn a ha)
    (old_lines_nondividing hk hkn a ha) f hdiv

theorem allFactors_ne_zero {k N : ℕ} (hkn : k + 1 ≤ N + 1)
    (a : Fin (N + 1) → Fin (k + 1) → K) (ha : Arc.IsArc (K := K) (k + 1) a) :
    allFactors a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (old_line_prime hkn a ha i).ne_zero)

end EvenOrderMDS.ArcPolynomialFactors
