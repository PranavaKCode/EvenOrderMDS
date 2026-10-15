module

public import EvenOrderMDS.LinearCoordinates
public import Mathlib.Data.Finset.Powerset

@[expose] public noncomputable section

/-! Literal homogeneous interpolation at star points of a finite arrangement. -/

namespace EvenOrderMDS.StarInterpolation

open scoped BigOperators

variable {K σ ι : Type*} [Field K] [DecidableEq ι]

noncomputable def basisPolynomial (L : ι → MvPolynomial σ K) (E S : Finset ι) :
    MvPolynomial σ K := ∏ i ∈ E \ S, L i

theorem basisPolynomial_homogeneous (L : ι → MvPolynomial σ K)
    (hL : ∀ i, (L i).IsHomogeneous 1) (E S : Finset ι) (hS : S ⊆ E) :
    (basisPolynomial L E S).IsHomogeneous (E.card - S.card) := by
  have h := MvPolynomial.IsHomogeneous.prod (E \ S) L (fun _ => 1) (fun i _ => hL i)
  simpa [basisPolynomial, Finset.card_sdiff_of_subset hS] using h

theorem basisPolynomial_eval_ne_zero (L : ι → MvPolynomial σ K) (E S : Finset ι)
    (p : σ → K) (hn : ∀ i ∈ E \ S, MvPolynomial.eval p (L i) ≠ 0) :
    MvPolynomial.eval p (basisPolynomial L E S) ≠ 0 := by
  classical
  rw [basisPolynomial, map_prod]
  exact Finset.prod_ne_zero_iff.mpr hn

theorem missing_label {E S T : Finset ι} (hS : S ⊆ E)
    (hcard : S.card = T.card) (hne : S ≠ T) : ∃ i ∈ E \ T, i ∈ S := by
  have hn : ¬ S ⊆ T := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hcard.ge)
  obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp hn
  exact ⟨i, Finset.mem_sdiff.mpr ⟨hS hi, hit⟩, hi⟩

theorem basisPolynomial_eval_zero (L : ι → MvPolynomial σ K) {E S T : Finset ι}
    (hS : S ⊆ E) (hcard : S.card = T.card) (hne : S ≠ T)
    (p : σ → K) (hz : ∀ i ∈ S, MvPolynomial.eval p (L i) = 0) :
    MvPolynomial.eval p (basisPolynomial L E T) = 0 := by
  classical
  obtain ⟨i, hi, his⟩ := missing_label hS hcard hne
  rw [basisPolynomial, map_prod]
  exact Finset.prod_eq_zero hi (hz i his)

noncomputable def interpolate (L : ι → MvPolynomial σ K) (E : Finset ι) (k : ℕ)
    (p : Finset ι → σ → K) (value : Finset ι → K) : MvPolynomial σ K :=
  ∑ S ∈ E.powersetCard k,
    (value S / MvPolynomial.eval (p S) (basisPolynomial L E S)) • basisPolynomial L E S

theorem interpolate_homogeneous (L : ι → MvPolynomial σ K)
    (hL : ∀ i, (L i).IsHomogeneous 1) (E : Finset ι) (k : ℕ)
    (p : Finset ι → σ → K) (value : Finset ι → K) :
    (interpolate L E k p value).IsHomogeneous (E.card - k) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro S hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  apply (MvPolynomial.homogeneousSubmodule σ K (E.card - k)).smul_mem
  simpa only [hcard, MvPolynomial.mem_homogeneousSubmodule] using
    basisPolynomial_homogeneous L hL E S hsub

theorem interpolate_values (L : ι → MvPolynomial σ K) (E : Finset ι) (k : ℕ)
    (p : Finset ι → σ → K) (value : Finset ι → K)
    (hzero : ∀ S ∈ E.powersetCard k, ∀ i ∈ S, MvPolynomial.eval (p S) (L i) = 0)
    (hne : ∀ S ∈ E.powersetCard k, ∀ i ∈ E \ S, MvPolynomial.eval (p S) (L i) ≠ 0)
    (S : Finset ι) (hS : S ∈ E.powersetCard k) :
    MvPolynomial.eval (p S) (interpolate L E k p value) = value S := by
  classical
  rw [interpolate, map_sum, Finset.sum_eq_single S]
  · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      div_mul_cancel₀ _ (basisPolynomial_eval_ne_zero L E S (p S) (hne S hS))]
  · intro T hT hTS
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      basisPolynomial_eval_zero L (Finset.mem_powersetCard.mp hS).1
        ((Finset.mem_powersetCard.mp hS).2.trans (Finset.mem_powersetCard.mp hT).2.symm)
        hTS.symm (p S) (hzero S hS), mul_zero]
  · exact fun h => (h hS).elim

end EvenOrderMDS.StarInterpolation
