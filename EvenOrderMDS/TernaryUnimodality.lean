module

public import EvenOrderMDS.StandardGeneration
public import EvenOrderMDS.LinearColonSequence

@[expose] public noncomputable section

/-!
# Symmetric first-half unimodality for an actual ternary generated algebra

The algebra is finite dimensional, internally graded, generated in degree one
by three explicit elements (zero or redundant generators are allowed), and has
a one-dimensional positive-degree socle. All quotient, pairing, binary, and
dimension-sequence bridges used in the induction are proved in imported modules.

The conversion from an embedding-dimension bound to three chosen generators is
separate. No MDS-code conclusion is part of this module.
-/

namespace EvenOrderMDS.TernaryUnimodality

universe u v

open StandardGeneration

section Generators

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]

theorem choose_nonzero_first_generator
    (A : ℕ → Submodule K R) (hne : A 1 ≠ ⊥)
    (hgens : ∃ x y z : R, A 1 = Submodule.span K ({x, y, z} : Set R)) :
    ∃ c y z : R, c ≠ 0 ∧ A 1 = Submodule.span K ({c, y, z} : Set R) := by
  obtain ⟨x, y, z, hgen⟩ := hgens
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · have hz : z ≠ 0 := by
        intro hz
        apply hne
        simpa [hx, hy, hz] using hgen
      refine ⟨z, x, y, hz, ?_⟩
      rw [hgen]
      congr 1
      ext r
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · refine ⟨y, x, z, hy, ?_⟩
      simpa only [Set.insert_comm x y] using hgen
  · exact ⟨x, y, z, hx, hgen⟩

theorem image_three_generators
    (A : ℕ → Submodule K R) (q : R →ₐ[K] S) (x y z : R)
    (hgen : A 1 = Submodule.span K ({x, y, z} : Set R)) :
    GradedImage.imagePieces A q 1 = Submodule.span K ({q x, q y, q z} : Set S) := by
  unfold GradedImage.imagePieces
  rw [hgen, Submodule.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem principal_quotient_two_generators
    (A : ℕ → Submodule K R) (c y z : R)
    (hgen : A 1 = Submodule.span K ({c, y, z} : Set R)) :
    GradedImage.imagePieces A (LinearColonSequence.principalMap (K := K) c) 1 =
      Submodule.span K ({LinearColonSequence.principalMap (K := K) c y,
        LinearColonSequence.principalMap (K := K) c z} : Set _) := by
  rw [image_three_generators A _ c y z hgen]
  have hc : LinearColonSequence.principalMap (K := K) c c = 0 :=
    (LinearColonSequence.principalMap_eq_zero_iff (K := K) c c).mpr (dvd_refl c)
  rw [hc]
  simp

end Generators

variable (K : Type u) [Field K]

/--
Concrete ternary standard-graded Gorenstein first-half monotonicity. The proof
is simultaneous in all finite algebras of the selected universe, so the actual
annihilator quotient can be used at each smaller socle degree.
-/
theorem first_half_monotone (s : ℕ) :
    ∀ (R : Type v) [CommRing R] [Algebra K R] [FiniteDimensional K R]
      (A : ℕ → Submodule K R) [GradedAlgebra A],
      StandardGenerated A →
      (∀ j : ℕ, s < j → A j = ⊥) →
      A s ≠ ⊥ →
      Module.finrank K (GradedSocle.positiveSocle A) = 1 →
      (∃ x y z : R, A 1 = Submodule.span K ({x, y, z} : Set R)) →
      HilbertSequence.FirstHalfMonotone s (fun j => Module.finrank K (A j)) := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
      intro R instRing instAlg instFinite A instGrading hstandard habove htop hsocle hgens i hi hhalf
      have hs : 2 ≤ s := by omega
      have hAone : A 1 ≠ ⊥ := degree_one_nonzero A hstandard (by omega) htop
      obtain ⟨c, y, z, hc0, hgen⟩ := choose_nonzero_first_generator A hAone hgens
      have hc : c ∈ A 1 := by
        rw [hgen]
        exact Submodule.subset_span (by simp)
      let G := R ⧸ ColonQuotient.annihilatorIdeal c
      let qG : R →ₐ[K] G := ColonQuotient.quotientMap (K := K) c
      let B : ℕ → Submodule K G := GradedImage.imagePieces A qG
      letI : GradedAlgebra B := ColonQuotient.quotientGrading A hc
      letI : FiniteDimensional K G :=
        FiniteDimensional.of_injective (ColonQuotient.quotientMul (K := K) c)
          (ColonQuotient.quotientMul_injective (K := K) c)
      have hBstandard : StandardGenerated B := image_standard_generated A hstandard qG
      have hBabove : ∀ j : ℕ, s - 1 < j → B j = ⊥ :=
        fun _ hj => ColonQuotient.quotient_piece_above_top A habove (by omega) hc hj
      have hBtop : B (s - 1) ≠ ⊥ :=
        ColonQuotient.quotient_top_nonzero A habove htop hsocle hc hc0
      have hBsocle : Module.finrank K (GradedSocle.positiveSocle B) = 1 :=
        ColonQuotient.quotient_socle_dimension A habove htop hsocle (by omega) hc hc0
      have hBgens : ∃ x y z : G, B 1 = Submodule.span K ({x, y, z} : Set G) :=
        ⟨qG c, qG y, qG z, image_three_generators A qG c y z hgen⟩
      let g : ℕ → ℕ := fun j => Module.finrank K (B j)
      have hgmono : HilbertSequence.FirstHalfMonotone (s - 1) g :=
        ih (s - 1) (by omega) G B hBstandard hBabove hBtop hBsocle hBgens
      let E := R ⧸ Ideal.span ({c} : Set R)
      let qE : R →ₐ[K] E := LinearColonSequence.principalMap (K := K) c
      let C : ℕ → Submodule K E := GradedImage.imagePieces A qE
      have hCstandard : StandardGenerated C := image_standard_generated A hstandard qE
      have hCgens : C 1 = Submodule.span K ({qE y, qE z} : Set E) :=
        principal_quotient_two_generators A c y z hgen
      let e : ℕ → ℕ := fun j => Module.finrank K (C j)
      have hbound : ∀ j : ℕ, e j ≤ j + 1 :=
        fun j => binary_hilbert_bound C hCstandard (qE y) (qE z) hCgens j
      have hnoRise : ∀ j : ℕ, e j < j + 1 → e (j + 1) ≤ e j :=
        fun _ hj => binary_hilbert_no_rise C hCstandard (qE y) (qE z) hCgens hj
      have hdec : ∀ j : ℕ, j ≤ s →
          Module.finrank K (A j) = HilbertSequence.shift g j + e j :=
        fun j _ => LinearColonSequence.hilbert_dimension_sequence A hc j
      have hsym : HilbertSequence.Symmetric s (fun j => Module.finrank K (A j)) :=
        fun _ hj => GradedPairing.complementary_finrank_eq A habove htop hsocle hj
      have hgsym : HilbertSequence.Symmetric (s - 1) g :=
        fun _ hj => GradedPairing.complementary_finrank_eq B hBabove hBtop hBsocle hj
      exact HilbertSequence.first_half_monotone_of_shifted_symmetry s
        (fun j => Module.finrank K (A j)) (HilbertSequence.shift g) e
        hdec hsym
        (fun _ hj hjs => HilbertSequence.shift_symmetry (by omega) g hgsym hj hjs)
        (HilbertSequence.shift_first_half_monotone g hgmono) hbound hnoRise i hi hhalf

end EvenOrderMDS.TernaryUnimodality
