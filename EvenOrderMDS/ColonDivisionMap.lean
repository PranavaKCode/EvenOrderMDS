module

public import EvenOrderMDS.HomogeneousDivision
public import EvenOrderMDS.CriticalColon

@[expose] public noncomputable section

/-! Actual semilinear division into the concrete homogeneous colon component. -/

namespace EvenOrderMDS.ColonDivisionMap

open PowerIdeal TruncatedGrading TruncatedColon CriticalColon

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def value {n d : ℕ} {C : PolynomialRing K} (g : component n C d) : PolynomialRing K := g.val.val

theorem value_injective {n d : ℕ} {C : PolynomialRing K} :
    Function.Injective (value : component n C d → PolynomialRing K) := by
  intro g h heq
  exact Subtype.ext (Subtype.ext heq)

theorem exists_division {n m d : ℕ} (C : PolynomialRing K) (hC : C.IsHomogeneous m)
    (σ : K ≃+* K) (φ : V →ₛₗ[σ.toRingHom] PolynomialRing K)
    (hdegree : ∀ v, (φ v).IsHomogeneous (m + d))
    (hI : ∀ v, φ v ∈ powerIdeal (K := K) n) (hdiv : ∀ v, C ∣ φ v) (v : V) :
    ∃ g : component n C d, C * value g = φ v := by
  letI : GradedAlgebra (polynomialPieces K) := MvPolynomial.gradedAlgebra
  obtain ⟨g, hg, heq⟩ := HomogeneousDivision.exists_homogeneous_quotient
    (polynomialPieces K) hC (hdegree v) (hdiv v)
  refine ⟨⟨⟨g, hg⟩, ?_⟩, heq.symm⟩
  change C * g ∈ powerIdeal (K := K) n
  rw [← heq]
  exact hI v

noncomputable def quotientValue {n m d : ℕ} (C : PolynomialRing K) (hC : C.IsHomogeneous m)
    (σ : K ≃+* K) (φ : V →ₛₗ[σ.toRingHom] PolynomialRing K)
    (hdegree : ∀ v, (φ v).IsHomogeneous (m + d))
    (hI : ∀ v, φ v ∈ powerIdeal (K := K) n) (hdiv : ∀ v, C ∣ φ v) (v : V) : component n C d :=
  Classical.choose (exists_division C hC σ φ hdegree hI hdiv v)

theorem quotientValue_spec {n m d : ℕ} (C : PolynomialRing K) (hC : C.IsHomogeneous m)
    (σ : K ≃+* K) (φ : V →ₛₗ[σ.toRingHom] PolynomialRing K)
    (hdegree : ∀ v, (φ v).IsHomogeneous (m + d))
    (hI : ∀ v, φ v ∈ powerIdeal (K := K) n) (hdiv : ∀ v, C ∣ φ v) (v : V) :
    C * value (quotientValue C hC σ φ hdegree hI hdiv v) = φ v :=
  Classical.choose_spec (exists_division C hC σ φ hdegree hI hdiv v)

noncomputable def divisionMap {n m d : ℕ} (C : PolynomialRing K) (hC : C.IsHomogeneous m) (hCne : C ≠ 0)
    (σ : K ≃+* K) (φ : V →ₛₗ[σ.toRingHom] PolynomialRing K)
    (hdegree : ∀ v, (φ v).IsHomogeneous (m + d))
    (hI : ∀ v, φ v ∈ powerIdeal (K := K) n) (hdiv : ∀ v, C ∣ φ v) : V →ₛₗ[σ.toRingHom] component n C d where
  toFun := quotientValue C hC σ φ hdegree hI hdiv
  map_add' := by
    intro v w
    apply value_injective
    apply mul_left_cancel₀ hCne
    change C * value (quotientValue C hC σ φ hdegree hI hdiv (v + w)) =
      C * (value (quotientValue C hC σ φ hdegree hI hdiv v) + value (quotientValue C hC σ φ hdegree hI hdiv w))
    rw [mul_add, quotientValue_spec, quotientValue_spec, quotientValue_spec, map_add]
  map_smul' := by
    intro c v
    apply value_injective
    apply mul_left_cancel₀ hCne
    change C * value (quotientValue C hC σ φ hdegree hI hdiv (c • v)) =
      C * (σ c • value (quotientValue C hC σ φ hdegree hI hdiv v))
    rw [mul_smul_comm, quotientValue_spec, quotientValue_spec, φ.map_smulₛₗ]
    rfl

theorem divisionMap_spec {n m d : ℕ} (C : PolynomialRing K) (hC : C.IsHomogeneous m) (hCne : C ≠ 0)
    (σ : K ≃+* K) (φ : V →ₛₗ[σ.toRingHom] PolynomialRing K)
    (hdegree : ∀ v, (φ v).IsHomogeneous (m + d))
    (hI : ∀ v, φ v ∈ powerIdeal (K := K) n) (hdiv : ∀ v, C ∣ φ v) (v : V) :
    C * value (divisionMap C hC hCne σ φ hdegree hI hdiv v) = φ v :=
  quotientValue_spec C hC σ φ hdegree hI hdiv v

theorem divisionMap_eq_zero_iff {n m d : ℕ} (C : PolynomialRing K) (hC : C.IsHomogeneous m) (hCne : C ≠ 0)
    (σ : K ≃+* K) (φ : V →ₛₗ[σ.toRingHom] PolynomialRing K)
    (hdegree : ∀ v, (φ v).IsHomogeneous (m + d))
    (hI : ∀ v, φ v ∈ powerIdeal (K := K) n) (hdiv : ∀ v, C ∣ φ v) (v : V) :
    divisionMap C hC hCne σ φ hdegree hI hdiv v = 0 ↔ φ v = 0 := by
  have hs := divisionMap_spec C hC hCne σ φ hdegree hI hdiv v
  constructor
  · intro h
    rw [h] at hs
    exact hs.symm.trans (mul_zero C)
  · intro h
    apply value_injective
    apply mul_left_cancel₀ hCne
    change C * value (divisionMap C hC hCne σ φ hdegree hI hdiv v) = C * 0
    rw [hs, h, mul_zero]

end EvenOrderMDS.ColonDivisionMap
