module

public import EvenOrderMDS.CompatibleCorrection
public import EvenOrderMDS.CommonHeight

@[expose] public noncomputable section

/-! The concrete compatibility subspace, including the negative-degree guard. -/

namespace EvenOrderMDS.CompatibleSpace

open CompatiblePolynomial ActualLiftCompatibility

variable {K : Type*} [Field K]

noncomputable def heightTermMap {M : ℕ} (a : Fin M → Fin 3 → K) :
    (Fin M → K) →ₗ[K] MvPolynomial (Fin 3) K where
  toFun := heightTerm a
  map_add' := by intro h k; simp [heightTerm, add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c h; simp [heightTerm, smul_smul, Finset.smul_sum]

noncomputable def polynomialMap {M : ℕ} (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    ((Fin M → K) × MvPolynomial (Fin 3) K) →ₗ[K] MvPolynomial (Fin 3) K where
  toFun p := polynomial a F p.1 p.2
  map_add' := by
    intro p q
    change _ + heightTermMap a (p.1 + q.1) * F = _
    rw [map_add]
    change PlaneArcColon.lineProduct a * (p.2 + q.2) +
      (heightTerm a p.1 + heightTerm a q.1) * F = _
    simp only [polynomial]
    ring
  map_smul' := by
    intro c p
    change _ + heightTermMap a (c • p.1) * F = _
    rw [map_smul]
    change PlaneArcColon.lineProduct a * (c • p.2) + (c • heightTerm a p.1) * F = _
    simp [polynomial, smul_add]

noncomputable def pairs {M : ℕ} (t : ℕ) (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    Submodule K ((Fin M → K) × MvPolynomial (Fin 3) K) where
  carrier := {p | p.2.IsHomogeneous (t - 1) ∧ (t = 0 → p.2 = 0) ∧
    MixedParity.mixedThird (polynomialMap a F p) = 0}
  zero_mem' := by
    refine ⟨MvPolynomial.isHomogeneous_zero (Fin 3) K (t - 1), fun _ => rfl, ?_⟩
    rw [map_zero, map_zero]
  add_mem' := by
    intro p q hp hq
    refine ⟨hp.1.add hq.1, fun ht => ?_, ?_⟩
    · change p.2 + q.2 = 0
      rw [hp.2.1 ht, hq.2.1 ht, add_zero]
    · rw [map_add, map_add, hp.2.2, hq.2.2, add_zero]
  smul_mem' := by
    intro c p hp
    refine ⟨(MvPolynomial.homogeneousSubmodule (Fin 3) K (t - 1)).smul_mem c hp.1, fun ht => ?_, ?_⟩
    · change c • p.2 = 0
      rw [hp.2.1 ht, smul_zero]
    · rw [map_smul, map_smul, hp.2.2, smul_zero]

theorem mem_pairs {M t : ℕ} (a : Fin M → Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (p : (Fin M → K) × MvPolynomial (Fin 3) K) :
    p ∈ pairs t a F ↔ p.2.IsHomogeneous (t - 1) ∧ (t = 0 → p.2 = 0) ∧
      MixedParity.mixedThird (polynomial a F p.1 p.2) = 0 := Iff.rfl

theorem heightProjection_injective [CharP K 2] [Finite K] {n t M : ℕ}
    (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) (F : MvPolynomial (Fin 3) K) :
    Function.Injective (CommonHeight.heightProjection (pairs t a F)) := by
  intro p q heq
  have hh : p.val.1 = q.val.1 := heq
  apply Subtype.ext
  apply Prod.ext hh
  exact CompatibleCorrection.correction_unique hn ht hsize a ha F p.val.1 p.val.2 q.val.2
    p.property.1 q.property.1 p.property.2.1 q.property.2.1 p.property.2.2
    (by rw [hh]; exact q.property.2.2)

theorem pairs_finiteDimensional [CharP K 2] [Finite K] {n t M : ℕ}
    (hn : 1 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) (F : MvPolynomial (Fin 3) K) :
    FiniteDimensional K (pairs t a F) :=
  FiniteDimensional.of_injective (CommonHeight.heightProjection (pairs t a F))
    (heightProjection_injective hn ht hsize a ha F)

theorem actual_lift_mem_heightSpace [CharP K 2] [Fintype K]
    {n t M : ℕ} (hn : 2 ≤ n) (ht : t ≤ n) (hsize : M + t = 2 * n + 2)
    (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous t)
    (hFv : NormalizedPlaneHighest.HasNormalizedValues a F)
    (h : Fin M → K) (hlift : Arc.IsArc (K := K) 4 (LiftGeometry.columns a h)) :
    h ∈ CommonHeight.heightSpace (pairs t a F) := by
  obtain ⟨Q, hQ, hQ0, hc⟩ := every_actual_lift_compatible hn ht hsize hcard a ha F hF hFv h hlift
  exact ⟨⟨(h, Q), hQ, hQ0, hc⟩, rfl⟩

end EvenOrderMDS.CompatibleSpace
