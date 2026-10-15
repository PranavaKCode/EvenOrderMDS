module

public import EvenOrderMDS.ConcreteHeightBound

@[expose] public noncomputable section

/-! Concrete bounded common height spaces constructed directly from actual plane arcs. -/

namespace EvenOrderMDS.CommonHeightCapacity

open ConcreteShearInjection ConcreteHeightBound ShearPolynomials

variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

noncomputable def dataOfArc {n t M : ℕ} (hn : 1 ≤ n) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) : PlaneData K :=
  let henv := NormalizedPlaneEnvelope.exists_plane_envelope hn ht hsize hcard a ha
  let hpow := FiniteField.card K 2
  { n := n
    t := t
    M := M
    e := (Classical.choose hpow).val
    positive := hn
    deficiency := ht
    size := hsize
    exponent := (Classical.choose_spec hpow).2.symm.trans hcard
    card := (Classical.choose_spec hpow).2
    columns := a
    arc := ha
    envelope := Classical.choose henv
    degree := (Classical.choose_spec henv).1
    normalized := (Classical.choose_spec henv).2 }

theorem exists_bounded_common_height_space {n t M : ℕ} (hn : 2 ≤ n) (ht1 : 1 ≤ t) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a) :
    ∃ H : Submodule K (Fin M → K), Module.finrank K H ≤ t + 2 ∧
      (∀ s : Fin 3 → K, heights a s ∈ H) ∧
      ∀ h : Fin M → K, Arc.IsArc (K := K) 4 (LiftGeometry.columns a h) → h ∈ H := by
  let D := dataOfArc (by omega : 1 ≤ n) ht hsize hcard a ha
  refine ⟨D.heightSpace, heightSpace_capacity D ht1, ?_, ?_⟩
  · intro s
    exact ⟨D.shearMap s, rfl⟩
  · intro h hh
    exact CompatibleSpace.actual_lift_mem_heightSpace hn ht hsize hcard a ha
      D.envelope D.degree D.normalized h hh

theorem every_low_degree_lift_is_shear {n t M : ℕ} (hn : 2 ≤ n) (ht : t ≤ 1)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (h : Fin M → K) (hlift : Arc.IsArc (K := K) 4 (LiftGeometry.columns a h)) :
    ∃ s : Fin 3 → K, h = heights a s := by
  let D := dataOfArc (by omega : 1 ≤ n) (by omega : t ≤ n) hsize hcard a ha
  have hh : h ∈ D.heightSpace := CompatibleSpace.actual_lift_mem_heightSpace hn (by omega) hsize hcard a ha
    D.envelope D.degree D.normalized h hlift
  exact (D.mem_shearHeights ⟨h, hh⟩).mp (D.low_degree_heights_are_shears ht ⟨h, hh⟩)

theorem too_many_independent_compatible_rows {n t M : ℕ}
    (hn : 2 ≤ n) (ht1 : 1 ≤ t) (ht : t ≤ n)
    (hsize : M + t = 2 * n + 2) (hcard : Fintype.card K = 2 * n)
    (a : Fin M → Fin 3 → K) (ha : Arc.IsArc (K := K) 3 a)
    (rows : Fin (t + 3) → Fin M → K) (hrows : LinearIndependent K rows)
    (hmember : ∀ i, (∃ s : Fin 3 → K, rows i = heights a s) ∨
      Arc.IsArc (K := K) 4 (LiftGeometry.columns a (rows i))) : False := by
  obtain ⟨H, hcap, hshear, hlifts⟩ := exists_bounded_common_height_space hn ht1 ht hsize hcard a ha
  have hm (i : Fin (t + 3)) : rows i ∈ H := by
    rcases hmember i with ⟨s, hs⟩ | hl
    · rw [hs]
      exact hshear s
    · exact hlifts (rows i) hl
  have hi : LinearIndependent K (fun i : Fin (t + 3) => (⟨rows i, hm i⟩ : H)) :=
    LinearIndependent.of_comp H.subtype hrows
  have hlow := hi.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hlow
  omega

end EvenOrderMDS.CommonHeightCapacity
