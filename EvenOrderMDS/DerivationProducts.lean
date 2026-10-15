module

public import EvenOrderMDS.LocalProductDerivatives

@[expose] public noncomputable section

/-! Finite product rule with literal complementary factors. -/

namespace EvenOrderMDS.DerivationProducts

open scoped BigOperators

variable {K R ι : Type*} [Field K] [CommRing R] [Algebra K R] [DecidableEq ι]

theorem product_rule (D : Derivation K R R) (f : ι → R) (s : Finset ι) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, smul_eq_mul, smul_eq_mul, ih,
      Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum, add_comm]
    congr 1
    · exact mul_comm _ _
    · apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by intro h; exact ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hai, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring

end EvenOrderMDS.DerivationProducts
