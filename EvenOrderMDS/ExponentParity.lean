module

public import EvenOrderMDS.LinearCoordinates
public import Lean.Elab.Tactic.Omega

@[expose] public noncomputable section

/-! Exact exponent division into its parity vector and twice its half. -/

namespace EvenOrderMDS.ExponentParity

open scoped BigOperators

variable {ι : Type*}

noncomputable def half (d : ι →₀ ℕ) : ι →₀ ℕ := d.mapRange (fun n => n / 2) (by decide)

noncomputable def remainder (d : ι →₀ ℕ) : ι →₀ ℕ := d.mapRange (fun n => n % 2) (by decide)

def bits (d : ι →₀ ℕ) : ι → Fin 2 := fun i => ⟨d i % 2, Nat.mod_lt _ (by decide)⟩

theorem half_apply (d : ι →₀ ℕ) (i : ι) : half d i = d i / 2 := rfl

theorem remainder_apply (d : ι →₀ ℕ) (i : ι) : remainder d i = d i % 2 := rfl

theorem exponent_decomposition (d : ι →₀ ℕ) : remainder d + 2 • half d = d := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, half_apply, remainder_apply]
  omega

theorem degree_decomposition (d : ι →₀ ℕ) :
    d.degree = (remainder d).degree + 2 * (half d).degree := by
  have h := congrArg Finsupp.degree (exponent_decomposition d)
  simpa only [two_smul, map_add, two_mul] using h.symm

variable [Fintype ι]

noncomputable def bitExponent (b : ι → Fin 2) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (b i : ℕ))

theorem bitExponent_apply (b : ι → Fin 2) (i : ι) : bitExponent b i = b i := by
  simp [bitExponent]

theorem bitExponent_bits (d : ι →₀ ℕ) : bitExponent (bits d) = remainder d := by
  ext i
  rw [bitExponent_apply, remainder_apply]
  rfl

theorem bitExponent_injective : Function.Injective (bitExponent (ι := ι)) := by
  intro b c h
  funext i
  apply Fin.ext
  have hi := congrArg (fun d : ι →₀ ℕ => d i) h
  simpa only [bitExponent_apply] using hi

theorem bits_half_injective {d e : ι →₀ ℕ} (hb : bits d = bits e) (hh : half d = half e) :
    d = e := by
  have hr : remainder d = remainder e := by rw [← bitExponent_bits, ← bitExponent_bits, hb]
  rw [← exponent_decomposition d, ← exponent_decomposition e, hr, hh]

theorem half_degree_of_parity {d : ι →₀ ℕ} {b : ι → Fin 2} {j : ℕ}
    (hd : d.degree = j) (hb : bits d = b) :
    (half d).degree = (j - (bitExponent b).degree) / 2 := by
  have h := degree_decomposition d
  rw [← bitExponent_bits, hb, hd] at h
  omega

end EvenOrderMDS.ExponentParity
