module

public import Lean

@[expose] public noncomputable section

/-!
# Numerical Hilbert-sequence lemmas

These theorems are about natural-number sequences. They do not assert that a
graded algebra satisfies their hypotheses. The bridge from graded Artinian
Gorenstein algebras to the recursive decomposition remains a separate task.

First written 2026-10-08. Consult STATUS.json for actual compilation status.
-/

namespace EvenOrderMDS.HilbertSequence

def FirstHalfMonotone (s : Nat) (h : Nat → Nat) : Prop :=
  ∀ i : Nat, 1 ≤ i → 2 * i ≤ s → h (i - 1) ≤ h i

def Symmetric (s : Nat) (h : Nat → Nat) : Prop :=
  ∀ i : Nat, i ≤ s → h i = h (s - i)

/-- Shift a natural-indexed sequence right, supplying the missing degree -1 by zero. -/
def shift (g : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then 0 else g (i - 1)

@[simp] theorem shift_zero (g : Nat → Nat) : shift g 0 = 0 := by
  simp [shift]

theorem shift_of_pos (g : Nat → Nat) {i : Nat} (hi : 1 ≤ i) :
    shift g i = g (i - 1) := by
  simp [shift, show i ≠ 0 by omega]

/-- A one-step binary no-rise rule propagates through the entire later tail. -/
theorem binary_no_rise_tail
    (e : Nat → Nat)
    (noRise : ∀ j : Nat, e j < j + 1 → e (j + 1) ≤ e j)
    {j t : Nat} (hj : e j < j + 1) (hjt : j ≤ t) :
    e t ≤ e j := by
  have haux : ∀ k : Nat, e (j + k) ≤ e j := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero] using (Nat.le_refl (e j))
    | succ k ih =>
        have hsmall : e (j + k) < (j + k) + 1 := by omega
        have hstep : e ((j + k) + 1) ≤ e (j + k) := noRise (j + k) hsmall
        have hindex : j + Nat.succ k = (j + k) + 1 := by omega
        rw [hindex]
        omega
  have hindex : j + (t - j) = t := by omega
  have ht := haux (t - j)
  rw [hindex] at ht
  exact ht

theorem zero_stays_zero
    (e : Nat → Nat)
    (noRise : ∀ j : Nat, e j < j + 1 → e (j + 1) ≤ e j)
    {j t : Nat} (hj : e j = 0) (hjt : j ≤ t) : e t = 0 := by
  have htail := binary_no_rise_tail e noRise (j := j) (t := t) (by omega) hjt
  omega

/-- The different symmetry centers rule out a first-half drop in h. -/
theorem first_half_monotone_of_shifted_symmetry
    (s : Nat) (h a e : Nat → Nat)
    (decomposition : ∀ j : Nat, j ≤ s → h j = a j + e j)
    (hSymmetry : Symmetric s h)
    (aShiftedSymmetry : ∀ j : Nat, 1 ≤ j → j ≤ s → a j = a (s + 1 - j))
    (aFirstHalf : FirstHalfMonotone s a)
    (binaryBound : ∀ j : Nat, e j ≤ j + 1)
    (noRise : ∀ j : Nat, e j < j + 1 → e (j + 1) ≤ e j) :
    FirstHalfMonotone s h := by
  intro i hi hhalf
  apply Classical.byContradiction
  intro hfailure
  have hdrop : h i < h (i - 1) := by omega
  have hprev := decomposition (i - 1) (by omega)
  have hhere := decomposition i (by omega)
  have amono := aFirstHalf i hi hhalf
  have eprevBound := binaryBound (i - 1)
  have esmall : e i < i + 1 := by omega
  have etail := binary_no_rise_tail e noRise (j := i) (t := s + 1 - i)
    esmall (by omega)
  have hmirror := hSymmetry (i - 1) (by omega)
  have hindex : s - (i - 1) = s + 1 - i := by omega
  rw [hindex] at hmirror
  have amirror := aShiftedSymmetry i hi (by omega)
  have hreflected := decomposition (s + 1 - i) (by omega)
  omega

/-- Shifting a sequence with center (s-1)/2 gives center (s+1)/2. -/
theorem shift_symmetry
    {s : Nat} (hs : 1 ≤ s) (g : Nat → Nat) (hg : Symmetric (s - 1) g)
    {i : Nat} (hi : 1 ≤ i) (his : i ≤ s) :
    shift g i = shift g (s + 1 - i) := by
  rw [shift_of_pos g hi, shift_of_pos g (by omega)]
  have hsym := hg (i - 1) (by omega)
  have hleft : (s - 1) - (i - 1) = s - i := by omega
  have hright : (s + 1 - i) - 1 = s - i := by omega
  rw [hleft] at hsym
  rw [hright]
  exact hsym

theorem shift_first_half_monotone
    {s : Nat} (g : Nat → Nat) (hg : FirstHalfMonotone (s - 1) g) :
    FirstHalfMonotone s (shift g) := by
  intro i hi hhalf
  by_cases hone : i = 1
  · subst i
    simp [shift]
  · have htwo : 2 ≤ i := by omega
    rw [shift_of_pos g (by omega), shift_of_pos g hi]
    have hmono := hg (i - 1) (by omega) (by omega)
    exact hmono

/--
An abstract induction interface for the full numerical argument. A future
graded-algebra bridge must prove `symmetry` and `decompose`; neither is hidden.

The family P may contain all Hilbert sequences of a class of algebras, but no
such identification is assumed by this theorem's name or definition.
-/
theorem first_half_monotone_of_recursive_binary_decomposition
    (P : Nat → (Nat → Nat) → Prop)
    (symmetry : ∀ s h, P s h → Symmetric s h)
    (decompose : ∀ s h, P s h → 2 ≤ s →
      ∃ g e : Nat → Nat,
        P (s - 1) g ∧
        (∀ j : Nat, j ≤ s → h j = shift g j + e j) ∧
        (∀ j : Nat, e j ≤ j + 1) ∧
        (∀ j : Nat, e j < j + 1 → e (j + 1) ≤ e j)) :
    ∀ s h, P s h → FirstHalfMonotone s h := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
      intro h hP i hi hhalf
      have hs : 2 ≤ s := by omega
      obtain ⟨g, e, hg, hdec, hbound, hnoRise⟩ := decompose s h hP hs
      have gmono : FirstHalfMonotone (s - 1) g := ih (s - 1) (by omega) g hg
      exact first_half_monotone_of_shifted_symmetry s h (shift g) e hdec
        (symmetry s h hP)
        (fun _ hi' his' => shift_symmetry (by omega) g (symmetry (s - 1) g hg) hi' his')
        (shift_first_half_monotone g gmono) hbound hnoRise i hi hhalf

end EvenOrderMDS.HilbertSequence
