import Erdos1212Kernel.IwaniecLemma15

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

/-- The literal stopped tuple: all selections before the last pass,
and the last selection fails the active cubic condition. -/
def iwaniecCubicStoppedWord : Nat → Real → List Nat → Prop
  | _, _, [] => False
  | offset, level, p :: tail =>
      if tail = [] then ¬(Even offset ∨ (p : Real) ^ 3 < level)
      else (Even offset ∨ (p : Real) ^ 3 < level) ∧
        iwaniecCubicStoppedWord (offset + 1) (level / p) tail

/-- Exact reciprocal tuple weight. R is evaluated at the failed last
prime; earlier successful selections contribute their reciprocal factors. -/
def iwaniecStoppedWordWeight : Nat → Real → List Nat → Real
  | _, _, [] => 0
  | offset, level, p :: tail =>
      if Even offset ∨ (p : Real) ^ 3 < level then
        (p : Real)⁻¹ * iwaniecStoppedWordWeight (offset + 1) (level / p) tail
      else if tail = [] then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0

@[simp] theorem iwaniecCubicStoppedWord_nil (offset : Nat) (level : Real) :
    ¬iwaniecCubicStoppedWord offset level [] := by simp [iwaniecCubicStoppedWord]

theorem iwaniecCubicStoppedWord_singleton (offset : Nat) (level : Real) (p : Nat) :
    iwaniecCubicStoppedWord offset level [p] ↔ ¬(Even offset ∨ (p : Real) ^ 3 < level) := by
  simp [iwaniecCubicStoppedWord]

theorem iwaniecCubicStoppedWord_cons_cons (offset : Nat) (level : Real) (p q : Nat) (tail : List Nat) :
    iwaniecCubicStoppedWord offset level (p :: q :: tail) ↔
      (Even offset ∨ (p : Real) ^ 3 < level) ∧ iwaniecCubicStoppedWord (offset + 1) (level / p) (q :: tail) := by
  simp only [iwaniecCubicStoppedWord, List.cons_ne_nil, if_false]

theorem iwaniecCubicStoppedWord_add_two (offset : Nat) (level : Real) (word : List Nat) :
    iwaniecCubicStoppedWord (offset + 2) level word ↔ iwaniecCubicStoppedWord offset level word := by
  induction word generalizing offset level with
  | nil => simp
  | cons p tail ih =>
      have he : Even (offset + 2) ↔ Even offset := by
        simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
        omega
      simp only [iwaniecCubicStoppedWord, he]
      rw [show offset + 2 + 1 = (offset + 1) + 2 by omega, ih]

@[simp] theorem iwaniecStoppedWordWeight_nil (offset : Nat) (level : Real) :
    iwaniecStoppedWordWeight offset level [] = 0 := rfl

theorem iwaniecStoppedWordWeight_nonneg (offset : Nat) (level : Real) (word : List Nat) :
    0 ≤ iwaniecStoppedWordWeight offset level word := by
  induction word generalizing offset level with
  | nil => simp
  | cons p tail ih =>
      rw [iwaniecStoppedWordWeight]
      split
      · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (ih (offset + 1) (level / p))
      · split
        · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (iwaniecPaperR_pos _).le
        · exact le_rfl

theorem iwaniecStoppedWordWeight_le_inv_prod (offset : Nat) (level : Real) (word : List Nat) :
    iwaniecStoppedWordWeight offset level word ≤ (word.prod : Real)⁻¹ := by
  induction word generalizing offset level with
  | nil => simp
  | cons p tail ih =>
      have hp0 : 0 ≤ (p : Real)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
      rw [iwaniecStoppedWordWeight]
      by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
      · rw [if_pos hc]
        have hh := mul_le_mul_of_nonneg_left (ih (offset + 1) (level / p)) hp0
        simpa only [List.prod_cons, Nat.cast_mul, mul_inv_rev, mul_comm] using hh
      · rw [if_neg hc]
        by_cases ht : tail = []
        · subst tail
          simpa using mul_le_mul_of_nonneg_left (iwaniecPaperR_le_one (p : Real)) hp0
        · rw [if_neg ht]
          exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem iwaniecStoppedWordWeight_zero_of_not_stopped (offset : Nat) (level : Real) (word : List Nat)
    (hnot : ¬iwaniecCubicStoppedWord offset level word) : iwaniecStoppedWordWeight offset level word = 0 := by
  classical
  induction word generalizing offset level with
  | nil => simp
  | cons p tail ih =>
      rw [iwaniecStoppedWordWeight]
      by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
      · rw [if_pos hc]
        by_cases ht : tail = []
        · subst tail
          simp
        · have hchild : ¬iwaniecCubicStoppedWord (offset + 1) (level / p) tail := by
            intro hh
            exact hnot (by simpa only [iwaniecCubicStoppedWord, if_neg ht] using And.intro hc hh)
          rw [ih (offset + 1) (level / p) hchild, mul_zero]
      · rw [if_neg hc]
        by_cases ht : tail = []
        · subst tail
          exact (hnot (by simpa only [iwaniecCubicStoppedWord, if_true] using hc)).elim
        · rw [if_neg ht]

end

end Erdos1212Kernel
