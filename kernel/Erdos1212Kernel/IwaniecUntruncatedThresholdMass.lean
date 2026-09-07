import Erdos1212Kernel.IwaniecCubicStoppedMassSplit

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Pure first-cubic-failure mass with no artificial depth parameter. -/
def iwaniecUntruncatedThresholdMass
    {α : Type*} (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) : List α → List α → Real
  | _selected, [] => 0
  | selected, factor :: tail =>
      let skipped := iwaniecUntruncatedThresholdMass evenRestriction
        factorWeight selected tail
      if Even selected.length ∨ evenRestriction selected factor then
        skipped + |factorWeight factor| *
          iwaniecUntruncatedThresholdMass evenRestriction factorWeight
            (selected ++ [factor]) tail
      else
        skipped + |factorWeight factor| *
          |iwaniecListEulerProduct factorWeight tail|

theorem iwaniecUntruncatedThresholdMass_nonneg
    {α : Type*} (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    0 ≤ iwaniecUntruncatedThresholdMass evenRestriction factorWeight
      selected tail := by
  induction tail generalizing selected with
  | nil => simp [iwaniecUntruncatedThresholdMass]
  | cons factor tail ih =>
      rw [iwaniecUntruncatedThresholdMass]
      by_cases hselect : Even selected.length ∨
          evenRestriction selected factor
      · rw [if_pos hselect]
        exact add_nonneg (ih selected)
          (mul_nonneg (abs_nonneg _) (ih (selected ++ [factor])))
      · rw [if_neg hselect]
        exact add_nonneg (ih selected)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Below the finite-pool depth ceiling, threshold mass is exactly the pure
untruncated first-failure recursion. -/
theorem iwaniecCubicThresholdMass_eq_untruncated_of_totalDepth
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α)
    (hdepth : selected.length + tail.length < 2 * r) :
    iwaniecCubicThresholdMass r evenRestriction factorWeight selected tail =
      iwaniecUntruncatedThresholdMass evenRestriction factorWeight
        selected tail := by
  induction tail generalizing selected with
  | nil =>
      simp [iwaniecCubicThresholdMass,
        iwaniecUntruncatedThresholdMass]
  | cons factor tail ih =>
      simp only [List.length_cons] at hdepth
      rw [iwaniecCubicThresholdMass,
        iwaniecUntruncatedThresholdMass]
      have hselectionDepth : selected.length + 1 < 2 * r := by omega
      by_cases hchoice : Even selected.length ∨
          evenRestriction selected factor
      · have hselect : selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected factor) :=
          ⟨hselectionDepth, hchoice⟩
        rw [dif_pos hselect, if_pos hchoice]
        rw [ih selected (by omega)]
        rw [ih (selected ++ [factor]) (by
          simp only [List.length_append, List.length_singleton]
          omega)]
      · have hnotSelect : ¬(selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected factor)) := by
          intro hselect
          exact hchoice hselect.2
        rw [dif_neg hnotSelect]
        have hnotTerminal : ¬2 * r ≤ selected.length + 1 := by omega
        rw [if_neg hnotTerminal, if_neg hchoice]
        rw [ih selected (by omega)]

end

end Erdos1212Kernel
