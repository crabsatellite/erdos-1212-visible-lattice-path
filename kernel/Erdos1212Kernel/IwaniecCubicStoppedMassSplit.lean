import Erdos1212Kernel.IwaniecCubicStopDecomposition

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Positive mass charged specifically to the terminal `2r` cut. -/
def iwaniecCubicTerminalMass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) : List α → List α → Real
  | _selected, [] => 0
  | selected, factor :: tail =>
      let skipped := iwaniecCubicTerminalMass r evenRestriction
        factorWeight selected tail
      if hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        skipped + |factorWeight factor| *
          iwaniecCubicTerminalMass r evenRestriction factorWeight
            (selected ++ [factor]) tail
      else if 2 * r ≤ selected.length + 1 then
        skipped + |factorWeight factor| *
          |iwaniecListEulerProduct factorWeight tail|
      else
        skipped

/-- Positive mass charged to a cubic failure while depth remains available. -/
def iwaniecCubicThresholdMass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) : List α → List α → Real
  | _selected, [] => 0
  | selected, factor :: tail =>
      let skipped := iwaniecCubicThresholdMass r evenRestriction
        factorWeight selected tail
      if hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        skipped + |factorWeight factor| *
          iwaniecCubicThresholdMass r evenRestriction factorWeight
            (selected ++ [factor]) tail
      else if 2 * r ≤ selected.length + 1 then
        skipped
      else
        skipped + |factorWeight factor| *
          |iwaniecListEulerProduct factorWeight tail|

theorem iwaniecWeightedStoppedMass_eq_terminal_add_threshold
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    iwaniecWeightedStoppedMass r evenRestriction factorWeight selected tail =
      iwaniecCubicTerminalMass r evenRestriction factorWeight selected tail +
        iwaniecCubicThresholdMass r evenRestriction factorWeight selected tail := by
  induction tail generalizing selected with
  | nil =>
      simp [iwaniecWeightedStoppedMass, iwaniecCubicTerminalMass,
        iwaniecCubicThresholdMass]
  | cons factor tail ih =>
      rw [iwaniecWeightedStoppedMass, iwaniecCubicTerminalMass,
        iwaniecCubicThresholdMass]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [if_pos hselect, dif_pos hselect, dif_pos hselect]
        rw [ih selected, ih (selected ++ [factor])]
        ring
      · rw [if_neg hselect, dif_neg hselect, dif_neg hselect]
        by_cases hdepth : 2 * r ≤ selected.length + 1
        · rw [if_pos hdepth, if_pos hdepth]
          rw [ih selected]
          ring
        · rw [if_neg hdepth, if_neg hdepth]
          rw [ih selected]
          ring

theorem iwaniecCubicTerminalMass_nonneg
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    0 ≤ iwaniecCubicTerminalMass r evenRestriction factorWeight selected tail := by
  induction tail generalizing selected with
  | nil => simp [iwaniecCubicTerminalMass]
  | cons factor tail ih =>
      rw [iwaniecCubicTerminalMass]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [dif_pos hselect]
        exact add_nonneg (ih selected)
          (mul_nonneg (abs_nonneg _) (ih (selected ++ [factor])))
      · rw [dif_neg hselect]
        by_cases hdepth : 2 * r ≤ selected.length + 1
        · rw [if_pos hdepth]
          exact add_nonneg (ih selected)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        · rw [if_neg hdepth]
          exact ih selected

theorem iwaniecCubicThresholdMass_nonneg
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    0 ≤ iwaniecCubicThresholdMass r evenRestriction factorWeight selected tail := by
  induction tail generalizing selected with
  | nil => simp [iwaniecCubicThresholdMass]
  | cons factor tail ih =>
      rw [iwaniecCubicThresholdMass]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [dif_pos hselect]
        exact add_nonneg (ih selected)
          (mul_nonneg (abs_nonneg _) (ih (selected ++ [factor])))
      · rw [dif_neg hselect]
        by_cases hdepth : 2 * r ≤ selected.length + 1
        · rw [if_pos hdepth]
          exact ih selected
        · rw [if_neg hdepth]
          exact add_nonneg (ih selected)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- If the remaining finite pool cannot reach depth `2r`, terminal mass is
identically zero. -/
theorem iwaniecCubicTerminalMass_eq_zero_of_totalDepth
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α)
    (hdepth : selected.length + tail.length < 2 * r) :
    iwaniecCubicTerminalMass r evenRestriction factorWeight selected tail = 0 := by
  induction tail generalizing selected with
  | nil => simp [iwaniecCubicTerminalMass]
  | cons factor tail ih =>
      simp only [List.length_cons] at hdepth
      rw [iwaniecCubicTerminalMass]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [dif_pos hselect]
        rw [ih selected (by omega)]
        rw [ih (selected ++ [factor]) (by
          simp only [List.length_append, List.length_singleton]
          omega)]
        ring
      · rw [dif_neg hselect]
        have hnotTerminal : ¬ 2 * r ≤ selected.length + 1 := by
          omega
        rw [if_neg hnotTerminal]
        exact ih selected (by omega)

end

end Erdos1212Kernel
