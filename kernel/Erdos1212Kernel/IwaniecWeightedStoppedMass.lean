import Erdos1212Kernel.IwaniecWeightedTreeDefect

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Positive majorant for every stopped or terminal branch of the weighted
Iwaniec tree.  Allowed branches recurse with absolute factor weight; a stopped
branch pays the full omitted Euler tail. -/
def iwaniecWeightedStoppedMass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) : List α → List α → Real
  | _selected, [] => 0
  | selected, factor :: tail =>
      let skipped := iwaniecWeightedStoppedMass r evenRestriction
        factorWeight selected tail
      if selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        skipped + |factorWeight factor| *
          iwaniecWeightedStoppedMass r evenRestriction factorWeight
            (selected ++ [factor]) tail
      else
        skipped + |factorWeight factor| *
          |iwaniecListEulerProduct factorWeight tail|

theorem iwaniecWeightedStoppedMass_nonneg
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    0 ≤ iwaniecWeightedStoppedMass r evenRestriction factorWeight
      selected tail := by
  induction tail generalizing selected with
  | nil => simp [iwaniecWeightedStoppedMass]
  | cons factor tail ih =>
      rw [iwaniecWeightedStoppedMass]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [if_pos hselect]
        exact add_nonneg (ih selected)
          (mul_nonneg (abs_nonneg _) (ih (selected ++ [factor])))
      · rw [if_neg hselect]
        exact add_nonneg (ih selected)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The exact stopped-tree deficit is bounded by the positive stopped mass. -/
theorem abs_iwaniecWeightedTreeDefect_le_stoppedMass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    |iwaniecWeightedTreeDefect r evenRestriction factorWeight selected tail| ≤
      iwaniecWeightedStoppedMass r evenRestriction factorWeight selected tail := by
  induction tail generalizing selected with
  | nil =>
      simp [iwaniecWeightedTreeDefect, iwaniecWeightedStoppedMass,
        iwaniecListEulerProduct, iwaniecWeightedLowerTreeSum]
  | cons factor tail ih =>
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [iwaniecWeightedTreeDefect_cons_of_select
          r evenRestriction factorWeight selected factor tail hselect,
        iwaniecWeightedStoppedMass, if_pos hselect]
        calc
          |iwaniecWeightedTreeDefect r evenRestriction factorWeight selected tail -
              factorWeight factor *
                iwaniecWeightedTreeDefect r evenRestriction factorWeight
                  (selected ++ [factor]) tail| ≤
            |iwaniecWeightedTreeDefect r evenRestriction factorWeight
                selected tail| +
              |factorWeight factor *
                iwaniecWeightedTreeDefect r evenRestriction factorWeight
                  (selected ++ [factor]) tail| := abs_sub _ _
          _ = |iwaniecWeightedTreeDefect r evenRestriction factorWeight
                selected tail| +
              |factorWeight factor| *
                |iwaniecWeightedTreeDefect r evenRestriction factorWeight
                  (selected ++ [factor]) tail| := by rw [abs_mul]
          _ ≤ iwaniecWeightedStoppedMass r evenRestriction factorWeight
                selected tail +
              |factorWeight factor| *
                iwaniecWeightedStoppedMass r evenRestriction factorWeight
                  (selected ++ [factor]) tail := by
            gcongr
            · exact ih selected
            · exact ih (selected ++ [factor])
          _ = _ := rfl
      · rw [iwaniecWeightedTreeDefect_cons_of_not_select
          r evenRestriction factorWeight selected factor tail hselect,
        iwaniecWeightedStoppedMass, if_neg hselect]
        calc
          |iwaniecWeightedTreeDefect r evenRestriction factorWeight selected tail -
              factorWeight factor *
                iwaniecListEulerProduct factorWeight tail| ≤
            |iwaniecWeightedTreeDefect r evenRestriction factorWeight
                selected tail| +
              |factorWeight factor *
                iwaniecListEulerProduct factorWeight tail| := abs_sub _ _
          _ = |iwaniecWeightedTreeDefect r evenRestriction factorWeight
                selected tail| +
              |factorWeight factor| *
                |iwaniecListEulerProduct factorWeight tail| := by rw [abs_mul]
          _ ≤ iwaniecWeightedStoppedMass r evenRestriction factorWeight
                selected tail +
              |factorWeight factor| *
                |iwaniecListEulerProduct factorWeight tail| := by
            gcongr
            exact ih selected
          _ = _ := rfl

/-- Main-tree lower bound reduced to the positive stopped mass. -/
theorem euler_sub_stoppedMass_le_iwaniecWeightedTree
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    iwaniecListEulerProduct factorWeight tail -
        iwaniecWeightedStoppedMass r evenRestriction factorWeight selected tail ≤
      iwaniecWeightedLowerTreeSum r evenRestriction factorWeight selected tail := by
  have habs := abs_iwaniecWeightedTreeDefect_le_stoppedMass
    r evenRestriction factorWeight selected tail
  have hself := le_abs_self
    (iwaniecWeightedTreeDefect r evenRestriction factorWeight selected tail)
  unfold iwaniecWeightedTreeDefect at habs hself
  linarith

end

end Erdos1212Kernel
