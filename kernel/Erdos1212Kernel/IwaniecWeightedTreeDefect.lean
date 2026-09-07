import Erdos1212Kernel.IwaniecWeightedLowerTree

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

/-- Euler-product deficit of the finite Iwaniec weighted tree. -/
def iwaniecWeightedTreeDefect
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) : Real :=
  iwaniecListEulerProduct factorWeight tail -
    iwaniecWeightedLowerTreeSum r evenRestriction factorWeight selected tail

@[simp]
theorem iwaniecWeightedTreeDefect_nil
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected : List α) :
    iwaniecWeightedTreeDefect r evenRestriction factorWeight selected [] = 0 := by
  simp [iwaniecWeightedTreeDefect, iwaniecListEulerProduct,
    iwaniecWeightedLowerTreeSum]

theorem iwaniecListEulerProduct_cons
    {α : Type*} (factorWeight : α → Real) (factor : α)
    (tail : List α) :
    iwaniecListEulerProduct factorWeight (factor :: tail) =
      (1 - factorWeight factor) *
        iwaniecListEulerProduct factorWeight tail := by
  simp [iwaniecListEulerProduct]

/-- Allowed selections transport the deficit with the same alternating
recursion as Iwaniec's `S/T` identities. -/
theorem iwaniecWeightedTreeDefect_cons_of_select
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected : List α) (factor : α)
    (tail : List α)
    (hselect : selected.length + 1 < 2 * r ∧
      (Even selected.length ∨ evenRestriction selected factor)) :
    iwaniecWeightedTreeDefect r evenRestriction factorWeight selected
        (factor :: tail) =
      iwaniecWeightedTreeDefect r evenRestriction factorWeight selected tail -
        factorWeight factor *
          iwaniecWeightedTreeDefect r evenRestriction factorWeight
            (selected ++ [factor]) tail := by
  rw [iwaniecWeightedTreeDefect, iwaniecListEulerProduct_cons,
    iwaniecWeightedLowerTreeSum, if_pos hselect]
  unfold iwaniecWeightedTreeDefect
  ring

/-- A stopped selection contributes its full omitted Euler branch.  This one
identity simultaneously records cubic stops and the terminal `2r` cut. -/
theorem iwaniecWeightedTreeDefect_cons_of_not_select
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected : List α) (factor : α)
    (tail : List α)
    (hselect : ¬(selected.length + 1 < 2 * r ∧
      (Even selected.length ∨ evenRestriction selected factor))) :
    iwaniecWeightedTreeDefect r evenRestriction factorWeight selected
        (factor :: tail) =
      iwaniecWeightedTreeDefect r evenRestriction factorWeight selected tail -
        factorWeight factor * iwaniecListEulerProduct factorWeight tail := by
  rw [iwaniecWeightedTreeDefect, iwaniecListEulerProduct_cons,
    iwaniecWeightedLowerTreeSum, if_neg hselect]
  unfold iwaniecWeightedTreeDefect
  ring

end

end Erdos1212Kernel
