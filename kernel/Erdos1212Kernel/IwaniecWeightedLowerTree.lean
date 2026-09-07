import Erdos1212Kernel.IwaniecLowerExpansion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- One ordered sublist contribution with an arbitrary multiplicative factor
weight.  The Iwaniec main term later takes `factorWeight p = 1 / p`. -/
def iwaniecWeightedContinuationTerm
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) : List α → List α → Real
  | _selected, [] => 1
  | selected, factor :: tail =>
      if selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        -(factorWeight factor *
          iwaniecWeightedContinuationTerm r evenRestriction factorWeight
            (selected ++ [factor]) tail)
      else
        0

def iwaniecWeightedExpansionSum
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) : Real :=
  (tail.sublists.map fun extension =>
    iwaniecWeightedContinuationTerm r evenRestriction factorWeight
      selected extension).sum

/-- Weighted form of Iwaniec's scanning recursion. -/
def iwaniecWeightedLowerTreeSum
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) : List α → List α → Real
  | _selected, [] => 1
  | selected, factor :: tail =>
      let skipped := iwaniecWeightedLowerTreeSum r evenRestriction
        factorWeight selected tail
      if selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        skipped - factorWeight factor *
          iwaniecWeightedLowerTreeSum r evenRestriction factorWeight
            (selected ++ [factor]) tail
      else
        skipped

theorem List.sum_map_neg_mul
    {α : Type*} (values : List α) (constant : Real)
    (weight : α → Real) :
    (values.map fun value => -(constant * weight value)).sum =
      -constant * (values.map weight).sum := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih, mul_add]

/-- The explicit weighted sublist sum and the paper's recursive main-term
tree are identical. -/
theorem iwaniecWeightedExpansionSum_eq_tree
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    iwaniecWeightedExpansionSum r evenRestriction factorWeight selected tail =
      iwaniecWeightedLowerTreeSum r evenRestriction factorWeight selected tail := by
  induction tail generalizing selected with
  | nil =>
      simp [iwaniecWeightedExpansionSum, iwaniecWeightedContinuationTerm,
        iwaniecWeightedLowerTreeSum]
  | cons factor tail ih =>
      rw [iwaniecWeightedExpansionSum, List.sublists_cons]
      change
        ((tail.sublists.flatMap fun extension =>
            [extension, factor :: extension]).map
          (fun extension =>
            iwaniecWeightedContinuationTerm r evenRestriction factorWeight
              selected extension)).sum = _
      rw [List.sum_map_flatMap_pair]
      change iwaniecWeightedExpansionSum r evenRestriction factorWeight
          selected tail +
        (tail.sublists.map fun extension =>
          iwaniecWeightedContinuationTerm r evenRestriction factorWeight
            selected (factor :: extension)).sum = _
      rw [ih, iwaniecWeightedLowerTreeSum]
      by_cases hselect :
          selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected factor)
      · rw [if_pos hselect]
        simp_rw [iwaniecWeightedContinuationTerm, if_pos hselect]
        rw [List.sum_map_neg_mul]
        change iwaniecWeightedLowerTreeSum r evenRestriction factorWeight
            selected tail + (-factorWeight factor) *
            iwaniecWeightedExpansionSum r evenRestriction factorWeight
              (selected ++ [factor]) tail = _
        rw [ih]
        ring
      · rw [if_neg hselect]
        simp_rw [iwaniecWeightedContinuationTerm, if_neg hselect]
        simp

def iwaniecListEulerProduct
    {α : Type*} (factorWeight : α → Real) (factors : List α) : Real :=
  (factors.map fun factor => 1 - factorWeight factor).prod

/-- With no cubic deletion and no depth truncation, the weighted tree is the
literal finite Euler product. -/
theorem iwaniecWeightedLowerTreeSum_eq_euler_of_depth
    {α : Type*} (r : Nat) (factorWeight : α → Real)
    (selected tail : List α)
    (hdepth : selected.length + tail.length < 2 * r) :
    iwaniecWeightedLowerTreeSum r (fun _selected _factor => true)
        factorWeight selected tail =
      iwaniecListEulerProduct factorWeight tail := by
  induction tail generalizing selected with
  | nil =>
      simp [iwaniecWeightedLowerTreeSum, iwaniecListEulerProduct]
  | cons factor tail ih =>
      simp only [List.length_cons] at hdepth
      rw [iwaniecWeightedLowerTreeSum]
      have hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ (true : Bool)) := by
        constructor
        · omega
        · simp
      rw [if_pos hselect]
      rw [ih selected (by omega)]
      rw [ih (selected ++ [factor]) (by
        simp only [List.length_append, List.length_singleton]
        omega)]
      simp [iwaniecListEulerProduct]
      ring

theorem iwaniecWeightedLowerTreeSum_root_eq_euler
    {α : Type*} (factorWeight : α → Real) (factors : List α) :
    iwaniecWeightedLowerTreeSum (factors.length + 1)
        (fun _selected _factor => true) factorWeight [] factors =
      iwaniecListEulerProduct factorWeight factors := by
  apply iwaniecWeightedLowerTreeSum_eq_euler_of_depth
  simp only [List.length_nil, zero_add]
  omega

end

end Erdos1212Kernel
