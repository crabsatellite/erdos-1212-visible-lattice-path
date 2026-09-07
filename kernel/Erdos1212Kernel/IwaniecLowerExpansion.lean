import Erdos1212Kernel.IwaniecLowerTree
import Mathlib.Data.List.Sublists

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

/-- Contribution of one ordered sublist to Iwaniec's lower expansion.  The
recursive definition keeps the original quantifier order: after every chosen
factor, the next restriction is evaluated against the entire chosen prefix. -/
def iwaniecLowerContinuationTerm
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool) :
    List α → List α → Int
  | _selected, [] => 1
  | selected, factor :: tail =>
      if selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        -iwaniecLowerContinuationTerm r evenRestriction
          (selected ++ [factor]) tail
      else
        0

/-- The explicit alternating sublist expansion consumed by the recursive
lower sieve. -/
def iwaniecLowerExpansionSum
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected tail : List α) : Int :=
  (tail.sublists.map fun extension =>
    iwaniecLowerContinuationTerm r evenRestriction selected extension).sum

theorem iwaniecLowerContinuationTerm_ne_zero_length_lt
    {α : Type*} {r : Nat} {evenRestriction : List α → α → Bool}
    {selected extension : List α}
    (hselected : selected.length < 2 * r)
    (hterm : iwaniecLowerContinuationTerm r evenRestriction
      selected extension ≠ 0) :
    selected.length + extension.length < 2 * r := by
  induction extension generalizing selected with
  | nil => simpa using hselected
  | cons factor tail ih =>
      rw [iwaniecLowerContinuationTerm] at hterm
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [if_pos hselect] at hterm
        have hchild : iwaniecLowerContinuationTerm r evenRestriction
            (selected ++ [factor]) tail ≠ 0 := by
          simpa using hterm
        have hnext : (selected ++ [factor]).length < 2 * r := by
          simpa using hselect.1
        have hresult := ih hnext hchild
        simp only [List.length_cons, List.length_append,
          List.length_singleton] at hresult ⊢
        omega
      · rw [if_neg hselect] at hterm
        exact (hterm rfl).elim

theorem List.sum_map_flatMap_pair
    {α β : Type*} [AddCommMonoid β]
    (values : List (List α)) (head : α) (weight : List α → β) :
    ((values.flatMap fun extension => [extension, head :: extension]).map
        weight).sum =
      (values.map weight).sum +
        (values.map fun extension => weight (head :: extension)).sum := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih, add_assoc, add_left_comm]

theorem List.sum_map_neg
    {α β : Type*} [AddCommGroup β]
    (values : List α) (weight : α → β) :
    (values.map fun value => -weight value).sum =
      -(values.map weight).sum := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih, add_comm]

/-- Iwaniec's recursive tree is definitionally the alternating sum over all
ordered sublists.  This is the bridge from Lemma 1's recursive proof to the
global divisor coefficient used by the arithmetic sieve. -/
theorem iwaniecLowerExpansionSum_eq_tree
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected tail : List α) :
    iwaniecLowerExpansionSum r evenRestriction selected tail =
      iwaniecLowerTreeSum r evenRestriction selected tail := by
  induction tail generalizing selected with
  | nil =>
      simp [iwaniecLowerExpansionSum, iwaniecLowerContinuationTerm,
        iwaniecLowerTreeSum]
  | cons factor tail ih =>
      rw [iwaniecLowerExpansionSum, List.sublists_cons]
      change
        ((tail.sublists.flatMap fun extension =>
            [extension, factor :: extension]).map
          (fun extension =>
            iwaniecLowerContinuationTerm r evenRestriction selected
              extension)).sum = _
      rw [List.sum_map_flatMap_pair]
      change iwaniecLowerExpansionSum r evenRestriction selected tail +
          (tail.sublists.map fun extension =>
            iwaniecLowerContinuationTerm r evenRestriction selected
              (factor :: extension)).sum = _
      rw [ih, iwaniecLowerTreeSum]
      by_cases hselect :
          selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected factor)
      · rw [if_pos hselect]
        simp_rw [iwaniecLowerContinuationTerm, if_pos hselect]
        rw [List.sum_map_neg]
        change iwaniecLowerTreeSum r evenRestriction selected tail -
            iwaniecLowerExpansionSum r evenRestriction
              (selected ++ [factor]) tail = _
        rw [ih]
      · rw [if_neg hselect]
        simp_rw [iwaniecLowerContinuationTerm, if_neg hselect]
        simp

/-- Explicit sublist form of the lower Bonferroni inequality. -/
theorem iwaniecLowerExpansionSum_root_nonpos
    {α : Type*} (r : Nat) (hr : 0 < r)
    (evenRestriction : List α → α → Bool) (factors : List α)
    (hfactors : factors ≠ []) :
    iwaniecLowerExpansionSum r evenRestriction [] factors ≤ 0 := by
  rw [iwaniecLowerExpansionSum_eq_tree]
  exact iwaniecLowerTreeSum_root_nonpos
    r hr evenRestriction factors hfactors

end

end Erdos1212Kernel
