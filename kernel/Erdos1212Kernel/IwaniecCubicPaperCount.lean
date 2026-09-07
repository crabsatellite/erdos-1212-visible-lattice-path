import Erdos1212Kernel.IwaniecCubicAdmissibleSupport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

noncomputable def iwaniecAdmissibleExtensionCount
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected tail : List α) (k : Nat) : Nat :=
  by
    classical
    exact ((tail.sublistsLen k).filter fun extension =>
      iwaniecAdmissibleExtensionBool r evenRestriction
        selected extension).length

@[simp]
theorem iwaniecAdmissibleExtensionCount_zero
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected tail : List α) :
    iwaniecAdmissibleExtensionCount r evenRestriction selected tail 0 = 1 := by
  classical
  simp [iwaniecAdmissibleExtensionCount, iwaniecAdmissibleExtensionBool]

theorem length_filter_map_cons_admissible
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected : List α) (factor : α) (values : List (List α)) :
    ((values.map (List.cons factor)).filter fun extension =>
        iwaniecAdmissibleExtensionBool r evenRestriction
          selected extension).length =
      if selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        (values.filter fun extension =>
          iwaniecAdmissibleExtensionBool r evenRestriction
            (selected ++ [factor]) extension).length
      else 0 := by
  classical
  induction values with
  | nil => simp
  | cons extension values ih =>
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · have hbool : iwaniecSelectionAllowedBool r evenRestriction
            selected factor = true := by
            simp [iwaniecSelectionAllowedBool, hselect]
        rw [List.map, List.filter, iwaniecAdmissibleExtensionBool, hbool,
          Bool.true_and, List.filter]
        rw [if_pos hselect] at ih ⊢
        cases hchild : iwaniecAdmissibleExtensionBool r evenRestriction
            (selected ++ [factor]) extension <;> simp [hchild, ih]
      · have hbool : iwaniecSelectionAllowedBool r evenRestriction
            selected factor = false := by
            simp [iwaniecSelectionAllowedBool, hselect]
        simp [iwaniecAdmissibleExtensionBool, hbool, hselect, ih]

/-- Exact skip/select recursion for the discrete support count.  This is the
finite combinatorial recursion underneath Iwaniec 1971 Theorem 5. -/
theorem iwaniecAdmissibleExtensionCount_succ_cons
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected : List α) (factor : α) (tail : List α) (k : Nat) :
    iwaniecAdmissibleExtensionCount r evenRestriction selected
        (factor :: tail) (k + 1) =
      iwaniecAdmissibleExtensionCount r evenRestriction selected tail (k + 1) +
        if selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected factor) then
          iwaniecAdmissibleExtensionCount r evenRestriction
            (selected ++ [factor]) tail k
        else 0 := by
  classical
  unfold iwaniecAdmissibleExtensionCount
  rw [List.sublistsLen_succ_cons, List.filter_append, List.length_append,
    length_filter_map_cons_admissible]

noncomputable def iwaniecAdmissibleExtensionLayer
    {α : Type*} [DecidableEq α]
    (r : Nat) (evenRestriction : List α → α → Bool)
    (selected tail : List α) (k : Nat) : Finset (List α) :=
  by
    classical
    exact (tail.sublistsLen k).toFinset.filter fun extension =>
      iwaniecAdmissibleExtension r evenRestriction selected extension

theorem iwaniecAdmissibleExtensionLayer_card
    {α : Type*} [DecidableEq α]
    (r : Nat) (evenRestriction : List α → α → Bool)
    (selected tail : List α) (k : Nat) (htail : tail.Nodup) :
    (iwaniecAdmissibleExtensionLayer r evenRestriction
      selected tail k).card =
      iwaniecAdmissibleExtensionCount r evenRestriction selected tail k := by
  classical
  unfold iwaniecAdmissibleExtensionLayer iwaniecAdmissibleExtensionCount
  have hsets :
      ((tail.sublistsLen k).toFinset.filter fun extension =>
          iwaniecAdmissibleExtension r evenRestriction selected extension) =
        ((tail.sublistsLen k).filter fun extension =>
          iwaniecAdmissibleExtensionBool r evenRestriction
            selected extension).toFinset := by
    ext extension
    simp [iwaniecAdmissibleExtensionBool_eq_true_iff]
  rw [hsets]
  exact List.toFinset_card_of_nodup
    ((List.nodup_sublistsLen k htail).filter _)

theorem iwaniecCubicPaperSupportLayer_eq_admissibleLayer
    (r y : Nat) (Q : Finset Nat) (k : Nat) :
    iwaniecCubicPaperSupportLayer r y Q k =
      iwaniecAdmissibleExtensionLayer r (iwaniecCubicEvenRestriction y) []
        (iwaniecDescendingFactors (iwaniecReferencePrimePool Q.card)) k := by
  classical
  ext ordered
  simp only [iwaniecCubicPaperSupportLayer,
    iwaniecAdmissibleExtensionLayer, Finset.mem_filter,
    List.mem_toFinset, List.mem_sublistsLen,
    iwaniecCubicAdmissibleOrdered]
  aesop

theorem iwaniecCubicPaperSupportLayer_card_eq_count
    (r y : Nat) (Q : Finset Nat) (k : Nat) :
    (iwaniecCubicPaperSupportLayer r y Q k).card =
      iwaniecAdmissibleExtensionCount r (iwaniecCubicEvenRestriction y) []
        (iwaniecDescendingFactors (iwaniecReferencePrimePool Q.card)) k := by
  rw [iwaniecCubicPaperSupportLayer_eq_admissibleLayer]
  apply iwaniecAdmissibleExtensionLayer_card
  exact Finset.sort_nodup _ _

theorem iwaniecCubicShiftedErrorMass_eq_sum_recursiveCounts
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat) :
    iwaniecCubicShiftedErrorMass r y Q =
      ∑ k ∈ Finset.range (2 * r),
        iwaniecAdmissibleExtensionCount r (iwaniecCubicEvenRestriction y) []
          (iwaniecDescendingFactors (iwaniecReferencePrimePool Q.card)) k := by
  rw [iwaniecCubicShiftedErrorMass_eq_sum_paperSupportLayers hr]
  norm_cast
  apply Finset.sum_congr rfl
  intro k _hk
  exact iwaniecCubicPaperSupportLayer_card_eq_count r y Q k

end

end Erdos1212Kernel
