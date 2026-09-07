import Erdos1212Kernel.IwaniecShiftedErrorSupport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Literal admissibility predicate for one already-selected prefix followed
by one ordered extension.  This is equation (2.6)'s depth and even-position
cubic condition, with the original quantifier order retained. -/
def iwaniecAdmissibleExtension
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool) :
    List α → List α → Prop
  | _selected, [] => True
  | selected, factor :: tail =>
      selected.length + 1 < 2 * r ∧
        (Even selected.length ∨ evenRestriction selected factor) ∧
        iwaniecAdmissibleExtension r evenRestriction
          (selected ++ [factor]) tail

def iwaniecSelectionAllowedBool
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected : List α) (factor : α) : Bool :=
  decide (selected.length + 1 < 2 * r ∧
    (Even selected.length ∨ evenRestriction selected factor))

def iwaniecAdmissibleExtensionBool
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool) :
    List α → List α → Bool
  | _selected, [] => true
  | selected, factor :: tail =>
      iwaniecSelectionAllowedBool r evenRestriction selected factor &&
        iwaniecAdmissibleExtensionBool r evenRestriction
          (selected ++ [factor]) tail

theorem iwaniecAdmissibleExtensionBool_eq_true_iff
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected extension : List α) :
    iwaniecAdmissibleExtensionBool r evenRestriction selected extension = true ↔
      iwaniecAdmissibleExtension r evenRestriction selected extension := by
  induction extension generalizing selected with
  | nil => simp [iwaniecAdmissibleExtensionBool, iwaniecAdmissibleExtension]
  | cons factor tail ih =>
      rw [iwaniecAdmissibleExtensionBool, iwaniecAdmissibleExtension]
      simp only [Bool.and_eq_true]
      rw [show iwaniecSelectionAllowedBool r evenRestriction selected factor = true ↔
          selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected factor) by
        simp [iwaniecSelectionAllowedBool]]
      rw [ih]
      aesop

theorem iwaniecLowerContinuationTerm_ne_zero_iff_admissible
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected extension : List α) :
    iwaniecLowerContinuationTerm r evenRestriction selected extension ≠ 0 ↔
      iwaniecAdmissibleExtension r evenRestriction selected extension := by
  induction extension generalizing selected with
  | nil => simp [iwaniecLowerContinuationTerm, iwaniecAdmissibleExtension]
  | cons factor tail ih =>
      rw [iwaniecLowerContinuationTerm, iwaniecAdmissibleExtension]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [if_pos hselect]
        simp only [neg_ne_zero]
        rw [ih]
        constructor
        · intro htail
          exact ⟨hselect.1, hselect.2, htail⟩
        · intro hadmissible
          exact hadmissible.2.2
      · rw [if_neg hselect]
        simp only [ne_eq, not_true_eq_false]
        constructor
        · intro hfalse
          exact hfalse.elim
        · intro hadmissible
          exact (hselect ⟨hadmissible.1, hadmissible.2.1⟩).elim

theorem iwaniecLowerContinuationTerm_eq_negOnePow_of_admissible
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected extension : List α)
    (hadmissible : iwaniecAdmissibleExtension r evenRestriction
      selected extension) :
    iwaniecLowerContinuationTerm r evenRestriction selected extension =
      (-1 : Int) ^ extension.length := by
  induction extension generalizing selected with
  | nil => simp [iwaniecLowerContinuationTerm]
  | cons factor tail ih =>
      rw [iwaniecAdmissibleExtension] at hadmissible
      rw [iwaniecLowerContinuationTerm, if_pos ⟨hadmissible.1,
        hadmissible.2.1⟩, ih (selected ++ [factor]) hadmissible.2.2]
      simp [pow_succ]

theorem iwaniecAdmissibleExtension_length_lt
    {α : Type*} {r : Nat} {evenRestriction : List α → α → Bool}
    {selected extension : List α}
    (hselected : selected.length < 2 * r)
    (hadmissible : iwaniecAdmissibleExtension r evenRestriction
      selected extension) :
    selected.length + extension.length < 2 * r := by
  have hterm : iwaniecLowerContinuationTerm r evenRestriction
      selected extension ≠ 0 := by
    rw [iwaniecLowerContinuationTerm_eq_negOnePow_of_admissible
      r evenRestriction selected extension hadmissible]
    simp
  exact iwaniecLowerContinuationTerm_ne_zero_length_lt hselected hterm

def iwaniecCubicAdmissibleOrdered
    (r y : Nat) (ordered : List Nat) : Prop :=
  iwaniecAdmissibleExtension r (iwaniecCubicEvenRestriction y) [] ordered

theorem iwaniecCubicAdmissibleOrdered_iff_continuation
    (r y : Nat) (ordered : List Nat) :
    iwaniecCubicAdmissibleOrdered r y ordered ↔
      iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
        ordered ≠ 0 := by
  exact (iwaniecLowerContinuationTerm_ne_zero_iff_admissible
    r (iwaniecCubicEvenRestriction y) [] ordered).symm

noncomputable def iwaniecCubicPaperSupportLayer
    (r y : Nat) (Q : Finset Nat) (k : Nat) : Finset (List Nat) :=
  by
    classical
    exact (iwaniecOrderedFactorSublists
        (iwaniecReferencePrimePool Q.card)).filter fun ordered =>
      ordered.length = k ∧ iwaniecCubicAdmissibleOrdered r y ordered

theorem iwaniecCubicPaperSupportLayer_eq_orderedErrorLayer
    (r y : Nat) (Q : Finset Nat) (k : Nat) :
    iwaniecCubicPaperSupportLayer r y Q k =
      iwaniecCubicOrderedErrorSupportLayer r y Q k := by
  classical
  ext ordered
  simp only [iwaniecCubicPaperSupportLayer,
    iwaniecCubicOrderedErrorSupportLayer, Finset.mem_filter]
  rw [iwaniecCubicAdmissibleOrdered_iff_continuation]

theorem iwaniecCubicPaperSupportLayer_card
    (r y : Nat) (Q : Finset Nat) (k : Nat) :
    (iwaniecCubicPaperSupportLayer r y Q k).card =
      (iwaniecCubicShiftedErrorSupportLayer r y Q k).card := by
  rw [iwaniecCubicPaperSupportLayer_eq_orderedErrorLayer]
  exact iwaniecCubicOrderedErrorSupportLayer_card r y Q k

theorem iwaniecCubicShiftedErrorMass_eq_sum_paperSupportLayers
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat) :
    iwaniecCubicShiftedErrorMass r y Q =
      ∑ k ∈ Finset.range (2 * r),
        (iwaniecCubicPaperSupportLayer r y Q k).card := by
  rw [iwaniecCubicShiftedErrorMass_eq_supportCard,
    iwaniecCubicShiftedErrorSupport_card_eq_sum_layers hr]
  norm_cast
  apply Finset.sum_congr rfl
  intro k _hk
  exact (iwaniecCubicPaperSupportLayer_card r y Q k).symm

end

end Erdos1212Kernel
