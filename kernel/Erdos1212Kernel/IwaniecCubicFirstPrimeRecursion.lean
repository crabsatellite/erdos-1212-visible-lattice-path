import Erdos1212Kernel.IwaniecCubicPaperMass
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Disintegrate a nonempty admissible tuple by its first selected factor.
No factor, multiplicity, or remaining suffix is discarded. -/
theorem iwaniecAdmissibleExtensionCount_eq_sum_firstFactor
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected tail : List α) (k : Nat) :
    iwaniecAdmissibleExtensionCount r evenRestriction selected tail (k + 1) =
      ∑ i : Fin tail.length,
        if selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected tail[i]) then
          iwaniecAdmissibleExtensionCount r evenRestriction
            (selected ++ [tail[i]]) (tail.drop (i.val + 1)) k
        else 0 := by
  induction tail with
  | nil => simp [iwaniecAdmissibleExtensionCount]
  | cons factor tail ih =>
      rw [iwaniecAdmissibleExtensionCount_succ_cons, ih]
      simp only [List.length_cons, Fin.sum_univ_succ,
        Fin.val_zero, List.getElem_cons_zero, zero_add,
        List.drop_succ_cons, List.drop_zero, Fin.val_succ,
        List.getElem_cons_succ]
      exact Nat.add_comm _ _

/-- Reciprocal-mass version of the same first-prime recursion.  This is the
finite head-prime summation structure used in Iwaniec's Lemma 15. -/
theorem iwaniecAdmissibleExtensionMass_eq_sum_firstFactor
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) (k : Nat) :
    iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
      selected tail (k + 1) =
      ∑ i : Fin tail.length,
        if selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected tail[i]) then
          factorWeight tail[i] *
            iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
              (selected ++ [tail[i]]) (tail.drop (i.val + 1)) k
        else 0 := by
  induction tail with
  | nil => simp [iwaniecAdmissibleExtensionMass]
  | cons factor tail ih =>
      rw [iwaniecAdmissibleExtensionMass_succ_cons, ih]
      simp only [List.length_cons, Fin.sum_univ_succ,
        Fin.val_zero, List.getElem_cons_zero, zero_add,
        List.drop_succ_cons, List.drop_zero, Fin.val_succ,
        List.getElem_cons_succ]
      exact add_comm _ _

/-- The cubic support layer, literally summed over its first reference prime.
The old selected prefix is retained in each child. -/
theorem iwaniecCubicPaperSupportLayer_card_eq_firstPrimeCount
    {r : Nat} (hr : 0 < r) (y : Nat) (Q : Finset Nat) (k : Nat) :
    let factors := iwaniecDescendingFactors (iwaniecReferencePrimePool Q.card)
    (iwaniecCubicPaperSupportLayer r y Q (k + 1)).card =
      ∑ i : Fin factors.length,
        iwaniecAdmissibleExtensionCount r (iwaniecCubicEvenRestriction y)
          [factors[i]] (factors.drop (i.val + 1)) k := by
  dsimp
  rw [iwaniecCubicPaperSupportLayer_card_eq_count,
    iwaniecAdmissibleExtensionCount_eq_sum_firstFactor]
  have hdepth : 1 < 2 * r := by omega
  simp [hdepth]

theorem iwaniecCubicPaperMass_eq_firstPrimeMass
    {r : Nat} (hr : 0 < r) (y : Nat) (factors : List Nat) (k : Nat) :
    iwaniecAdmissibleExtensionMass r (iwaniecCubicEvenRestriction y)
      iwaniecReciprocalFactorWeight [] factors (k + 1) =
      ∑ i : Fin factors.length,
        (factors[i] : Real)⁻¹ *
          iwaniecAdmissibleExtensionMass r (iwaniecCubicEvenRestriction y)
            iwaniecReciprocalFactorWeight [factors[i]]
              (factors.drop (i.val + 1)) k := by
  rw [iwaniecAdmissibleExtensionMass_eq_sum_firstFactor]
  have hdepth : 1 < 2 * r := by omega
  simp [hdepth, iwaniecReciprocalFactorWeight]

end

end Erdos1212Kernel
