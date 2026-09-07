import Erdos1212Kernel.IwaniecCubicRealLevelTransport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

attribute [local instance] Classical.propDecidable

def iwaniecCubicRealCount (offset : Nat) (level : Real)
    (factors : List Nat) (k : Nat) : Nat := by
  classical
  exact ((factors.sublistsLen k).filter fun extension =>
    decide (iwaniecCubicRealAdmissible offset level extension)).length

@[simp]
theorem iwaniecCubicRealCount_zero (offset : Nat) (level : Real)
    (factors : List Nat) :
    iwaniecCubicRealCount offset level factors 0 = 1 := by
  simp [iwaniecCubicRealCount, iwaniecCubicRealAdmissible]

theorem iwaniecAdmissibleExtensionCount_eq_realCount
    (r y : Nat) (selected factors : List Nat) (k : Nat)
    (hdepth : selected.length + k < 2 * r)
    (hprod : 0 < selected.prod)
    (hpositive : ∀ p ∈ factors, 0 < p) :
    iwaniecAdmissibleExtensionCount r (iwaniecCubicEvenRestriction y)
        selected factors k =
      iwaniecCubicRealCount selected.length ((y : Real) / selected.prod) factors k := by
  classical
  unfold iwaniecAdmissibleExtensionCount iwaniecCubicRealCount
  apply congrArg List.length
  apply List.filter_congr
  intro extension hextension
  have hdata := List.mem_sublistsLen.mp hextension
  have hpos : ∀ p ∈ extension, 0 < p := fun p hp =>
    hpositive p (hdata.1.subset hp)
  apply Bool.eq_iff_iff.mpr
  rw [iwaniecAdmissibleExtensionBool_eq_true_iff, decide_eq_true_eq,
    iwaniecAdmissibleExtension_iff_realLevel r y selected extension
      (by omega) hprod hpos]
  simp only [hdata.2, hdepth, true_and]

theorem iwaniecCubicRealCount_cons_map
    (offset : Nat) (level : Real) (p : Nat) (values : List (List Nat)) :
    ((values.map (List.cons p)).filter fun extension =>
        decide (iwaniecCubicRealAdmissible offset level extension)).length =
      if Even offset ∨ (p : Real) ^ 3 < level then
        (values.filter fun extension =>
          decide (iwaniecCubicRealAdmissible (offset + 1) (level / p) extension)).length
      else 0 := by
  classical
  induction values with
  | nil => simp
  | cons extension values ih =>
      by_cases hallow : Even offset ∨ (p : Real) ^ 3 < level
      · cases hchild : decide (iwaniecCubicRealAdmissible
          (offset + 1) (level / p) extension) <;>
          simp [List.filter_cons, iwaniecCubicRealAdmissible, hallow, hchild] at ih ⊢ <;>
          omega
      · simp [iwaniecCubicRealAdmissible, hallow, ih]

theorem iwaniecCubicRealCount_succ_cons
    (offset : Nat) (level : Real) (p : Nat) (factors : List Nat) (k : Nat) :
    iwaniecCubicRealCount offset level (p :: factors) (k + 1) =
      iwaniecCubicRealCount offset level factors (k + 1) +
        if Even offset ∨ (p : Real) ^ 3 < level then
          iwaniecCubicRealCount (offset + 1) (level / p) factors k
        else 0 := by
  classical
  unfold iwaniecCubicRealCount
  rw [List.sublistsLen_succ_cons, List.filter_append, List.length_append,
    iwaniecCubicRealCount_cons_map]

/-- The finite, exact `y/p` recursion; unlike a scale adapter, it is an
identity between the actual filtered sublist counts. -/
theorem iwaniecCubicRealCount_eq_sum_firstPrime
    (offset : Nat) (level : Real) (factors : List Nat) (k : Nat) :
    iwaniecCubicRealCount offset level factors (k + 1) =
      ∑ i : Fin factors.length,
        if Even offset ∨ (factors[i] : Real) ^ 3 < level then
          iwaniecCubicRealCount (offset + 1) (level / factors[i])
            (factors.drop (i.val + 1)) k
        else 0 := by
  classical
  induction factors with
  | nil => simp [iwaniecCubicRealCount]
  | cons p factors ih =>
      rw [iwaniecCubicRealCount_succ_cons, ih]
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero,
        List.drop_succ_cons, List.drop_zero, Fin.val_succ]
      exact add_comm _ _

theorem iwaniecCubicRealAdmissible_add_two
    (offset : Nat) (level : Real) (ordered : List Nat) :
    iwaniecCubicRealAdmissible (offset + 2) level ordered ↔
      iwaniecCubicRealAdmissible offset level ordered := by
  induction ordered generalizing offset level with
  | nil => simp [iwaniecCubicRealAdmissible]
  | cons p tail ih =>
      have heven : Even (offset + 2) ↔ Even offset := by
        simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
        omega
      simp only [iwaniecCubicRealAdmissible, heven]
      have hoff : offset + 2 + 1 = (offset + 1) + 2 := by omega
      rw [hoff, ih]

theorem iwaniecCubicRealCount_add_two
    (offset : Nat) (level : Real) (factors : List Nat) (k : Nat) :
    iwaniecCubicRealCount (offset + 2) level factors k =
      iwaniecCubicRealCount offset level factors k := by
  classical
  simp only [iwaniecCubicRealCount, iwaniecCubicRealAdmissible_add_two]

/-- Consume the exact real-level transport into the original support mass.
The positive factors and the rank bound are discharged here, not supplied
as new hypotheses to the final sieve. -/
theorem iwaniecCubicShiftedErrorMass_eq_realCounts
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat) :
    iwaniecCubicShiftedErrorMass r y Q =
      ∑ k ∈ Finset.range (2 * r),
        (iwaniecCubicRealCount 0 y
          (iwaniecDescendingFactors (iwaniecReferencePrimePool Q.card)) k : Real) := by
  rw [iwaniecCubicShiftedErrorMass_eq_sum_recursiveCounts hr]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hdepth : ([] : List Nat).length + k < 2 * r := by
    simpa using Finset.mem_range.mp hk
  have hpositive : ∀ p ∈ iwaniecDescendingFactors
      (iwaniecReferencePrimePool Q.card), 0 < p := by
    intro p hp
    apply (iwaniecReferencePrimePool_prime Q.card p ?_).pos
    simpa [iwaniecDescendingFactors] using hp
  have hcount := iwaniecAdmissibleExtensionCount_eq_realCount r y []
    (iwaniecDescendingFactors (iwaniecReferencePrimePool Q.card)) k
    hdepth (by simp) hpositive
  simpa using congrArg (fun n : Nat => (n : Real)) hcount

end

end Erdos1212Kernel
