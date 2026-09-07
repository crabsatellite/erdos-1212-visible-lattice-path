import Erdos1212Kernel.IwaniecLowerExpansion
import Mathlib.Data.Finset.Sort

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

/-- Canonical decreasing order of a finite factor set. -/
def iwaniecDescendingFactors (factors : Finset Nat) : List Nat :=
  factors.sort (fun left right => right ≤ left)

/-- All ordered factor sublists, represented without duplicate list values. -/
def iwaniecOrderedFactorSublists (factors : Finset Nat) : Finset (List Nat) :=
  ⟨(iwaniecDescendingFactors factors).sublists,
    (Finset.sort_nodup factors (fun left right => right ≤ left)).sublists⟩

@[simp]
theorem mem_iwaniecOrderedFactorSublists
    {factors : Finset Nat} {ordered : List Nat} :
    ordered ∈ iwaniecOrderedFactorSublists factors ↔
      List.Sublist ordered (iwaniecDescendingFactors factors) := by
  simp [iwaniecOrderedFactorSublists]

theorem iwaniecDescendingFactors_injective :
    Function.Injective iwaniecDescendingFactors := by
  intro left right heq
  have hsets := congrArg List.toFinset heq
  simpa [iwaniecDescendingFactors] using hsets

theorem iwaniecDescendingFactors_sublist_of_subset
    {small large : Finset Nat} (hsubset : small ⊆ large) :
    List.Sublist (iwaniecDescendingFactors small)
      (iwaniecDescendingFactors large) := by
  apply List.sublist_of_subperm_of_pairwise
    (r := fun left right : Nat => right ≤ left)
  · apply List.Nodup.subperm
    · exact Finset.sort_nodup small (fun left right => right ≤ left)
    · intro factor hfactor
      have hsmall : factor ∈ small := by
        simpa [iwaniecDescendingFactors] using hfactor
      have hlarge := hsubset hsmall
      simpa [iwaniecDescendingFactors] using hlarge
  · exact Finset.pairwise_sort small (fun left right => right ≤ left)
  · exact Finset.pairwise_sort large (fun left right => right ≤ left)

theorem iwaniecDescendingFactors_toFinset_of_orderedSublist
    {factors : Finset Nat} {ordered : List Nat}
    (hordered : List.Sublist ordered (iwaniecDescendingFactors factors)) :
    iwaniecDescendingFactors ordered.toFinset = ordered := by
  have hnodup : ordered.Nodup :=
    (Finset.sort_nodup factors
      (fun left right : Nat => right ≤ left)).sublist hordered
  apply (List.toFinset_sort (r := fun left right : Nat => right ≤ left)
    hnodup).2
  exact (Finset.pairwise_sort factors
    (fun left right => right ≤ left)).sublist hordered

theorem iwaniecOrderedFactorSublists_eq_image
    (factors : Finset Nat) :
    iwaniecOrderedFactorSublists factors =
      factors.powerset.image iwaniecDescendingFactors := by
  ext ordered
  constructor
  · intro hordered
    have hsublist := mem_iwaniecOrderedFactorSublists.mp hordered
    apply Finset.mem_image.mpr
    refine ⟨ordered.toFinset, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro factor hfactor
      have hmem : factor ∈ ordered := by simpa using hfactor
      have hambient : factor ∈ iwaniecDescendingFactors factors :=
        hsublist.subset hmem
      simpa [iwaniecDescendingFactors] using hambient
    · exact iwaniecDescendingFactors_toFinset_of_orderedSublist hsublist
  · intro himage
    obtain ⟨subset, hsubset, rfl⟩ := Finset.mem_image.mp himage
    apply mem_iwaniecOrderedFactorSublists.mpr
    exact iwaniecDescendingFactors_sublist_of_subset
      (Finset.mem_powerset.mp hsubset)

/-- Reindex a powerset sum by the literal decreasing ordered sublists. -/
theorem sum_powerset_iwaniecDescendingFactors
    {β : Type*} [AddCommMonoid β]
    (factors : Finset Nat) (weight : List Nat → β) :
    (∑ subset ∈ factors.powerset,
        weight (iwaniecDescendingFactors subset)) =
      ∑ ordered ∈ iwaniecOrderedFactorSublists factors, weight ordered := by
  rw [iwaniecOrderedFactorSublists_eq_image]
  symm
  exact Finset.sum_image fun _left _hleft _right _hright heq =>
    iwaniecDescendingFactors_injective heq

end

end Erdos1212Kernel
