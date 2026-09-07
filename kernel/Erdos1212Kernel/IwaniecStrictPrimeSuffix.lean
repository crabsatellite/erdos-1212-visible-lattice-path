import Erdos1212Kernel.IwaniecPaperSupportCount

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

theorem iwaniecDescendingFactors_strict
    (pool : Finset Nat) :
    (iwaniecDescendingFactors pool).Pairwise (fun p q => q < p) := by
  have horder : (iwaniecDescendingFactors pool).Pairwise (fun p q => q ≤ p) :=
    Finset.pairwise_sort _ _
  have hnodup : (iwaniecDescendingFactors pool).Nodup := Finset.sort_nodup _ _
  exact (horder.and hnodup).imp (by intro p q h; omega)

theorem iwaniecStrictList_drop_eq_filter
    (factors : List Nat) (horder : factors.Pairwise (fun p q => q < p))
    (i : Fin factors.length) :
    factors.drop (i.val + 1) = factors.filter (fun q => q < factors[i]) := by
  induction factors with
  | nil => exact Fin.elim0 i
  | cons p tail ih =>
      have hpair := List.pairwise_cons.mp horder
      refine Fin.cases ?_ (fun j => ?_) i
      · have hfilter : tail.filter (fun q => q < p) = tail := by
          apply List.filter_eq_self.mpr
          intro q hq
          simpa using hpair.1 q hq
        change tail = (p :: tail).filter (fun q => decide (q < p))
        simpa only [List.filter_cons, lt_self_iff_false, decide_false,
          Bool.false_eq_true, if_false] using hfilter.symm
      · have hnot : ¬p < tail[j] := by
          have hlt := hpair.1 tail[j] (List.getElem_mem j.isLt)
          omega
        change tail.drop (j.val + 1) =
          (p :: tail).filter (fun q => decide (q < tail[j]))
        simpa only [List.filter_cons, hnot, decide_false,
          Bool.false_eq_true, if_false] using ih hpair.2 j

/-- After selecting a prime from a complete strict prime pool, the remaining
suffix is exactly the complete prime pool below that prime. -/
theorem iwaniecStrictPrimeSuffix
    (z : Real)
    (i : Fin (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).length) :
    let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
    factors.drop (i.val + 1) =
      iwaniecDescendingFactors (iwaniecStrictPrimePool (factors[i] : Real)) := by
  dsimp
  let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
  have hselected : factors[i] ∈ iwaniecStrictPrimePool z := by
    have hmem : factors[i] ∈ factors := List.getElem_mem i.isLt
    exact (Finset.mem_sort _).1 hmem
  have hselectedLt : (factors[i] : Real) < z :=
    (mem_iwaniecStrictPrimePool.mp hselected).2
  have hdrop := List.drop_sublist (i.val + 1) factors
  have hsorted := iwaniecDescendingFactors_toFinset_of_orderedSublist hdrop
  have hfilter := iwaniecStrictList_drop_eq_filter factors
    (iwaniecDescendingFactors_strict _) i
  have hset : (factors.drop (i.val + 1)).toFinset =
      iwaniecStrictPrimePool (factors[i] : Real) := by
    ext q
    rw [List.mem_toFinset, hfilter, List.mem_filter, mem_iwaniecStrictPrimePool]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hqMem, hqLt⟩
      have hqPool : q ∈ iwaniecStrictPrimePool z := by
        simpa [factors, iwaniecDescendingFactors] using hqMem
      exact ⟨(mem_iwaniecStrictPrimePool.mp hqPool).1, by exact_mod_cast hqLt⟩
    · rintro ⟨hqPrime, hqLt⟩
      have hqPool : q ∈ iwaniecStrictPrimePool z :=
        mem_iwaniecStrictPrimePool.mpr ⟨hqPrime, hqLt.trans hselectedLt⟩
      exact ⟨by simpa [factors, iwaniecDescendingFactors] using hqPool,
        by exact_mod_cast hqLt⟩
  change factors.drop (i.val + 1) = _
  rw [← hsorted, hset]
  rfl

theorem iwaniecSum_descendingFactors
    (pool : Finset Nat) (weight : Nat → Nat) :
    (∑ i : Fin (iwaniecDescendingFactors pool).length,
      weight (iwaniecDescendingFactors pool)[i]) =
        ∑ p ∈ pool, weight p := by
  classical
  apply Finset.sum_bij (fun i _hi => (iwaniecDescendingFactors pool)[i])
  · intro i hi
    have hmem : (iwaniecDescendingFactors pool)[i] ∈ iwaniecDescendingFactors pool :=
      List.getElem_mem i.isLt
    exact (Finset.mem_sort _).1 hmem
  · intro i hi j hj heq
    apply Fin.ext
    exact (List.getElem_inj (Finset.sort_nodup _ _)).1 heq
  · intro p hp
    have hmem : p ∈ iwaniecDescendingFactors pool := by
      simpa [iwaniecDescendingFactors] using hp
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, heq⟩
  · intro i hi
    rfl

end

end Erdos1212Kernel
