import Erdos1212Kernel.IwaniecStoppedWordMass

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

def iwaniecStoppedWordSupport (offset : Nat) (level z : Real) (rank : Nat) : Finset (List Nat) := by
  classical
  exact (iwaniecOrderedFactorSublists (iwaniecStrictPrimePool z)).filter
    (fun word => word.length ≤ rank ∧ iwaniecCubicStoppedWord offset level word)

theorem iwaniecStoppedWordMass_eq_finset_layer (offset : Nat) (level z : Real) (k : Nat) :
    iwaniecStoppedWordMass offset level (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) k =
      ∑ word ∈ (iwaniecOrderedFactorSublists (iwaniecStrictPrimePool z)).filter (fun word => word.length = k),
        iwaniecStoppedWordWeight offset level word := by
  classical
  let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
  have hset : (iwaniecOrderedFactorSublists (iwaniecStrictPrimePool z)).filter (fun word => word.length = k) =
      (factors.sublistsLen k).toFinset := by
    ext word
    simp only [factors, Finset.mem_filter, mem_iwaniecOrderedFactorSublists, List.mem_toFinset, List.mem_sublistsLen]
  rw [hset]
  exact (List.sum_toFinset (iwaniecStoppedWordWeight offset level)
    (List.nodup_sublistsLen k (Finset.sort_nodup _ _))).symm

theorem iwaniecPaperStoppedPartial_eq_length_filtered_words (offset : Nat) (level z : Real) (rank : Nat) :
    iwaniecPaperStoppedPartial offset level z rank =
      ∑ word ∈ (iwaniecOrderedFactorSublists (iwaniecStrictPrimePool z)).filter (fun word => word.length ≤ rank),
        iwaniecStoppedWordWeight offset level word := by
  classical
  rw [iwaniecPaperStoppedPartial_eq_sum]
  simp_rw [iwaniecPaperStoppedLayer_eq_wordMass, iwaniecStoppedWordMass_eq_finset_layer]
  have hh := Finset.sum_fiberwise_eq_sum_filter
    (iwaniecOrderedFactorSublists (iwaniecStrictPrimePool z)) (Finset.range (rank + 1))
    List.length (iwaniecStoppedWordWeight offset level)
  simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh

/-- Exact tuple expansion; removing a non-stopped tuple uses its proved
zero weight, not a change in the counted carrier. -/
theorem iwaniecPaperStoppedPartial_eq_word_support (offset : Nat) (level z : Real) (rank : Nat) :
    iwaniecPaperStoppedPartial offset level z rank =
      ∑ word ∈ iwaniecStoppedWordSupport offset level z rank, iwaniecStoppedWordWeight offset level word := by
  classical
  rw [iwaniecPaperStoppedPartial_eq_length_filtered_words]
  symm
  apply Finset.sum_subset
  · intro word hw
    obtain ⟨hmem, hlen, hstop⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hmem, hlen⟩
  · intro word hw hn
    have hnot : ¬iwaniecCubicStoppedWord offset level word := by
      intro hstop
      exact hn (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2, hstop⟩)
    exact iwaniecStoppedWordWeight_zero_of_not_stopped offset level word hnot

theorem iwaniecOrderedPrimeSublists_prod_injOn (z : Real) :
    Set.InjOn List.prod (iwaniecOrderedFactorSublists (iwaniecStrictPrimePool z) : Set (List Nat)) := by
  classical
  intro xs hxs ys hys hprod
  have hxsub := mem_iwaniecOrderedFactorSublists.mp hxs
  have hysub := mem_iwaniecOrderedFactorSublists.mp hys
  have hxn : xs.Nodup := (Finset.sort_nodup (iwaniecStrictPrimePool z) (fun a b : Nat => b ≤ a)).sublist hxsub
  have hyn : ys.Nodup := (Finset.sort_nodup (iwaniecStrictPrimePool z) (fun a b : Nat => b ≤ a)).sublist hysub
  have hxp : ∀ p ∈ xs.toFinset, p.Prime := by
    intro p hp
    have hpList : p ∈ xs := List.mem_toFinset.mp hp
    have hpPool : p ∈ iwaniecStrictPrimePool z := by
      simpa only [iwaniecDescendingFactors, Finset.mem_sort] using hxsub.subset hpList
    exact (mem_iwaniecStrictPrimePool.mp hpPool).1
  have hyp : ∀ p ∈ ys.toFinset, p.Prime := by
    intro p hp
    have hpList : p ∈ ys := List.mem_toFinset.mp hp
    have hpPool : p ∈ iwaniecStrictPrimePool z := by
      simpa only [iwaniecDescendingFactors, Finset.mem_sort] using hysub.subset hpList
    exact (mem_iwaniecStrictPrimePool.mp hpPool).1
  have hprodX : xs.toFinset.prod id = xs.prod := by simpa using List.prod_toFinset id hxn
  have hprodY : ys.toFinset.prod id = ys.prod := by simpa using List.prod_toFinset id hyn
  have hset : xs.toFinset = ys.toFinset := by
    calc
      _ = (xs.toFinset.prod id).primeFactors := by simpa using (Nat.primeFactors_prod hxp).symm
      _ = (ys.toFinset.prod id).primeFactors := by rw [hprodX, hprodY, hprod]
      _ = _ := by simpa using Nat.primeFactors_prod hyp
  rw [← iwaniecDescendingFactors_toFinset_of_orderedSublist hxsub,
    ← iwaniecDescendingFactors_toFinset_of_orderedSublist hysub, hset]


theorem iwaniecStoppedWordSupport_prod_injOn (offset : Nat) (level z : Real) (rank : Nat) :
    Set.InjOn List.prod (iwaniecStoppedWordSupport offset level z rank : Set (List Nat)) := by
  classical
  apply (iwaniecOrderedPrimeSublists_prod_injOn z).mono
  intro word hw
  exact (Finset.mem_filter.mp hw).1

end

end Erdos1212Kernel
