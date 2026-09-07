import Erdos1212Kernel.IwaniecPaperSupportCount

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 650000

def iwaniecPaperFiniteSupport (rank : Nat) (level z : Real) : Finset (List Nat) := by
  classical
  exact (iwaniecOrderedFactorSublists (iwaniecStrictPrimePool z)).filter fun xs =>
    xs.length ≤ rank ∧ iwaniecCubicRealAdmissible (if Even rank then 1 else 0) level xs ∧
      (xs.prod : Real) < level

theorem iwaniecPaperFiniteSupport_card (rank : Nat) (level z : Real) :
    (iwaniecPaperFiniteSupport rank level z).card = iwaniecPaperSupportCount rank level z := by
  classical
  have hmap : (iwaniecPaperFiniteSupport rank level z : Set (List Nat)).MapsTo List.length
      (Finset.range (rank + 1)) := by
    intro xs hxs
    have hlen := (Finset.mem_filter.mp hxs).2.1
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  unfold iwaniecPaperSupportCount
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ rank := by have hh := Finset.mem_range.mp hk; omega
  let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
  let pred := fun xs : List Nat => decide
    (iwaniecCubicRealAdmissible (if Even rank then 1 else 0) level xs ∧ (xs.prod : Real) < level)
  have hset : (iwaniecPaperFiniteSupport rank level z).filter (fun xs => xs.length = k) =
      ((factors.sublistsLen k).filter pred).toFinset := by
    ext xs
    simp only [iwaniecPaperFiniteSupport, Finset.mem_filter, mem_iwaniecOrderedFactorSublists,
      List.mem_toFinset, List.mem_filter, List.mem_sublistsLen, pred, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hsub, hlen, hadm, hprod⟩, hlength⟩
      exact ⟨⟨hsub, hlength⟩, hadm, hprod⟩
    · rintro ⟨⟨hsub, hlength⟩, hadm, hprod⟩
      exact ⟨⟨hsub, by omega, hadm, hprod⟩, hlength⟩
  rw [hset]
  have hnodup : factors.Nodup := Finset.sort_nodup _ _
  exact List.toFinset_card_of_nodup ((List.nodup_sublistsLen k hnodup).filter pred)

theorem iwaniecPaperFiniteSupport_prod_injOn (rank : Nat) (level z : Real) :
    Set.InjOn List.prod (iwaniecPaperFiniteSupport rank level z : Set (List Nat)) := by
  classical
  intro xs hxs ys hys hprod
  have hxsub := mem_iwaniecOrderedFactorSublists.mp (Finset.mem_filter.mp hxs).1
  have hysub := mem_iwaniecOrderedFactorSublists.mp (Finset.mem_filter.mp hys).1
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

theorem iwaniecPaperSupportCount_le_floor (rank : Nat) {level z : Real} (hy : 1 < level) :
    iwaniecPaperSupportCount rank level z ≤ Nat.floor level := by
  classical
  let S := iwaniecPaperFiniteSupport rank level z
  have hsub : S.image List.prod ⊆ Finset.Icc 1 (Nat.floor level) := by
    intro n hn
    obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.mp hn
    have hdata := Finset.mem_filter.mp hxs
    have hxsub := mem_iwaniecOrderedFactorSublists.mp hdata.1
    have hpos : 0 < xs.prod := by
      apply List.prod_pos
      intro p hp
      have hpPool : p ∈ iwaniecStrictPrimePool z := by
        simpa only [iwaniecDescendingFactors, Finset.mem_sort] using hxsub.subset hp
      exact (mem_iwaniecStrictPrimePool.mp hpPool).1.pos
    have hupper := (Nat.le_floor_iff (show 0 ≤ level by linarith)).mpr hdata.2.2.2.le
    exact Finset.mem_Icc.mpr ⟨hpos, hupper⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (iwaniecPaperFiniteSupport_prod_injOn rank level z)] at hcard
  simpa only [S, iwaniecPaperFiniteSupport_card, Nat.card_Icc, Nat.add_sub_cancel] using hcard

theorem iwaniecPaperSupportCount_le_level (rank : Nat) {level z : Real} (hy : 1 < level) :
    (iwaniecPaperSupportCount rank level z : Real) ≤ level := by
  exact (show (iwaniecPaperSupportCount rank level z : Real) ≤ (Nat.floor level : Real) by
    exact_mod_cast iwaniecPaperSupportCount_le_floor rank hy).trans (Nat.floor_le (by linarith))

end

end Erdos1212Kernel
