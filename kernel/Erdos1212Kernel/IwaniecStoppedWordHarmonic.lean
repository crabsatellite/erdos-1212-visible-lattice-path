import Erdos1212Kernel.IwaniecStoppedWordSupport
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecStoppedWordSupport_data {offset rank : Nat} {level z : Real} {word : List Nat}
    (hw : word ∈ iwaniecStoppedWordSupport offset level z rank) :
    (∀ p ∈ word, p.Prime ∧ (p : Real) < z) ∧ word.Pairwise (fun p q => q ≤ p) ∧
      iwaniecCubicStoppedWord offset level word := by
  classical
  obtain ⟨hmem, hlen, hstop⟩ := Finset.mem_filter.mp hw
  have hsub := mem_iwaniecOrderedFactorSublists.mp hmem
  refine ⟨?_, (Finset.pairwise_sort _ _).sublist hsub, hstop⟩
  intro p hp
  have hpPool : p ∈ iwaniecStrictPrimePool z := by
    simpa only [iwaniecDescendingFactors, Finset.mem_sort] using hsub.subset hp
  exact mem_iwaniecStrictPrimePool.mp hpPool

theorem iwaniecStoppedWordSupport_prod_gt_one {offset rank : Nat} {level z : Real} {word : List Nat}
    (hw : word ∈ iwaniecStoppedWordSupport offset level z rank) : 1 < word.prod := by
  have hd := iwaniecStoppedWordSupport_data hw
  have hne := iwaniecCubicStoppedWord_ne_nil hd.2.2
  cases word with
  | nil => exact (hne rfl).elim
  | cons p tail =>
      have hp2 := (hd.1 p (by simp)).1.two_le
      have ht : 0 < tail.prod := List.prod_pos (fun q hq => (hd.1 q (by simp [hq])).1.pos)
      have hm := Nat.mul_le_mul_left p (show 1 ≤ tail.prod from ht)
      simp only [Nat.mul_one] at hm
      change 1 < p * tail.prod
      omega

/-- Exact weighted comparison with the source harmonic sum. The unit
integer is absent from the stopped support, making the comparison strict. -/
theorem iwaniecStoppedPartial_add_one_le_harmonic (offset rank : Nat) {level z : Real}
    (hy : 1 < level)
    (hprod : ∀ word ∈ iwaniecStoppedWordSupport offset level z rank, (word.prod : Real) < level) :
    iwaniecPaperStoppedPartial offset level z rank + 1 ≤ (harmonic (Nat.floor level) : Real) := by
  classical
  let S := iwaniecStoppedWordSupport offset level z rank
  let P := S.image List.prod
  have hnot : 1 ∉ P := by
    intro h
    obtain ⟨word, hw, hEq⟩ := Finset.mem_image.mp h
    have hgt := iwaniecStoppedWordSupport_prod_gt_one hw
    omega
  have hsub : insert 1 P ⊆ Finset.Icc 1 (Nat.floor level) := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by simpa only [Nat.cast_one] using hy.le)⟩
    · obtain ⟨word, hw, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr ⟨(iwaniecStoppedWordSupport_prod_gt_one hw).le, Nat.le_floor (hprod word hw).le⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : Nat => (n : Real)⁻¹) hsub
    (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  simp only [Finset.sum_insert hnot, Nat.cast_one, inv_one] at hsum
  have himage : (∑ word ∈ S, (word.prod : Real)⁻¹) = ∑ n ∈ P, (n : Real)⁻¹ := by
    symm
    exact Finset.sum_image (fun a ha b hb hab => (iwaniecStoppedWordSupport_prod_injOn offset level z rank) ha hb hab)
  have hweight : iwaniecPaperStoppedPartial offset level z rank ≤ ∑ n ∈ P, (n : Real)⁻¹ := by
    rw [iwaniecPaperStoppedPartial_eq_word_support]
    calc
      _ ≤ ∑ word ∈ S, (word.prod : Real)⁻¹ := Finset.sum_le_sum (fun word hw => iwaniecStoppedWordWeight_le_inv_prod offset level word)
      _ = _ := himage
  have hH : (∑ n ∈ Finset.Icc 1 (Nat.floor level), (n : Real)⁻¹) = (harmonic (Nat.floor level) : Real) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hH] at hsum
  linarith only [hsum, hweight]

theorem iwaniecStoppedPartial_lt_harmonic (offset rank : Nat) {level z : Real}
    (hy : 1 < level)
    (hprod : ∀ word ∈ iwaniecStoppedWordSupport offset level z rank, (word.prod : Real) < level) :
    iwaniecPaperStoppedPartial offset level z rank < (harmonic (Nat.floor level) : Real) := by
  have hh := iwaniecStoppedPartial_add_one_le_harmonic offset rank hy hprod
  linarith

theorem iwaniecStoppedPartial_lt_one_add_log (offset rank : Nat) {level z : Real}
    (hy : 1 < level)
    (hprod : ∀ word ∈ iwaniecStoppedWordSupport offset level z rank, (word.prod : Real) < level) :
    iwaniecPaperStoppedPartial offset level z rank < 1 + Real.log level :=
  (iwaniecStoppedPartial_lt_harmonic offset rank hy hprod).trans_le (harmonic_floor_le_one_add_log level hy.le)

end

end Erdos1212Kernel
