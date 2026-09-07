import Erdos1212Kernel.IwaniecStrictPrimeSuffix

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

theorem iwaniecCubicRealTotalCount_strictPrimeRecursion
    (offset : Nat) (level z : Real) (depth : Nat) :
    iwaniecCubicRealTotalCount offset level
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (depth + 1) =
      1 + ∑ p ∈ iwaniecStrictPrimePool z,
        if Even offset ∨ (p : Real) ^ 3 < level then
          iwaniecCubicRealTotalCount (offset + 1) (level / p)
            (iwaniecDescendingFactors (iwaniecStrictPrimePool p)) depth
        else 0 := by
  classical
  rw [iwaniecCubicRealTotalCount_succ]
  apply congrArg (fun n : Nat => 1 + n)
  calc
    _ = ∑ i : Fin (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).length,
        if Even offset ∨
            ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) ^ 3 < level then
          iwaniecCubicRealTotalCount (offset + 1)
            (level / (iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i])
            (iwaniecDescendingFactors (iwaniecStrictPrimePool
              ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real))) depth
        else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iwaniecStrictPrimeSuffix z i]
    _ = _ := iwaniecSum_descendingFactors (iwaniecStrictPrimePool z)
      (fun p => if Even offset ∨ (p : Real) ^ 3 < level then
        iwaniecCubicRealTotalCount (offset + 1) (level / p)
          (iwaniecDescendingFactors (iwaniecStrictPrimePool p)) depth else 0)

theorem iwaniecPaperSupportCount_even_eq_realTotalCount
    (r : Nat) {level : Real} (hlevel : 1 < level) (z : Real) :
    iwaniecPaperSupportCount (2 * r) level z =
      iwaniecCubicRealTotalCount 1 level
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (2 * r) := by
  unfold iwaniecPaperSupportCount iwaniecCubicRealTotalCount
  have heven : Even (2 * r) := ⟨r, by omega⟩
  rw [if_pos heven]
  apply Finset.sum_congr rfl
  intro k hk
  apply iwaniecCubicRealProductCount_eq_cubicFirst _ _ k hlevel
  · apply iwaniecDescendingFactors_positive
    intro p hp
    exact (mem_iwaniecStrictPrimePool.mp hp).1
  · exact Finset.pairwise_sort _ _

/-- First identity in Lemma 17, at the strict cutoff `z`. -/
theorem iwaniecPaperSupportCount_odd_recursion
    (r : Nat) {level z : Real} (hlevel : 1 < level) (hz : z ≤ level) :
    iwaniecPaperSupportCount (2 * r + 1) level z =
      1 + ∑ p ∈ iwaniecStrictPrimePool z,
        iwaniecPaperSupportCount (2 * r) (level / p) p := by
  classical
  rw [iwaniecPaperSupportCount_eq_realTotalCount _ hlevel hz]
  have hodd : Odd (2 * r + 1) := ⟨r, rfl⟩
  rw [if_neg (Nat.not_even_iff_odd.mpr hodd),
    iwaniecCubicRealTotalCount_strictPrimeRecursion]
  have hEvenZero : Even (0 : Nat) := ⟨0, rfl⟩
  simp only [hEvenZero, true_or, if_true, zero_add]
  apply congrArg (fun n : Nat => 1 + n)
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpPrime, hpLt⟩ := mem_iwaniecStrictPrimePool.mp hp
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hchild : 1 < level / p := by
    rw [lt_div_iff₀ hpPos, one_mul]
    exact hpLt.trans_le hz
  exact (iwaniecPaperSupportCount_even_eq_realTotalCount r hchild p).symm

/-- Definition-derived second recursion.  The empty tuple contributes `1`;
the printed Lemma 17 display omits it. -/
theorem iwaniecPaperSupportCount_even_recursion_with_unit
    (r : Nat) {level z : Real} (hlevel : 1 < level)
    (hcutoff : ∀ p ∈ iwaniecStrictPrimePool z, (p : Real) ^ 3 < level) :
    iwaniecPaperSupportCount (2 * r + 2) level z =
      1 + ∑ p ∈ iwaniecStrictPrimePool z,
        iwaniecPaperSupportCount (2 * r + 1) (level / p) p := by
  classical
  have hrank : 2 * r + 2 = 2 * (r + 1) := by omega
  rw [hrank, iwaniecPaperSupportCount_even_eq_realTotalCount (r + 1) hlevel z,
    ← hrank]
  change iwaniecCubicRealTotalCount 1 level
    (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) ((2 * r + 1) + 1) = _
  rw [iwaniecCubicRealTotalCount_strictPrimeRecursion]
  have hoff : 1 + 1 = 0 + 2 := rfl
  simp only [hoff, iwaniecCubicRealTotalCount_add_two]
  apply congrArg (fun n : Nat => 1 + n)
  apply Finset.sum_congr rfl
  intro p hp
  have hcubic := hcutoff p hp
  rw [if_pos (Or.inr hcubic)]
  have hprime := (mem_iwaniecStrictPrimePool.mp hp).1
  have hpPos : (0 : Real) < p := by exact_mod_cast hprime.pos
  have hpOne : (1 : Real) ≤ p := by exact_mod_cast hprime.pos
  have hpSquare : (p : Real) ^ 2 ≤ (p : Real) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpOne) (sq_nonneg (p : Real))]
  have hpLower : (p : Real) ≤ (p : Real) ^ 2 := by nlinarith
  have hchild : 1 < level / p := by
    rw [lt_div_iff₀ hpPos, one_mul]
    exact hpLower.trans_lt (hpSquare.trans_lt hcubic)
  have hchildCutoff : (p : Real) ≤ level / p := by
    rw [le_div_iff₀ hpPos]
    nlinarith [hpSquare.trans_lt hcubic]
  rw [iwaniecPaperSupportCount_eq_realTotalCount _ hchild hchildCutoff]
  have hodd : Odd (2 * r + 1) := ⟨r, rfl⟩
  rw [if_neg (Nat.not_even_iff_odd.mpr hodd)]

end

end Erdos1212Kernel
