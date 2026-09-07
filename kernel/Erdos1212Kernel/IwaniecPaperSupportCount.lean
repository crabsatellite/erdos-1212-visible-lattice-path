import Erdos1212Kernel.IwaniecCubicRealProductBound
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Strict real prime cutoff from the paper.  The ceiling is only an
enumeration bound; the predicate retains the original strict endpoint. -/
def iwaniecStrictPrimePool (z : Real) : Finset Nat :=
  (Nat.primesLE ⌈z⌉₊).filter (fun p => (p : Real) < z)

@[simp]
theorem mem_iwaniecStrictPrimePool {p : Nat} {z : Real} :
    p ∈ iwaniecStrictPrimePool z ↔ p.Prime ∧ (p : Real) < z := by
  simp only [iwaniecStrictPrimePool, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpBound, hpPrime⟩, hpLt⟩
    exact ⟨hpPrime, hpLt⟩
  · rintro ⟨hpPrime, hpLt⟩
    exact ⟨⟨by exact_mod_cast hpLt.le.trans (Nat.le_ceil z), hpPrime⟩, hpLt⟩

theorem iwaniecStrictPrimePool_eq_empty {z : Real} (hz : z ≤ 2) :
    iwaniecStrictPrimePool z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hprime, hlt⟩ := mem_iwaniecStrictPrimePool.mp hp
  have hpTwo : (2 : Real) ≤ p := by exact_mod_cast hprime.two_le
  linarith

theorem iwaniecStrictPrimePool_nat_add_one (N : Nat) :
    iwaniecStrictPrimePool ((N : Real) + 1) = Nat.primesLE N := by
  ext p
  rw [mem_iwaniecStrictPrimePool, Nat.mem_primesLE]
  have hbound : (p : Real) < (N : Real) + 1 ↔ p ≤ N := by
    rw [← Nat.lt_succ_iff]
    norm_cast
  rw [hbound, and_comm]

/-- The tuple form of the paper's `A_(r,y)`, before substituting `z=y^(1/s)`.
It includes the empty tuple, the strict prime cutoff, and `d < y`. -/
def iwaniecPaperSupportCount (rank : Nat) (level z : Real) : Nat :=
  ∑ k ∈ Finset.range (rank + 1),
    iwaniecCubicRealProductCount (if Even rank then 1 else 0) level
      (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) k

def iwaniecPaperA (rank : Nat) (level s : Real) : Nat :=
  iwaniecPaperSupportCount rank level (Real.exp (Real.log level / s))

theorem iwaniecPaperSupportCount_eq_realTotalCount
    (rank : Nat) {level z : Real} (hlevel : 1 < level) (hz : z ≤ level) :
    iwaniecPaperSupportCount rank level z =
      iwaniecCubicRealTotalCount (if Even rank then 1 else 0) level
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) rank := by
  have hpositive : ∀ p ∈ iwaniecDescendingFactors (iwaniecStrictPrimePool z), 0 < p := by
    apply iwaniecDescendingFactors_positive
    intro p hp
    exact (mem_iwaniecStrictPrimePool.mp hp).1
  have hordered : (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).Pairwise
      (fun p q => q ≤ p) := Finset.pairwise_sort _ _
  unfold iwaniecPaperSupportCount iwaniecCubicRealTotalCount
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hrank : Even rank
  · simp only [if_pos hrank]
    exact iwaniecCubicRealProductCount_eq_cubicFirst _ _ k hlevel hpositive hordered
  · simp only [if_neg hrank]
    apply iwaniecCubicRealProductCount_eq_of_cutoff _ _ k hlevel hpositive hordered
    intro p hp
    have hpool : p ∈ iwaniecStrictPrimePool z := by
      simpa [iwaniecDescendingFactors] using hp
    exact (mem_iwaniecStrictPrimePool.mp hpool).2.trans_le hz

theorem iwaniecCubicRealProductCount_nil_zero
    (offset : Nat) {level : Real} (hlevel : 1 < level) :
    iwaniecCubicRealProductCount offset level [] 0 = 1 := by
  simp [iwaniecCubicRealProductCount, iwaniecCubicRealAdmissible, hlevel]

theorem iwaniecCubicRealProductCount_nil_succ
    (offset : Nat) (level : Real) (k : Nat) :
    iwaniecCubicRealProductCount offset level [] (k + 1) = 0 := by
  simp [iwaniecCubicRealProductCount]

theorem iwaniecPaperSupportCount_eq_one_of_no_primes
    (rank : Nat) {level z : Real} (hlevel : 1 < level)
    (hpool : iwaniecStrictPrimePool z = ∅) :
    iwaniecPaperSupportCount rank level z = 1 := by
  unfold iwaniecPaperSupportCount
  rw [hpool]
  simp only [iwaniecDescendingFactors, Finset.sort_empty]
  rw [Finset.sum_range_succ']
  simp [iwaniecCubicRealProductCount_nil_succ,
    iwaniecCubicRealProductCount_nil_zero _ hlevel]

theorem iwaniecStrictPrimePool_cuberoot_two :
    iwaniecStrictPrimePool (Real.exp (Real.log 2 / 3)) = ∅ := by
  apply iwaniecStrictPrimePool_eq_empty
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.exp (Real.log 2 / 3) < Real.exp (Real.log 2) := by
    apply Real.exp_lt_exp.mpr
    linarith
  rw [Real.exp_log (by norm_num : (0 : Real) < 2)] at hlt
  exact hlt.le

/-- Empty-tuple audit of the second display in Lemma 17.  With `y=2,s=3`,
the prime sum is empty but `A_(2,y)` is one.  Hence a recurrence omitting
the empty-tuple term cannot be consumed literally. -/
theorem iwaniecPaperA_two_two_three_ne_head_sum_without_unit :
    iwaniecPaperA 2 2 3 ≠
      ∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log 2 / 3)),
        iwaniecPaperSupportCount 1 (2 / (p : Real)) p := by
  have hA : iwaniecPaperA 2 2 3 = 1 :=
    iwaniecPaperSupportCount_eq_one_of_no_primes 2 (by norm_num)
      iwaniecStrictPrimePool_cuberoot_two
  rw [hA, iwaniecStrictPrimePool_cuberoot_two]
  simp

end

end Erdos1212Kernel
