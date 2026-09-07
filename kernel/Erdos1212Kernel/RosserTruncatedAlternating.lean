import Mathlib.Data.Nat.Choose.Sum
import Erdos1212Kernel.RosserLowerSieveBasics

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

def oddTruncatedAlternatingChoose (m r : Nat) : Int :=
  ∑ k ∈ Finset.range (min (2 * r) (m + 1)),
    (-1 : Int) ^ k * m.choose k

theorem sum_choose_mul_truncated_eq_oddTruncated
    (m r : Nat) :
    (∑ k ∈ Finset.range (m + 1),
      m.choose k •
        (if k < 2 * r then (-1 : Int) ^ k else 0)) =
      oddTruncatedAlternatingChoose m r := by
  simp only [nsmul_eq_mul', ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hset :
      (Finset.range (m + 1)).filter (fun k => k < 2 * r) =
        Finset.range (min (2 * r) (m + 1)) := by
    ext k
    simp [and_comm]
  rw [hset]
  unfold oddTruncatedAlternatingChoose
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The unconditioned odd Bonferroni truncation is a lower Moebius divisor
sum.  Iwaniec's Rosser restrictions delete terms while preserving this
direction. -/
theorem oddTruncatedAlternatingChoose_le_indicator (m r : Nat) :
    oddTruncatedAlternatingChoose m r ≤ if m = 0 then 1 else 0 := by
  cases r with
  | zero =>
      simp [oddTruncatedAlternatingChoose]
      split_ifs <;> omega
  | succ r =>
      by_cases hm : m < 2 * (r + 1)
      · have hmin : min (2 * (r + 1)) (m + 1) = m + 1 :=
          min_eq_right (by omega)
        rw [oddTruncatedAlternatingChoose, hmin,
          Int.alternating_sum_range_choose]
      · have hmLower : 2 * (r + 1) ≤ m := by omega
        have hmPos : 0 < m := by omega
        let t := 2 * (r + 1) - 1
        have htSucc : t + 1 = 2 * (r + 1) := by
          dsimp [t]
          omega
        have htOdd : Odd t := by
          refine ⟨r, ?_⟩
          dsimp [t]
          omega
        have hmEq : m = (m - 1) + 1 := by omega
        have hmin : min (2 * (r + 1)) (m + 1) = 2 * (r + 1) :=
          min_eq_left (by omega)
        rw [oddTruncatedAlternatingChoose, hmin, ← htSucc, hmEq,
          Int.alternating_sum_range_choose_eq_choose, htOdd.neg_one_pow]
        simp

end

end Erdos1212Kernel
