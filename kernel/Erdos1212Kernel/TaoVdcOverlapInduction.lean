import Erdos1212Kernel.TaoVdcInductionStatement

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

/-- The induction hypothesis is consumed on the literal overlap and on
the actual differentiated family. Shifts beyond M have empty overlap. -/
theorem taoVdc_induction_overlap {k : Nat} {C : Real} (hbound : taoVdcBound k C)
    (F : Nat → Real → Real) (a : Int) (M N h : Nat) {A T : Real}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hMN : M ≤ N) (hh : 0 < h)
    (hF : taoDerivativeHypotheses F (k + 1) (a : Real) ((a : Real) + M) A N T) :
    ‖∑ n ∈ taoCorputOverlap a M h,
        taoCorputPhase (F 0 ((n : Real) + h) - F 0 (n : Real))‖ / (N : Real) ≤
      C * A ^ (2 * taoVdcAlpha k) * taoVdcRate k N ((h : Real) * T / N) := by
  have hAp : 0 < A := by linarith
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hhp : 0 < (h : Real) := by exact_mod_cast hh
  have hnew : 0 < (h : Real) * T / N := by positivity
  by_cases hhm : h ≤ M
  · have hlen : M - h ≤ N := (Nat.sub_le M h).trans hMN
    have hEq : ((a : Real) + M) - (h : Real) = (a : Real) + (M - h : Nat) := by
      rw [Nat.cast_sub hhm]
      ring
    have hdiff := taoDerivativeHypotheses_difference hF hAp hNp hT hhp.le
    rw [hEq] at hdiff
    have hih := hbound (fun j => taoShiftDifference (F j) h) a (M - h) N hA hN hnew hlen hdiff
    rw [taoCorputOverlap_eq_interval a M h hhm]
    simpa only [taoShiftDifference, Int.cast_add, Int.cast_natCast] using hih
  · rw [taoCorputOverlap_eq_empty_of_length_le a M h (by omega), Finset.sum_empty, norm_zero, zero_div]
    have hrate := (taoVdcRate_pos k hNp hnew).le
    have hamp : 0 ≤ A ^ (2 * taoVdcAlpha k) := Real.rpow_nonneg hAp.le _
    exact mul_nonneg (mul_nonneg hC hamp) hrate

end

end Erdos1212Kernel
