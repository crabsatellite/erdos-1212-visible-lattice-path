import Erdos1212Kernel.IwaniecAuxiliaryDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def iwaniecAuxLowerTailKernel (t : Real) : Real :=
  iwaniecAuxUpper (t - 1) * t / (t - 1) ^ 2

def iwaniecAuxUpperTailKernel (t : Real) : Real :=
  iwaniecAuxLower (t - 1) * t / (t - 1) ^ 2

theorem iwaniecAuxLowerTailKernel_pos {t : Real} (ht : 2 ≤ t) :
    0 < iwaniecAuxLowerTailKernel t := by
  exact div_pos (mul_pos (iwaniecAuxUpper_pos (by linarith)) (by linarith))
    (sq_pos_of_pos (by linarith))

theorem iwaniecAuxUpperTailKernel_pos {t : Real} (ht : 3 ≤ t) :
    0 < iwaniecAuxUpperTailKernel t := by
  exact div_pos (mul_pos (iwaniecAuxLower_pos (by linarith)) (by linarith))
    (sq_pos_of_pos (by linarith))

theorem neg_iwaniecAuxLower_hasDerivAt {t : Real} (ht : 3 < t) :
    HasDerivAt (fun s => -iwaniecAuxLower s) (iwaniecAuxLowerTailKernel t) t := by
  convert (iwaniecAuxLower_hasDerivAt ht).neg using 1
  unfold iwaniecAuxLowerTailKernel
  ring

theorem neg_iwaniecAuxUpper_hasDerivAt {t : Real} (ht : 3 < t) :
    HasDerivAt (fun s => -iwaniecAuxUpper s) (iwaniecAuxUpperTailKernel t) t := by
  convert (iwaniecAuxUpper_hasDerivAt ht).neg using 1
  unfold iwaniecAuxUpperTailKernel
  ring

theorem iwaniecAuxLowerTail_integrable_high {s : Real} (hs : 3 ≤ s) :
    IntegrableOn iwaniecAuxLowerTailKernel (Set.Ioi s) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    ((iwaniecAuxLower_continuousOn.continuousAt (Ioi_mem_nhds (by linarith : 1 < s))).neg.continuousWithinAt)
    (fun t ht => neg_iwaniecAuxLower_hasDerivAt (lt_of_le_of_lt hs ht))
    (fun t ht => (iwaniecAuxLowerTailKernel_pos (by linarith [ht.out])).le)
  simpa using tendsto_iwaniecAuxLower_atTop_zero.neg

theorem iwaniecAuxUpperTail_integrable {s : Real} (hs : 3 ≤ s) :
    IntegrableOn iwaniecAuxUpperTailKernel (Set.Ioi s) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    ((iwaniecAuxUpper_continuousOn.continuousAt (Ioi_mem_nhds (by linarith : 1 < s))).neg.continuousWithinAt)
    (fun t ht => neg_iwaniecAuxUpper_hasDerivAt (lt_of_le_of_lt hs ht))
    (fun t ht => (iwaniecAuxUpperTailKernel_pos (by linarith [ht.out])).le)
  simpa using tendsto_iwaniecAuxUpper_atTop_zero.neg

theorem iwaniecAuxLower_tail_high {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxLower s = ∫ t in Set.Ioi s, iwaniecAuxLowerTailKernel t := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((iwaniecAuxLower_continuousOn.continuousAt (Ioi_mem_nhds (by linarith : 1 < s))).neg.continuousWithinAt)
    (fun t ht => neg_iwaniecAuxLower_hasDerivAt (lt_of_le_of_lt hs ht))
    (fun t ht => (iwaniecAuxLowerTailKernel_pos (by linarith [ht.out])).le)
    (show Tendsto (fun t => -iwaniecAuxLower t) atTop (nhds 0) from
      by simpa using tendsto_iwaniecAuxLower_atTop_zero.neg)
  simpa using h.symm

/-- Source (3.13), with the stated constant branch supplied separately by
`iwaniecAuxUpper_initial`. -/
theorem iwaniecAuxUpper_tail {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxUpper s = ∫ t in Set.Ioi s, iwaniecAuxUpperTailKernel t := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((iwaniecAuxUpper_continuousOn.continuousAt (Ioi_mem_nhds (by linarith : 1 < s))).neg.continuousWithinAt)
    (fun t ht => neg_iwaniecAuxUpper_hasDerivAt (lt_of_le_of_lt hs ht))
    (fun t ht => (iwaniecAuxUpperTailKernel_pos (by linarith [ht.out])).le)
    (show Tendsto (fun t => -iwaniecAuxUpper t) atTop (nhds 0) from
      by simpa using tendsto_iwaniecAuxUpper_atTop_zero.neg)
  simpa using h.symm

end

end Erdos1212Kernel
