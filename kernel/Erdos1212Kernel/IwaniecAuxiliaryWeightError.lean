import Erdos1212Kernel.IwaniecAuxiliaryWeightedFunctions

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

def iwaniecAuxWeightError (level s : Real) : Real :=
  100 * iwaniecAuxCorollaryConstant * s ^ 2 * Real.log s ^ 4 / Real.log level ^ 2

theorem iwaniecAuxWeightLogDerivative_le_forty
    {level s : Real} (hy : 1 < level) (hs : 1 ≤ s) (hlog : 1 ≤ Real.log s) :
    iwaniecAuxWeightLogDerivative level s ≤
      40 * s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2 := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos hy
  have hlogPos : 0 < Real.log s := by linarith
  have hpow : Real.log s ^ 4 ≤ Real.log s ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hlog (pow_nonneg hlogPos.le 4)
    simpa only [mul_one, ← pow_succ] using h
  have hlogBase := Real.log_le_sub_one_of_pos (iwaniecAuxWeightBase_pos level hs)
  have hden : Real.log level ^ 2 ≤ s ^ 2 * Real.log s ^ 5 + Real.log level ^ 2 := by
    have hnn := mul_nonneg (sq_nonneg s) (pow_nonneg hlogPos.le 5)
    linarith
  have hnum : 0 ≤ 5 * s * (2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) := by positivity
  have hpoly : 5 * s * (2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) ≤
      35 * s ^ 2 * Real.log s ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 25 * s ^ 2 by positivity)
    nlinarith
  have hfrac := (div_le_div_of_nonneg_left hnum (sq_pos_of_pos hL) hden).trans
    (div_le_div_of_nonneg_right hpoly (sq_nonneg (Real.log level)))
  have hlogBase' : Real.log (iwaniecAuxWeightBase level s) ≤
      s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2 := by
    unfold iwaniecAuxWeightBase at hlogBase ⊢
    linarith
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hlogBase' (show (0 : Real) ≤ 5 by norm_num)) hfrac
  unfold iwaniecAuxWeightLogDerivative
  convert hsum using 1 <;> ring

/-- Source's `100*c3*t^2*log^4(t)/log^2(y)` derivative loss, with the
actual G-corollary producer consumed. No xi-size premise is used here. -/
theorem neg_deriv_iwaniecAuxTau_gt_error_bound (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : 3 < s) (hlog : 1 ≤ Real.log s) :
    iwaniecAuxWeightPower level s * iwaniecAuxGKernel rank s * (1 - iwaniecAuxWeightError level s) <
      -deriv (iwaniecAuxTau rank level) s := by
  have hL := Real.log_pos hy
  have hlogPos : 0 < Real.log s := by linarith
  have hD := iwaniecAuxWeightLogDerivative_le_forty hy (show 1 ≤ s by linarith) hlog
  have hG := iwaniecAuxG_log_lt_kernel rank hs
  have hGPos := iwaniecAuxG_pos (rank + 1) (s := s) (by linarith)
  have hKPos := iwaniecAuxGKernel_pos rank hs.le
  have hWPos := iwaniecAuxWeightPower_pos level (s := s) (by linarith)
  have hCPos : 0 < iwaniecAuxCorollaryConstant := by
    linarith [iwaniecAuxCorollaryConstant_gt_three_hundred]
  have hscale : 0 < 100 * s ^ 2 * Real.log s ^ 4 / Real.log level ^ 2 := by positivity
  have hDhundred : iwaniecAuxWeightLogDerivative level s ≤
      (100 * s ^ 2 * Real.log s ^ 4 / Real.log level ^ 2) * Real.log s := by
    have hnn : 0 ≤ s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2 := by positivity
    have h40 : 40 * s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2 ≤
        (100 * s ^ 2 * Real.log s ^ 4 / Real.log level ^ 2) * Real.log s := by
      calc
        _ = 40 * (s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2) := by ring
        _ ≤ 100 * (s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num : (40 : Real) ≤ 100) hnn
        _ = _ := by ring
    exact hD.trans h40
  have hprod := mul_le_mul_of_nonneg_right hDhundred hGPos.le
  have hsmall := mul_lt_mul_of_pos_left hG hscale
  have hloss : iwaniecAuxWeightLogDerivative level s * iwaniecAuxG (rank + 1) s <
      iwaniecAuxWeightError level s * iwaniecAuxGKernel rank s := by
    calc
      _ ≤ (100 * s ^ 2 * Real.log s ^ 4 / Real.log level ^ 2) * Real.log s *
          iwaniecAuxG (rank + 1) s := hprod
      _ = (100 * s ^ 2 * Real.log s ^ 4 / Real.log level ^ 2) *
          (iwaniecAuxG (rank + 1) s * Real.log s) := by ring
      _ < (100 * s ^ 2 * Real.log s ^ 4 / Real.log level ^ 2) *
          (iwaniecAuxCorollaryConstant * iwaniecAuxGKernel rank s) := hsmall
      _ = _ := by unfold iwaniecAuxWeightError; ring
  rw [neg_deriv_iwaniecAuxTau rank hy hs]
  have hdiff : iwaniecAuxGKernel rank s * (1 - iwaniecAuxWeightError level s) <
      iwaniecAuxGKernel rank s - iwaniecAuxWeightLogDerivative level s * iwaniecAuxG (rank + 1) s := by
    nlinarith
  have h := mul_lt_mul_of_pos_left hdiff hWPos
  simpa only [mul_assoc] using h

end

end Erdos1212Kernel
