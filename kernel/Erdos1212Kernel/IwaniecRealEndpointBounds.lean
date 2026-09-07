import Erdos1212Kernel.IwaniecLemma13Initial

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 600000

def iwaniecRealEndpointConstant : Real := Real.exp 1 / Real.log 2

theorem iwaniecRealEndpointConstant_pos : 0 < iwaniecRealEndpointConstant :=
  div_pos (Real.exp_pos _) (Real.log_pos (by norm_num))

theorem iwaniecLogKernel_source_rate_two {x : Real} (hx : 2 ≤ x) :
    iwaniecLogKernel x ≤ iwaniecRealEndpointConstant * Real.exp (-Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogInv := one_div_le_one_div_of_le hlog2 hlog
  have hxInv := iwaniec_inverse_le_sqrt_log_exponential (show 1 ≤ x by linarith)
  calc
    _ = (1 / x) * (1 / Real.log x) := by unfold iwaniecLogKernel; ring
    _ ≤ (1 / x) * (1 / Real.log 2) := mul_le_mul_of_nonneg_left hlogInv (by positivity)
    _ ≤ (Real.exp 1 * Real.exp (-Real.sqrt (Real.log x))) * (1 / Real.log 2) :=
      mul_le_mul_of_nonneg_right hxInv (by positivity)
    _ = _ := by unfold iwaniecRealEndpointConstant; ring

theorem iwaniecShortWeightedIntegral_source_bound (b : Real → Real) {B u v M : Real}
    (hB : 2 ≤ B) (hBu : B ≤ u) (huv : u ≤ v) (hlen : v - u ≤ 1)
    (hb : ∀ x ∈ Icc u v, 0 ≤ b x ∧ b x ≤ M) :
    |∫ x in u..v, b x / (x * Real.log x)| ≤
      iwaniecRealEndpointConstant * M * Real.exp (-Real.sqrt (Real.log B)) := by
  have hM : 0 ≤ M := (hb u ⟨le_rfl, huv⟩).1.trans (hb u ⟨le_rfl, huv⟩).2
  have hK : 0 ≤ iwaniecLogKernel B := (iwaniecLogKernel_pos (by linarith : 1 < B)).le
  calc
    _ ≤ (v - u) * M * iwaniecLogKernel B := iwaniecShortWeightedIntegral_bound b hB hBu huv hb
    _ ≤ M * iwaniecLogKernel B := by
      have hh := mul_le_mul_of_nonneg_right hlen (mul_nonneg hM hK)
      simpa only [one_mul, mul_assoc] using hh
    _ ≤ M * (iwaniecRealEndpointConstant * Real.exp (-Real.sqrt (Real.log B))) :=
      mul_le_mul_of_nonneg_left (iwaniecLogKernel_source_rate_two hB) hM
    _ = _ := by ring

end

end Erdos1212Kernel
