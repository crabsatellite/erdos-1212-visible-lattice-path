import Erdos1212Kernel.IwaniecWeightedQuadratureError

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def iwaniecQuadratureSourceConstant : Real := (2 / Real.log 2) * Real.exp 1

theorem iwaniecQuadratureSourceConstant_pos : 0 < iwaniecQuadratureSourceConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold iwaniecQuadratureSourceConstant
  positivity

theorem iwaniecLogKernel_pred_inverse_bound {x : Real} (hx : 3 ≤ x) :
    iwaniecLogKernel (x - 1) ≤ (2 / Real.log 2) * (1 / x) := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < x - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (x - 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogp : 0 < Real.log (x - 1) := hlog2.trans_le hlog
  have hden : x * Real.log 2 ≤ 2 * ((x - 1) * Real.log (x - 1)) := by
    have h1 := mul_le_mul_of_nonneg_right (show x ≤ 2 * (x - 1) by linarith) hlog2.le
    have h2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * (x - 1) by positivity)
    nlinarith
  unfold iwaniecLogKernel
  calc
    _ ≤ 2 / (x * Real.log 2) := (div_le_div_iff₀ (mul_pos hp hlogp) (mul_pos hx0 hlog2)).mpr (by simpa only [one_mul] using hden)
    _ = _ := by ring

theorem iwaniec_inverse_le_sqrt_log_exponential {x : Real} (hx : 1 ≤ x) :
    1 / x ≤ Real.exp 1 * Real.exp (-Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hs := Real.sq_sqrt hL
  have hroot : Real.sqrt (Real.log x) ≤ Real.log x + 1 := by
    nlinarith [sq_nonneg (Real.sqrt (Real.log x) - 1)]
  calc
    _ = Real.exp (-Real.log x) := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
    _ ≤ Real.exp (1 + -Real.sqrt (Real.log x)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_add _ _

theorem iwaniecLogKernel_pred_source_rate {x : Real} (hx : 3 ≤ x) :
    iwaniecLogKernel (x - 1) ≤ iwaniecQuadratureSourceConstant * Real.exp (-Real.sqrt (Real.log x)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ (2 / Real.log 2) * (1 / x) := iwaniecLogKernel_pred_inverse_bound hx
    _ ≤ (2 / Real.log 2) * (Real.exp 1 * Real.exp (-Real.sqrt (Real.log x))) :=
      mul_le_mul_of_nonneg_left (iwaniec_inverse_le_sqrt_log_exponential (by linarith)) (by positivity)
    _ = _ := by unfold iwaniecQuadratureSourceConstant; ring

/-- The quadrature part alone now has the exact exponential scale in
source Lemma 13, for integer endpoints. The prime remainder is separate. -/
theorem iwaniecWeightedLogLog_quadrature_source_error (b : Real → Real) {B A : Nat}
    (hB : 3 ≤ B) (hBA : B ≤ A)
    (hbMono : MonotoneOn b (Set.Icc (B : Real) (A : Real)))
    (hbNonneg : ∀ x ∈ Set.Icc (B : Real) (A : Real), 0 ≤ b x) :
    |iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A - iwaniecWeightedLogKernelIntegral b B A| ≤
      iwaniecQuadratureSourceConstant * b A * Real.exp (-Real.sqrt (Real.log (B : Real))) := by
  have h := iwaniecWeightedLogLog_quadrature_bounds b hB hBA hbMono hbNonneg
  have hBreal : (3 : Real) ≤ B := by exact_mod_cast hB
  have hK := iwaniecLogKernel_pred_source_rate hBreal
  have hpred : ((B - 1 : Nat) : Real) = (B : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one]
  rw [← hpred] at hK
  have hbA : 0 ≤ b A := hbNonneg A ⟨by exact_mod_cast hBA, le_rfl⟩
  rw [abs_of_nonneg h.1]
  calc
    _ ≤ b A * iwaniecLogKernel ((B - 1 : Nat) : Real) := h.2
    _ ≤ b A * (iwaniecQuadratureSourceConstant * Real.exp (-Real.sqrt (Real.log (B : Real)))) :=
      mul_le_mul_of_nonneg_left hK hbA
    _ = _ := by ring

theorem iwaniecWeightedPrimeIntegral_isolated_source_error (b : Real → Real) {B A : Nat}
    (hB : 3 ≤ B) (hBA : B ≤ A)
    (hbMono : MonotoneOn b (Set.Icc (B : Real) (A : Real)))
    (hbNonneg : ∀ x ∈ Set.Icc (B : Real) (A : Real), 0 ≤ b x) :
    |iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A -
        (∫ x in (B : Real)..(A : Real), b x / (x * Real.log x)) -
        iwaniecPrimeReciprocalRemainderAbel (fun n => b n) B A| ≤
      iwaniecQuadratureSourceConstant * b A * Real.exp (-Real.sqrt (Real.log (B : Real))) := by
  have h := iwaniecWeightedLogLog_quadrature_source_error b hB hBA hbMono hbNonneg
  have hi : iwaniecWeightedLogKernelIntegral b B A =
      ∫ x in (B : Real)..(A : Real), b x / (x * Real.log x) := by
    unfold iwaniecWeightedLogKernelIntegral
    apply intervalIntegral.integral_congr
    intro x _hx
    unfold iwaniecLogKernel
    ring
  rw [hi] at h
  rw [iwaniecPrimeReciprocalWeightedInterval_eq_logLogIncrement_add_remainder (fun n => b n) hBA]
  convert h using 1 <;> congr 1 <;> ring

end

end Erdos1212Kernel
