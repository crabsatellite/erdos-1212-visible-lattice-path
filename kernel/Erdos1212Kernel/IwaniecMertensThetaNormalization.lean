import Erdos1212Kernel.IwaniecMertensThetaAbel
import Erdos1212Kernel.IwaniecMertensRealLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def iwaniecMertensThetaBoundary (x : Real) : Real :=
  (Chebyshev.theta x - x) / (x * Real.log x)

def iwaniecMertensThetaErrorDensity (x : Real) : Real :=
  (Chebyshev.theta x - x) * iwaniecMertensThetaKernel x

def iwaniecMertensThetaBase : Real := 1 / Real.log 2 - Real.log (Real.log 2)

theorem iwaniecMertensTheta_baseline_hasDerivAt {x : Real} (hx : 1 < x) :
    HasDerivAt (fun t : Real => Real.log (Real.log t) - 1 / Real.log t)
      (x * iwaniecMertensThetaKernel x) x := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have hlog := Real.hasDerivAt_log hx0.ne'
  have h := (hlog.log hl.ne').sub ((hasDerivAt_const x (1 : Real)).div hlog hl.ne')
  apply h.congr_deriv
  unfold iwaniecMertensThetaKernel
  field_simp [hx0.ne', hl.ne']
  <;> ring

theorem iwaniecMertensTheta_baseline_intervalIntegrable {a b : Real} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => t * iwaniecMertensThetaKernel t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_id.mul (iwaniecMertensThetaKernel_continuousOn.mono (fun x hx => (lt_min ha hb).trans_le hx.1))

theorem iwaniecMertensThetaErrorDensity_intervalIntegrable {a b : Real} (ha : 2 ≤ a) (hb : a ≤ b) :
    IntervalIntegrable iwaniecMertensThetaErrorDensity volume a b := by
  have hi := (iwaniecTheta_weight_intervalIntegrable ha hb).sub
    (iwaniecMertensTheta_baseline_intervalIntegrable (by linarith : 1 < a) (by linarith : 1 < b))
  have hEq : (fun t : Real => Chebyshev.theta t * iwaniecMertensThetaKernel t - t * iwaniecMertensThetaKernel t) =
      iwaniecMertensThetaErrorDensity := by
    funext t
    unfold iwaniecMertensThetaErrorDensity
    ring
  rwa [hEq] at hi

theorem iwaniecMertensTheta_baseline_integral {x : Real} (hx : 2 ≤ x) :
    (∫ t in (2 : Real)..x, t * iwaniecMertensThetaKernel t) =
      Real.log (Real.log x) - 1 / Real.log x + iwaniecMertensThetaBase := by
  have hi := iwaniecMertensTheta_baseline_intervalIntegrable (by norm_num : (1 : Real) < 2) (by linarith : 1 < x)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
    rw [Set.uIcc_of_le hx] at ht
    exact iwaniecMertensTheta_baseline_hasDerivAt (by linarith [ht.1] : 1 < t)) hi
  rw [h]
  unfold iwaniecMertensThetaBase
  ring

/-- Finite, exactly normalized precursor to RS (4.20), retaining the
actual previously constructed Meissel-Mertens constant. -/
theorem iwaniecMertensRealRemainder_theta_finite {x : Real} (hx : 2 ≤ x) :
    iwaniecMertensRealRemainder x = iwaniecMertensThetaBoundary x + iwaniecMertensThetaBase -
      Erdos696.Mertens.meisselMertensConstant + ∫ t in (2 : Real)..x, iwaniecMertensThetaErrorDensity t := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos (show 1 < x by linarith)
  have hsplit : Chebyshev.theta x / (x * Real.log x) = iwaniecMertensThetaBoundary x + 1 / Real.log x := by
    unfold iwaniecMertensThetaBoundary
    field_simp [hx0.ne', hl.ne']
    <;> ring
  have hfun : (fun t : Real => Chebyshev.theta t * iwaniecMertensThetaKernel t) =
      (fun t : Real => iwaniecMertensThetaErrorDensity t + t * iwaniecMertensThetaKernel t) := by
    funext t
    unfold iwaniecMertensThetaErrorDensity
    ring
  unfold iwaniecMertensRealRemainder
  rw [iwaniecPrimeReciprocalReal_theta_formula hx, hsplit, hfun,
    intervalIntegral.integral_add (iwaniecMertensThetaErrorDensity_intervalIntegrable le_rfl hx)
      (iwaniecMertensTheta_baseline_intervalIntegrable (by norm_num : (1 : Real) < 2) (by linarith : 1 < x)),
    iwaniecMertensTheta_baseline_integral hx]
  ring

end

end Erdos1212Kernel
