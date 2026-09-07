import Erdos1212Kernel.IwaniecMertensThetaNormalization

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem iwaniecTheta_error_coarse {x : Real} (hx : 0 ≤ x) :
    |Chebyshev.theta x - x| ≤ (Real.log 4 + 1) * x := by
  have h := abs_add_le (Chebyshev.theta x) (-x)
  rw [abs_of_nonneg (Chebyshev.theta_nonneg x), abs_neg, abs_of_nonneg hx, ← sub_eq_add_neg] at h
  have htheta := Chebyshev.theta_le_log4_mul_x hx
  nlinarith

theorem iwaniecMertensThetaBoundary_abs_bound {x : Real} (hx : 1 < x) :
    |iwaniecMertensThetaBoundary x| ≤ (Real.log 4 + 1) / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  unfold iwaniecMertensThetaBoundary
  rw [abs_div, abs_of_pos (mul_pos hx0 hl)]
  calc
    _ ≤ ((Real.log 4 + 1) * x) / (x * Real.log x) :=
      div_le_div_of_nonneg_right (iwaniecTheta_error_coarse hx0.le) (mul_pos hx0 hl).le
    _ = _ := by field_simp

/-- Only the elementary Chebyshev bound is needed to remove this
endpoint in the constant-identification limit. No PNT error rate is assumed. -/
theorem tendsto_iwaniecMertensThetaBoundary : Tendsto iwaniecMertensThetaBoundary atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := fun x : Real => (Real.log 4 + 1) / Real.log x) _
    (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
  simpa only [Real.norm_eq_abs] using iwaniecMertensThetaBoundary_abs_bound hx

theorem tendsto_iwaniecMertensThetaErrorDensity_primitive :
    Tendsto (fun x : Real => ∫ t in (2 : Real)..x, iwaniecMertensThetaErrorDensity t) atTop
      (nhds (Erdos696.Mertens.meisselMertensConstant - iwaniecMertensThetaBase)) := by
  have h := ((tendsto_iwaniecMertensRealRemainder.sub tendsto_iwaniecMertensThetaBoundary).sub_const
    iwaniecMertensThetaBase).add_const Erdos696.Mertens.meisselMertensConstant
  simp only [sub_self, zero_sub] at h
  have he : -iwaniecMertensThetaBase + Erdos696.Mertens.meisselMertensConstant =
      Erdos696.Mertens.meisselMertensConstant - iwaniecMertensThetaBase := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  rw [iwaniecMertensRealRemainder_theta_finite hx]
  ring

end

end Erdos1212Kernel
