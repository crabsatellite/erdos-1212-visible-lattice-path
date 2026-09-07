import Erdos1212Kernel.DeBruijnSaddleTaylor
import Erdos1212Kernel.DeBruijnSaddleScale

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

def deBruijnSaddleScaledPhase (u : Real) (w : Complex) : Complex :=
  deBruijnSaddlePhase u ((deBruijnSaddle u : Complex) + w / (Real.sqrt (deBruijnSaddleCurvature u) : Complex)) -
    deBruijnSaddlePhase u (deBruijnSaddle u : Complex)

theorem deBruijnSaddleScaledPhase_error_bound {u : Real} (hu : 1 < u) (w : Complex) :
    ‖deBruijnSaddleScaledPhase u w - w ^ 2 / 2‖ ≤
      ‖w‖ ^ 3 * Real.exp (‖w‖ / Real.sqrt (deBruijnSaddleCurvature u)) / Real.sqrt (deBruijnSaddleCurvature u) := by
  let s := Real.sqrt (deBruijnSaddleCurvature u)
  have hs : 0 < s := Real.sqrt_pos.mpr (deBruijnSaddleCurvature_pos u)
  have hsq : s ^ 2 = deBruijnSaddleCurvature u := Real.sq_sqrt (deBruijnSaddleCurvature_pos u).le
  have hsC : (s : Complex) ≠ 0 := by exact_mod_cast hs.ne'
  have hsqC : (s : Complex) ^ 2 = (deBruijnSaddleCurvature u : Complex) := by exact_mod_cast hsq
  have hquad : ((w / (s : Complex)) ^ 2 / 2) * (deBruijnSaddleCurvature u : Complex) = w ^ 2 / 2 := by
    rw [← hsqC]
    field_simp
    <;> ring
  have hn : ‖w / (s : Complex)‖ = ‖w‖ / s := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hb : (‖w‖ / s) ^ 3 * Real.exp (‖w‖ / s) * deBruijnSaddleCurvature u =
      ‖w‖ ^ 3 * Real.exp (‖w‖ / s) / s := by
    rw [← hsq]
    field_simp
    <;> ring
  have h := deBruijnSaddlePhase_taylor_bound hu (w / (s : Complex))
  rw [hquad, hn, hb] at h
  exact h

theorem tendsto_deBruijnSaddleScaledPhase_error (w : Complex) :
    Tendsto (fun u : Real => deBruijnSaddleScaledPhase u w - w ^ 2 / 2) atTop (nhds 0) := by
  have h1 : Tendsto (fun u : Real => ‖w‖ / Real.sqrt (deBruijnSaddleCurvature u)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_deBruijnSaddle_sqrt_curvature
  have h3 : Tendsto (fun u : Real => ‖w‖ ^ 3 / Real.sqrt (deBruijnSaddleCurvature u)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_deBruijnSaddle_sqrt_curvature
  have he : Tendsto (fun u : Real => Real.exp (‖w‖ / Real.sqrt (deBruijnSaddleCurvature u))) atTop (nhds 1) := by
    simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto (0 : Real)).comp h1
  have hb : Tendsto (fun u : Real => ‖w‖ ^ 3 * Real.exp (‖w‖ / Real.sqrt (deBruijnSaddleCurvature u)) /
      Real.sqrt (deBruijnSaddleCurvature u)) atTop (nhds 0) := by
    simpa only [div_mul_eq_mul_div, zero_mul] using h3.mul he
  apply squeeze_zero_norm' (a := fun u : Real => ‖w‖ ^ 3 * Real.exp (‖w‖ / Real.sqrt (deBruijnSaddleCurvature u)) /
    Real.sqrt (deBruijnSaddleCurvature u)) _ hb
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact deBruijnSaddleScaledPhase_error_bound hu w

theorem tendsto_deBruijnSaddleScaledPhase (w : Complex) :
    Tendsto (fun u : Real => deBruijnSaddleScaledPhase u w) atTop (nhds (w ^ 2 / 2)) := by
  have h := (tendsto_deBruijnSaddleScaledPhase_error w).add_const (w ^ 2 / 2)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards with u
  ring

theorem deBruijnF1_scaled_integrand_identity (u : Real) (w : Complex) :
    deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) + w / (Real.sqrt (deBruijnSaddleCurvature u) : Complex)) /
      deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex) = Complex.exp (deBruijnSaddleScaledPhase u w) := by
  rw [deBruijnF1Integrand_eq_saddlePhase, deBruijnF1Integrand_eq_saddlePhase, ← Complex.exp_sub]
  rfl

theorem tendsto_deBruijnF1_scaled_integrand (w : Complex) :
    Tendsto (fun u : Real =>
      deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) + w / (Real.sqrt (deBruijnSaddleCurvature u) : Complex)) /
        deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)) atTop (nhds (Complex.exp (w ^ 2 / 2))) := by
  have h := Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_deBruijnSaddleScaledPhase w)
  apply h.congr'
  filter_upwards with u
  exact (deBruijnF1_scaled_integrand_identity u w).symm

theorem deBruijnSaddle_vertical_coordinate (u v : Real) :
    (((v / Real.sqrt (deBruijnSaddleCurvature u) : Real) : Complex) * Complex.I) =
      ((v : Complex) * Complex.I) / (Real.sqrt (deBruijnSaddleCurvature u) : Complex) := by
  rw [Complex.ofReal_div, div_mul_eq_mul_div]

/-- Pointwise Gaussian limit for the actual F1 integrand along the
vertical line through the source saddle, at its proved curvature scale. -/
theorem deBruijnF1_vertical_local_gaussian (v : Real) :
    Tendsto (fun u : Real =>
      deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) +
        ((v / Real.sqrt (deBruijnSaddleCurvature u) : Real) : Complex) * Complex.I) /
      deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)) atTop
        (nhds ((Real.exp (-v ^ 2 / 2) : Real) : Complex)) := by
  have h := tendsto_deBruijnF1_scaled_integrand ((v : Complex) * Complex.I)
  have he : Complex.exp (((v : Complex) * Complex.I) ^ 2 / 2) = ((Real.exp (-v ^ 2 / 2) : Real) : Complex) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards with u
  rw [deBruijnSaddle_vertical_coordinate]

end

end Erdos1212Kernel
