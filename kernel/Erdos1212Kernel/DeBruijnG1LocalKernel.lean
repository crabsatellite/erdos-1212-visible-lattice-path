import Erdos1212Kernel.DeBruijnG1Concentration

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnRealSaddlePhase_scaled_identity (u v : Real) :
    (deBruijnSaddleScaledPhase u (v : Complex)).re =
      deBruijnRealSaddlePhase u (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) -
        deBruijnRealSaddlePhase u (deBruijnSaddle u) := by
  unfold deBruijnSaddleScaledPhase
  rw [← Complex.ofReal_div, ← Complex.ofReal_add, ← deBruijnRealSaddlePhase_complex, ← deBruijnRealSaddlePhase_complex,
    ← Complex.ofReal_sub, Complex.ofReal_re]

theorem tendsto_deBruijnRealSaddlePhase_scaled (v : Real) :
    Tendsto (fun u : Real =>
      deBruijnRealSaddlePhase u (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) -
        deBruijnRealSaddlePhase u (deBruijnSaddle u)) atTop (nhds (v ^ 2 / 2)) := by
  have h := tendsto_deBruijnSaddleScaledPhase (v : Complex)
  have hv : (v : Complex) ^ 2 / 2 = ((v ^ 2 / 2 : Real) : Complex) := by push_cast <;> rfl
  rw [hv] at h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simp only [Complex.ofReal_re] at hr
  apply hr.congr'
  filter_upwards with u
  exact deBruijnRealSaddlePhase_scaled_identity u v

def deBruijnG1ScaledKernel (u b v : Real) : Real :=
  Real.exp (-(deBruijnRealSaddlePhase u (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) -
    deBruijnRealSaddlePhase u (deBruijnSaddle u))) * Real.exp (b * (v / Real.sqrt (deBruijnSaddleCurvature u))) *
      deBruijnSaddle u / (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u))

theorem deBruijnG1ScaledKernel_measurable (u b : Real) : Measurable (deBruijnG1ScaledKernel u b) := by
  have hx : Continuous (fun v : Real => deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) :=
    continuous_const.add (continuous_id.div_const _)
  have hp : Continuous (fun v : Real => Real.exp (-(deBruijnRealSaddlePhase u
      (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) - deBruijnRealSaddlePhase u (deBruijnSaddle u)))) :=
    Real.continuous_exp.comp ((((deBruijnRealSaddlePhase_continuous u).comp hx).sub continuous_const).neg)
  have hb : Continuous (fun v : Real => Real.exp (b * (v / Real.sqrt (deBruijnSaddleCurvature u)))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.div_const _))
  exact ((hp.mul hb).mul_const (deBruijnSaddle u)).measurable.div hx.measurable

theorem tendsto_deBruijnG1ScaledKernel (b v : Real) :
    Tendsto (fun u : Real => deBruijnG1ScaledKernel u b v) atTop (nhds (Real.exp (-v ^ 2 / 2))) := by
  have hd : Tendsto (fun u : Real => v / Real.sqrt (deBruijnSaddleCurvature u)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_deBruijnSaddle_sqrt_curvature
  have he : Tendsto (fun u : Real => Real.exp (b * (v / Real.sqrt (deBruijnSaddleCurvature u)))) atTop (nhds 1) := by
    have hb := hd.const_mul b
    simp only [mul_zero] at hb
    simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto (0 : Real)).comp hb
  have hsmall := hd.div_atTop tendsto_deBruijnSaddle
  have hbase : Tendsto (fun u : Real => 1 + (v / Real.sqrt (deBruijnSaddleCurvature u)) / deBruijnSaddle u) atTop (nhds 1) := by
    simpa only [add_zero] using hsmall.const_add 1
  have hratio : Tendsto (fun u : Real => deBruijnSaddle u / (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)))
      atTop (nhds 1) := by
    have h := hbase.inv₀ (by norm_num : (1 : Real) ≠ 0)
    simp only [inv_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
    have hsum : 1 + (v / Real.sqrt (deBruijnSaddleCurvature u)) / deBruijnSaddle u =
        (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) / deBruijnSaddle u := by
      field_simp [(deBruijnSaddle_pos hu).ne']
    rw [hsum, inv_div]
  have hphase := (Real.continuous_exp.tendsto (-(v ^ 2 / 2))).comp (tendsto_deBruijnRealSaddlePhase_scaled v).neg
  have h := (hphase.mul he).mul hratio
  simpa only [deBruijnG1ScaledKernel, mul_div_assoc, mul_one, neg_div] using h

end

end Erdos1212Kernel
