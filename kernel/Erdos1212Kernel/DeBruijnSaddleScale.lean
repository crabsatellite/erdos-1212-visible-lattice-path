import Erdos1212Kernel.DeBruijnSaddleGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem tendsto_deBruijnSaddleCurvature_ratio :
    Tendsto (fun u : Real => deBruijnSaddleCurvature u / u) atTop (nhds 1) := by
  have hi : Tendsto (fun u : Real => 1 / u) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
  have ha : Tendsto (fun u : Real => 1 - 1 / u) atTop (nhds 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : Real))).sub hi
  have hb := ha.div_atTop tendsto_deBruijnSaddle
  have h := (tendsto_const_nhds (x := (1 : Real))).sub hb
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact (deBruijnSaddleCurvature_ratio hu).symm

theorem tendsto_deBruijnSaddleCurvature : Tendsto deBruijnSaddleCurvature atTop atTop := by
  have hhalf := tendsto_deBruijnSaddleCurvature_ratio.eventually (Ioi_mem_nhds (show (1 / 2 : Real) < 1 by norm_num))
  apply tendsto_atTop_mono' atTop _
    ((tendsto_id : Tendsto (fun u : Real => u) atTop atTop).const_mul_atTop (show (0 : Real) < 1 / 2 by norm_num))
  filter_upwards [hhalf, eventually_gt_atTop (1 : Real)] with u hh hu
  have h := (lt_div_iff₀ (show 0 < u by linarith)).mp hh
  exact h.le

theorem tendsto_deBruijnSaddleCurvature_inverse_ratio :
    Tendsto (fun u : Real => u / deBruijnSaddleCurvature u) atTop (nhds 1) := by
  have h := tendsto_deBruijnSaddleCurvature_ratio.inv₀ (by norm_num : (1 : Real) ≠ 0)
  simpa only [inv_div, inv_one] using h

theorem tendsto_deBruijnSaddle_inverse :
    Tendsto (fun u : Real => 1 / deBruijnSaddle u) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_deBruijnSaddle

theorem tendsto_deBruijnSaddleCurvature_inverse :
    Tendsto (fun u : Real => 1 / deBruijnSaddleCurvature u) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_deBruijnSaddleCurvature

theorem tendsto_deBruijnSaddle_sqrt_curvature :
    Tendsto (fun u : Real => Real.sqrt (deBruijnSaddleCurvature u)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_deBruijnSaddleCurvature

theorem tendsto_deBruijnSaddle_gaussian_width :
    Tendsto (fun u : Real => 1 / Real.sqrt (deBruijnSaddleCurvature u)) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_deBruijnSaddle_sqrt_curvature

theorem tendsto_deBruijnSaddle_normalization_factor :
    Tendsto (fun u : Real => Real.exp (deBruijnSaddle u) /
      (deBruijnSaddle u * deBruijnSaddleCurvature u)) atTop (nhds 1) := by
  have h := tendsto_deBruijnSaddleCurvature_inverse_ratio.add
    (tendsto_deBruijnSaddle_inverse.mul tendsto_deBruijnSaddleCurvature_inverse)
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  have he : Real.exp (deBruijnSaddle u) = 1 + u * deBruijnSaddle u := by linarith [deBruijnSaddle_equation hu]
  rw [he]
  field_simp [(deBruijnSaddle_pos hu).ne', (deBruijnSaddleCurvature_pos u).ne']
  <;> ring

theorem tendsto_deBruijnSaddle_shifted_factor :
    Tendsto (fun u : Real => u / (deBruijnSaddle u * deBruijnSaddleCurvature u)) atTop (nhds 0) := by
  have h := tendsto_deBruijnSaddleCurvature_inverse_ratio.mul tendsto_deBruijnSaddle_inverse
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  field_simp [(deBruijnSaddle_pos hu).ne', (deBruijnSaddleCurvature_pos u).ne']

end

end Erdos1212Kernel
