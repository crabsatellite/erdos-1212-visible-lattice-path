import Erdos1212Kernel.DeBruijnG1LeftTailBound
import Erdos1212Kernel.DeBruijnG1RegularPartLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem tendsto_deBruijnG1CurvatureFloor : Tendsto deBruijnG1CurvatureFloor atTop atTop :=
  tendsto_deBruijnSaddleCurvature.const_mul_atTop (Real.exp_pos (-1))

def deBruijnG1LeftMajorant (u : Real) : Real :=
  2 * u ^ 2 * Real.exp (-(Real.exp (-1) / 4) * u)

theorem tendsto_deBruijnG1LeftMajorant : Tendsto deBruijnG1LeftMajorant atTop (nhds 0) := by
  have h := (deBruijn_polynomial_exp_decay 2 (a := Real.exp (-1) / 4) (by positivity)).const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with u
  unfold deBruijnG1LeftMajorant
  ring

theorem eventually_deBruijnG1_normalized_left_bound {b : Real} (hb : 0 ≤ b) :
    ∀ᶠ u : Real in atTop, |deBruijnG1Normalizer u b * deBruijnG1LeftTail u b| ≤ deBruijnG1LeftMajorant u := by
  filter_upwards [eventually_gt_atTop (1 : Real), tendsto_deBruijnSaddle.eventually_ge_atTop 2,
    tendsto_deBruijnG1CurvatureFloor.eventually_ge_atTop 1] with u hu hξ hm
  have hC := deBruijnSaddleCurvature_lower_half hu hξ
  have hmU : Real.exp (-1) * (u / 2) ≤ deBruijnG1CurvatureFloor u :=
    mul_le_mul_of_nonneg_left hC (Real.exp_pos _).le
  have hE : Real.exp (-deBruijnG1CurvatureFloor u / 2) ≤ Real.exp (-(Real.exp (-1) / 4) * u) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hξ0 := (deBruijnSaddle_pos hu).le
  have hs0 := Real.sqrt_nonneg (deBruijnSaddleCurvature u)
  have hp : Real.sqrt (deBruijnSaddleCurvature u) * deBruijnSaddle u ≤ 2 * u ^ 2 := by
    have h := mul_le_mul (deBruijnSaddle_sqrt_le_parameter hu) (deBruijnSaddle_le_two_mul hu)
      hξ0 (show 0 ≤ u by linarith)
    nlinarith
  calc
    _ ≤ (Real.sqrt (deBruijnSaddleCurvature u) * deBruijnSaddle u * Real.exp (-deBruijnG1CurvatureFloor u / 2)) /
        deBruijnG1CurvatureFloor u := deBruijnG1_normalized_left_bound hu hξ hb
    _ ≤ Real.sqrt (deBruijnSaddleCurvature u) * deBruijnSaddle u * Real.exp (-deBruijnG1CurvatureFloor u / 2) :=
      div_le_self (by positivity) hm
    _ ≤ 2 * u ^ 2 * Real.exp (-(Real.exp (-1) / 4) * u) :=
      mul_le_mul hp hE (Real.exp_pos _).le (by positivity)
    _ = _ := rfl

theorem tendsto_deBruijnG1_normalized_left {b : Real} (hb : 0 ≤ b) :
    Tendsto (fun u : Real => deBruijnG1Normalizer u b * deBruijnG1LeftTail u b) atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := deBruijnG1LeftMajorant) _ tendsto_deBruijnG1LeftMajorant
  simpa only [Real.norm_eq_abs] using eventually_deBruijnG1_normalized_left_bound hb

end

end Erdos1212Kernel
