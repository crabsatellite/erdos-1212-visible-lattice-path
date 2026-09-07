import Erdos1212Kernel.DeBruijnRhoSaddleNormalization
import Erdos1212Kernel.DeBruijnLogErrorScaleLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

theorem deBruijnRho1951Main_log {u : Real} (hu : 1 < u) :
    Real.log (deBruijnRho1951Main u) = Real.eulerMascheroniConstant -
      (Real.log (2 * Real.pi) + Real.log u) / 2 - deBruijn1951SaddleIntegral (deBruijnSaddle u) := by
  have hu0 : 0 < u := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hs : 0 < Real.sqrt (2 * Real.pi * u) := by positivity
  unfold deBruijnRho1951Main
  rw [Real.log_mul (div_ne_zero (Real.exp_pos _).ne' hs.ne') (Real.exp_pos _).ne',
    Real.log_div (Real.exp_pos _).ne' hs.ne', Real.log_exp, Real.log_exp,
    Real.log_sqrt (by positivity), Real.log_mul hp.ne' hu0.ne']
  ring

theorem deBruijnRho_log_saddle_identity {u : Real} (hu : 1 < u) :
    Real.log (deBruijnRho u) + deBruijn1951SaddleIntegral (deBruijnSaddle u) =
      Real.eulerMascheroniConstant - (Real.log (2 * Real.pi) + Real.log u) / 2 +
        Real.log (deBruijnRho u / deBruijnRho1951Main u) := by
  have hρ : 0 < deBruijnRho u := by
    rw [deBruijnRho_eq_dickman (by linarith : 0 ≤ u)]
    exact iwaniecDickman_pos (by linarith)
  rw [Real.log_div hρ.ne' (deBruijnRho1951Main_pos hu).ne', deBruijnRho1951Main_log hu]
  ring

theorem tendsto_deBruijnRho_log_saddle_ratio :
    Tendsto (fun u : Real => Real.log (deBruijnRho u / deBruijnRho1951Main u)) atTop (nhds 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1 : Real) ≠ 0)).tendsto.comp tendsto_deBruijnRho1951_ratio
  simpa only [Real.log_one] using h

theorem deBruijnRho_log_saddle_bound {u : Real} (hu : 1 < u)
    (hr : |Real.log (deBruijnRho u / deBruijnRho1951Main u)| ≤ 1) :
    |Real.log (deBruijnRho u) + deBruijn1951SaddleIntegral (deBruijnSaddle u)| ≤
      |Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| + 1 + Real.log u := by
  have hL := Real.log_pos hu
  have hnum : |(Real.log (2 * Real.pi) + Real.log u) / 2| ≤ |Real.log (2 * Real.pi)| + Real.log u := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      _ ≤ |Real.log (2 * Real.pi) + Real.log u| := div_le_self (abs_nonneg _) (by norm_num)
      _ ≤ _ := by simpa only [abs_of_pos hL] using abs_add_le (Real.log (2 * Real.pi)) (Real.log u)
  have hpre := abs_add_le Real.eulerMascheroniConstant (-((Real.log (2 * Real.pi) + Real.log u) / 2))
  rw [abs_neg, ← sub_eq_add_neg] at hpre
  have hsum := abs_add_le (Real.eulerMascheroniConstant - (Real.log (2 * Real.pi) + Real.log u) / 2)
    (Real.log (deBruijnRho u / deBruijnRho1951Main u))
  rw [deBruijnRho_log_saddle_identity hu]
  linarith

theorem deBruijnRho_log_saddle_error :
    Asymptotics.IsBigO atTop (fun u : Real => Real.log (deBruijnRho u) + deBruijn1951SaddleIntegral (deBruijnSaddle u))
      deBruijnRhoLogErrorScale := by
  have hnorm : Tendsto (fun u : Real => |Real.log (deBruijnRho u / deBruijnRho1951Main u)|) atTop (nhds 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using tendsto_deBruijnRho_log_saddle_ratio.norm
  have hr := hnorm.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
  let D := |Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| + 1
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_gt_atTop (1 : Real), hr, eventually_deBruijnRhoLogErrorScale_ge_log,
    tendsto_deBruijnRhoLogErrorScale.eventually_ge_atTop D,
    tendsto_deBruijnRhoLogErrorScale.eventually_ge_atTop 0] with u hu hratio hL hD hpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  have h := deBruijnRho_log_saddle_bound hu hratio.le
  dsimp [D] at hD
  linarith

end

end Erdos1212Kernel
