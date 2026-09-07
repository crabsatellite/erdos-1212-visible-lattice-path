import Erdos1212Kernel.DeBruijnF1SaddleEstimate
import Erdos1212Kernel.DeBruijnG1SaddleEstimate

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

theorem deBruijnF1G1_saddle_main_product (u b : Real) :
    deBruijnF1SaddleMain u * deBruijnG1SaddleMain u b =
      Real.exp (b * deBruijnSaddle u) / (deBruijnSaddle u * deBruijnSaddleCurvature u) := by
  have he : deBruijnSaddleHeight u * Real.exp (-deBruijnRealSaddlePhase u (deBruijnSaddle u)) = 1 := by
    rw [deBruijnSaddleHeight_eq_phase, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hs : Real.sqrt (2 * Real.pi / deBruijnSaddleCurvature u) ^ 2 = 2 * Real.pi / deBruijnSaddleCurvature u :=
    Real.sq_sqrt (div_nonneg (by positivity) (deBruijnSaddleCurvature_pos u).le)
  calc
    _ = (deBruijnSaddleHeight u * Real.exp (-deBruijnRealSaddlePhase u (deBruijnSaddle u))) *
        Real.exp (b * deBruijnSaddle u) / deBruijnSaddle u *
        (Real.sqrt (2 * Real.pi / deBruijnSaddleCurvature u) ^ 2) / (2 * Real.pi) := by
      unfold deBruijnF1SaddleMain deBruijnG1SaddleMain
      ring
    _ = _ := by rw [he, hs]; field_simp [Real.pi_ne_zero]

theorem deBruijnF1G1_product_identity {u : Real} (hu : 1 < u) (b : Real) :
    deBruijnF1 u * deBruijn1951G1 (u - 1 + b) =
      ((deBruijnF1 u / deBruijnF1SaddleMain u) * (deBruijn1951G1 (u - 1 + b) / deBruijnG1SaddleMain u b)) *
        (Real.exp (b * deBruijnSaddle u) / (deBruijnSaddle u * deBruijnSaddleCurvature u)) := by
  rw [← deBruijnF1G1_saddle_main_product]
  field_simp [(deBruijnF1SaddleMain_pos u).ne', (deBruijnG1SaddleMain_pos hu b).ne']

/-- First asymptotic equivalence in source (2.12), before taking its limit. -/
theorem deBruijnF1G1_product_asymptotic :
    Asymptotics.IsEquivalent atTop (fun u : Real => deBruijnF1 u * deBruijn1951G1 u)
      (fun u => Real.exp (deBruijnSaddle u) / (deBruijnSaddle u * deBruijnSaddleCurvature u)) := by
  have h := deBruijnF1_saddle_asymptotic.mul (deBruijnG1_saddle_asymptotic (b := 1) (by constructor <;> norm_num))
  change Asymptotics.IsEquivalent atTop (fun u : Real => deBruijnF1 u * deBruijn1951G1 (u - 1 + 1))
    (fun u : Real => deBruijnF1SaddleMain u * deBruijnG1SaddleMain u 1) at h
  simpa only [sub_add_cancel, deBruijnF1G1_saddle_main_product, one_mul] using h

theorem tendsto_deBruijnF1G1_product :
    Tendsto (fun u : Real => deBruijnF1 u * deBruijn1951G1 u) atTop (nhds 1) := by
  have h := (tendsto_deBruijnF1_saddle_ratio.mul
    (tendsto_deBruijnG1_saddle_ratio (b := 1) (by constructor <;> norm_num))).mul tendsto_deBruijnSaddle_normalization_factor
  simp only [one_mul, sub_add_cancel] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  simpa only [sub_add_cancel, one_mul] using (deBruijnF1G1_product_identity hu 1).symm

/-- Source (2.13) is used with its actual vanishing factor, not merely
with pointwise saddle limits for the separate functions. -/
theorem tendsto_deBruijnF1G1_shifted_product :
    Tendsto (fun u : Real => u * deBruijnF1 u * deBruijn1951G1 (u - 1)) atTop (nhds 0) := by
  have h := (tendsto_deBruijnF1_saddle_ratio.mul
    (tendsto_deBruijnG1_saddle_ratio (b := 0) (by constructor <;> norm_num))).mul tendsto_deBruijnSaddle_shifted_factor
  simp only [one_mul, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  have hid := deBruijnF1G1_product_identity hu 0
  simp only [add_zero, zero_mul, Real.exp_zero] at hid
  calc
    _ = u * (((deBruijnF1 u / deBruijnF1SaddleMain u) * (deBruijn1951G1 (u - 1) / deBruijnG1SaddleMain u 0)) *
        (1 / (deBruijnSaddle u * deBruijnSaddleCurvature u))) := by ring
    _ = u * (deBruijnF1 u * deBruijn1951G1 (u - 1)) := by rw [← hid]
    _ = _ := by ring

end

end Erdos1212Kernel
