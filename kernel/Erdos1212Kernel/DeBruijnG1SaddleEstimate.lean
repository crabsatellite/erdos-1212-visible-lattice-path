import Erdos1212Kernel.DeBruijnG1SaddleNormalized
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

/-- The two source main terms, b=1 in (2.10) and b=0 in (2.11).
In both cases the saddle and curvature are evaluated at u, not u-1. -/
def deBruijnG1SaddleMain (u b : Real) : Real :=
  Real.exp (-deBruijnRealSaddlePhase u (deBruijnSaddle u)) * Real.exp (b * deBruijnSaddle u) /
    deBruijnSaddle u * Real.sqrt (2 * Real.pi / deBruijnSaddleCurvature u)

theorem deBruijnG1SaddleMain_pos {u : Real} (hu : 1 < u) (b : Real) : 0 < deBruijnG1SaddleMain u b := by
  have hξ := deBruijnSaddle_pos hu
  have hC := deBruijnSaddleCurvature_pos u
  unfold deBruijnG1SaddleMain
  positivity

theorem deBruijnG1SaddleMain_normalized {u : Real} (hu : 1 < u) (b : Real) :
    deBruijnG1Normalizer u b * deBruijnG1SaddleMain u b = Real.sqrt (2 * Real.pi) := by
  have hξ := (deBruijnSaddle_pos hu).ne'
  have hs := (Real.sqrt_pos.mpr (deBruijnSaddleCurvature_pos u)).ne'
  have he : deBruijnSaddleHeight u * Real.exp (-b * deBruijnSaddle u) *
      Real.exp (-deBruijnRealSaddlePhase u (deBruijnSaddle u)) * Real.exp (b * deBruijnSaddle u) = 1 := by
    rw [deBruijnSaddleHeight_eq_phase]
    simp only [← Real.exp_add]
    rw [show deBruijnRealSaddlePhase u (deBruijnSaddle u) + -b * deBruijnSaddle u +
      -deBruijnRealSaddlePhase u (deBruijnSaddle u) + b * deBruijnSaddle u = 0 by ring, Real.exp_zero]
  unfold deBruijnG1Normalizer deBruijnG1SaddleMain
  rw [Real.sqrt_div (show 0 ≤ 2 * Real.pi by positivity) (deBruijnSaddleCurvature u)]
  calc
    _ = (deBruijnSaddleHeight u * Real.exp (-b * deBruijnSaddle u) *
        Real.exp (-deBruijnRealSaddlePhase u (deBruijnSaddle u)) * Real.exp (b * deBruijnSaddle u)) *
        (deBruijnSaddle u / deBruijnSaddle u) *
        (Real.sqrt (deBruijnSaddleCurvature u) / Real.sqrt (deBruijnSaddleCurvature u)) * Real.sqrt (2 * Real.pi) := by ring
    _ = _ := by rw [he, div_self hξ, div_self hs]; ring

theorem deBruijnG1_saddle_ratio_eq {u : Real} (hu : 1 < u) (b : Real) :
    deBruijn1951G1 (u - 1 + b) / deBruijnG1SaddleMain u b =
      (deBruijnG1Normalizer u b * deBruijn1951G1 (u - 1 + b)) / Real.sqrt (2 * Real.pi) := by
  rw [← deBruijnG1SaddleMain_normalized hu b]
  field_simp [(deBruijnG1Normalizer_pos hu b).ne', (deBruijnG1SaddleMain_pos hu b).ne']

theorem tendsto_deBruijnG1_saddle_ratio {b : Real} (hb : b ∈ Set.Icc (0 : Real) 1) :
    Tendsto (fun u : Real => deBruijn1951G1 (u - 1 + b) / deBruijnG1SaddleMain u b) atTop (nhds 1) := by
  have h := (tendsto_deBruijnG1_normalized hb).div_const (Real.sqrt (2 * Real.pi))
  rw [div_self (show Real.sqrt (2 * Real.pi) ≠ 0 by positivity)] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact (deBruijnG1_saddle_ratio_eq hu b).symm

theorem deBruijnG1_saddle_asymptotic {b : Real} (hb : b ∈ Set.Icc (0 : Real) 1) :
    Asymptotics.IsEquivalent atTop (fun u : Real => deBruijn1951G1 (u - 1 + b)) (fun u => deBruijnG1SaddleMain u b) :=
  Asymptotics.isEquivalent_of_tendsto_one (tendsto_deBruijnG1_saddle_ratio hb)

/-- Literal display of de Bruijn 1951 (2.10). -/
theorem deBruijn1951_G1_saddle_formula :
    Tendsto (fun u : Real => deBruijn1951G1 u /
      (Real.exp (-(-u * deBruijnSaddle u + deBruijn1951ExpIntegral (deBruijnSaddle u))) *
        Real.exp (deBruijnSaddle u) / deBruijnSaddle u *
        Real.sqrt (2 * Real.pi / deBruijnSaddleCurvature u))) atTop (nhds 1) := by
  simpa only [sub_add_cancel, deBruijnG1SaddleMain, deBruijnRealSaddlePhase, one_mul] using
    (tendsto_deBruijnG1_saddle_ratio (b := 1) (by constructor <;> norm_num))

/-- Literal display of de Bruijn 1951 (2.11), retaining xi(u), not xi(u-1). -/
theorem deBruijn1951_G1_shifted_saddle_formula :
    Tendsto (fun u : Real => deBruijn1951G1 (u - 1) /
      (Real.exp (-(-u * deBruijnSaddle u + deBruijn1951ExpIntegral (deBruijnSaddle u))) /
        deBruijnSaddle u * Real.sqrt (2 * Real.pi / deBruijnSaddleCurvature u))) atTop (nhds 1) := by
  simpa only [add_zero, deBruijnG1SaddleMain, deBruijnRealSaddlePhase, zero_mul, Real.exp_zero, mul_one] using
    (tendsto_deBruijnG1_saddle_ratio (b := 0) (by constructor <;> norm_num))

end

end Erdos1212Kernel
