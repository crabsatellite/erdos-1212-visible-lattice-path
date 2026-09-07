import Erdos1212Kernel.DeBruijnNormalizedComparison
import Erdos1212Kernel.DeBruijn1951SaddleDisplay

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

def deBruijnRho1951Main (u : Real) : Real :=
  Real.exp Real.eulerMascheroniConstant / Real.sqrt (2 * Real.pi * u) *
    Real.exp (-deBruijn1951SaddleIntegral (deBruijnSaddle u))

theorem deBruijnRho1951Main_pos {u : Real} (hu : 1 < u) : 0 < deBruijnRho1951Main u := by
  have hu0 : 0 < u := by linarith
  unfold deBruijnRho1951Main
  positivity

theorem deBruijnF1GaussianCoefficient_reciprocal :
    deBruijnF1GaussianCoefficient = 1 / Real.sqrt (2 * Real.pi) := by
  have hs := Real.sqrt_pos.mpr (show 0 < 2 * Real.pi by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  unfold deBruijnF1GaussianCoefficient
  apply (div_eq_div_iff (show 2 * Real.pi ≠ 0 by positivity) hs.ne').mpr
  nlinarith

theorem deBruijnRhoSaddleMain_eq (u : Real) :
    deBruijnRhoSaddleMain u = Real.exp Real.eulerMascheroniConstant * deBruijnSaddleHeight u /
      (Real.sqrt (2 * Real.pi) * Real.sqrt (deBruijnSaddleCurvature u)) := by
  rw [deBruijnRhoSaddleMain, deBruijnF1SaddleMain_eq, deBruijnF1GaussianCoefficient_reciprocal]
  ring

theorem deBruijnRho1951Main_eq {u : Real} (hu : 1 < u) :
    deBruijnRho1951Main u = Real.exp Real.eulerMascheroniConstant * deBruijnSaddleHeight u /
      (Real.sqrt (2 * Real.pi) * Real.sqrt u) := by
  unfold deBruijnRho1951Main
  rw [deBruijn1951SaddleIntegral_height hu, Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity)]
  ring

theorem deBruijnRho1951Main_ratio {u : Real} (hu : 1 < u) :
    deBruijnRhoSaddleMain u / deBruijnRho1951Main u = Real.sqrt (u / deBruijnSaddleCurvature u) := by
  have hu0 : 0 < u := by linarith
  have hp := Real.sqrt_pos.mpr (show 0 < 2 * Real.pi by positivity)
  have hs := Real.sqrt_pos.mpr (deBruijnSaddleCurvature_pos u)
  have huS := Real.sqrt_pos.mpr hu0
  rw [deBruijnRhoSaddleMain_eq, deBruijnRho1951Main_eq hu, Real.sqrt_div hu0.le]
  field_simp [(Real.exp_pos Real.eulerMascheroniConstant).ne', (deBruijnSaddleHeight_pos u).ne', hp.ne', hs.ne', huS.ne']

theorem tendsto_deBruijnRho1951Main_ratio :
    Tendsto (fun u : Real => deBruijnRhoSaddleMain u / deBruijnRho1951Main u) atTop (nhds 1) := by
  have h := (Real.continuous_sqrt.tendsto (1 : Real)).comp tendsto_deBruijnSaddleCurvature_inverse_ratio
  rw [Real.sqrt_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact (deBruijnRho1951Main_ratio hu).symm

theorem tendsto_deBruijnRho1951_ratio :
    Tendsto (fun u : Real => deBruijnRho u / deBruijnRho1951Main u) atTop (nhds 1) := by
  have h := tendsto_deBruijnRho_saddle_ratio.mul tendsto_deBruijnRho1951Main_ratio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  field_simp [(deBruijnRhoSaddleMain_pos u).ne', (deBruijnRho1951Main_pos hu).ne']

/-- The literal displayed formula (1.6), with its exact exponent integral
and numerical prefactor, obtained through the original Section 2 route. -/
theorem deBruijn1951_rho_asymptotic_formula :
    Tendsto (fun u : Real => deBruijnRho u /
      (Real.exp Real.eulerMascheroniConstant / Real.sqrt (2 * Real.pi * u) *
        Real.exp (-(∫ s in (0 : Real)..(deBruijnSaddle u), (s * Real.exp s - Real.exp s + 1) / s))))
      atTop (nhds 1) := tendsto_deBruijnRho1951_ratio

theorem deBruijn1951_rho_asymptotic : Asymptotics.IsEquivalent atTop deBruijnRho deBruijnRho1951Main :=
  Asymptotics.isEquivalent_of_tendsto_one tendsto_deBruijnRho1951_ratio

theorem iwaniecDickman_1951_asymptotic : Asymptotics.IsEquivalent atTop iwaniecDickman deBruijnRho1951Main := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply tendsto_deBruijnRho1951_ratio.congr'
  filter_upwards [eventually_ge_atTop (0 : Real)] with u hu
  rw [deBruijnRho_eq_dickman hu]
  rfl

end

end Erdos1212Kernel
