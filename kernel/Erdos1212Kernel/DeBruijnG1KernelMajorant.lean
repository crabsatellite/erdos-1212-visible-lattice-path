import Erdos1212Kernel.DeBruijnG1LocalKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1700000

def deBruijnG1GaussianConstant : Real := Real.exp (-1) / 2

def deBruijnG1GaussianMajorant (v : Real) : Real :=
  2 * Real.exp (2 / deBruijnG1GaussianConstant) * Real.exp (-(deBruijnG1GaussianConstant / 2) * v ^ 2)

theorem deBruijnG1GaussianConstant_pos : 0 < deBruijnG1GaussianConstant := by unfold deBruijnG1GaussianConstant; positivity

theorem deBruijnG1_abs_quadratic_bound (v : Real) :
    |v| ≤ deBruijnG1GaussianConstant / 2 * v ^ 2 + 2 / deBruijnG1GaussianConstant := by
  have hc := deBruijnG1GaussianConstant_pos
  by_cases hv : |v| ≤ 2 / deBruijnG1GaussianConstant
  · have hq : 0 ≤ deBruijnG1GaussianConstant / 2 * v ^ 2 := by positivity
    linarith
  · have htwo : 2 ≤ deBruijnG1GaussianConstant * |v| := by
      have h := (div_lt_iff₀ hc).mp (lt_of_not_ge hv)
      nlinarith
    have hq : 2 * |v| ≤ deBruijnG1GaussianConstant * v ^ 2 := by
      calc
        _ ≤ (deBruijnG1GaussianConstant * |v|) * |v| := mul_le_mul_of_nonneg_right htwo (abs_nonneg v)
        _ = deBruijnG1GaussianConstant * |v| ^ 2 := by ring
        _ = _ := by rw [sq_abs]
    have hconst : 0 ≤ 2 / deBruijnG1GaussianConstant := by positivity
    linarith

theorem deBruijnG1GaussianMajorant_integrable : Integrable deBruijnG1GaussianMajorant := by
  have hc : 0 < deBruijnG1GaussianConstant / 2 := by have h := deBruijnG1GaussianConstant_pos; positivity
  exact (integrable_exp_neg_mul_sq hc).const_mul (2 * Real.exp (2 / deBruijnG1GaussianConstant))

theorem deBruijnG1ScaledKernel_bound {u b v : Real} (hu : 1 < u) (hξ : 2 ≤ deBruijnSaddle u)
    (hs1 : 1 ≤ Real.sqrt (deBruijnSaddleCurvature u)) (hb : b ∈ Set.Icc (0 : Real) 1)
    (hv : -Real.sqrt (deBruijnSaddleCurvature u) ≤ v) :
    |deBruijnG1ScaledKernel u b v| ≤ deBruijnG1GaussianMajorant v := by
  let s := Real.sqrt (deBruijnSaddleCurvature u)
  have hs : 0 < s := Real.sqrt_pos.mpr (deBruijnSaddleCurvature_pos u)
  have hd : -1 ≤ v / s := (le_div_iff₀ hs).mpr (by change -1 * s ≤ v; dsimp [s]; linarith)
  have hx : 0 < deBruijnSaddle u + v / s := by linarith
  have hr : deBruijnSaddle u / (deBruijnSaddle u + v / s) ≤ 2 := (div_le_iff₀ hx).mpr (by linarith)
  have hr0 : 0 ≤ deBruijnSaddle u / (deBruijnSaddle u + v / s) := div_nonneg (deBruijnSaddle_pos hu).le hx.le
  have hP := deBruijnRealSaddlePhase_quadratic_lower hu (x := deBruijnSaddle u + v / s) (by linarith)
  have hsq : (v / s) ^ 2 * deBruijnSaddleCurvature u = v ^ 2 := by
    rw [div_pow, show s ^ 2 = deBruijnSaddleCurvature u from Real.sq_sqrt (deBruijnSaddleCurvature_pos u).le]
    exact div_mul_cancel₀ _ (deBruijnSaddleCurvature_pos u).ne'
  have heq : deBruijnG1CurvatureFloor u / 2 * (deBruijnSaddle u + v / s - deBruijnSaddle u) ^ 2 =
      deBruijnG1GaussianConstant * v ^ 2 := by
    have harg : deBruijnSaddle u + v / s - deBruijnSaddle u = v / s := by ring
    rw [harg]
    unfold deBruijnG1CurvatureFloor deBruijnG1GaussianConstant
    calc
      _ = (Real.exp (-1) / 2) * ((v / s) ^ 2 * deBruijnSaddleCurvature u) := by ring
      _ = _ := by rw [hsq]
  rw [heq] at hP
  have hEP := Real.exp_le_exp.mpr (neg_le_neg hP)
  have hdabs : |v / s| ≤ |v| := by
    rw [abs_div, abs_of_pos hs]
    exact div_le_self (abs_nonneg v) hs1
  have hbδ : b * (v / s) ≤ |v| := by
    calc
      _ ≤ b * |v / s| := mul_le_mul_of_nonneg_left (le_abs_self _) hb.1
      _ ≤ |v / s| := by nlinarith [abs_nonneg (v / s), hb.2]
      _ ≤ _ := hdabs
  have hEB := Real.exp_le_exp.mpr hbδ
  have hprod := mul_le_mul hEP hEB (Real.exp_pos _).le (Real.exp_pos _).le
  have htriple := mul_le_mul hprod hr hr0 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hnonneg : 0 ≤ deBruijnG1ScaledKernel u b v := by
    unfold deBruijnG1ScaledKernel
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (deBruijnSaddle_pos hu).le) hx.le
  rw [abs_of_nonneg hnonneg]
  calc
    _ = (Real.exp (-(deBruijnRealSaddlePhase u (deBruijnSaddle u + v / s) - deBruijnRealSaddlePhase u (deBruijnSaddle u))) *
        Real.exp (b * (v / s))) * (deBruijnSaddle u / (deBruijnSaddle u + v / s)) := by unfold deBruijnG1ScaledKernel; ring
    _ ≤ (Real.exp (-(deBruijnG1GaussianConstant * v ^ 2)) * Real.exp |v|) * 2 := htriple
    _ = 2 * Real.exp (|v| - deBruijnG1GaussianConstant * v ^ 2) := by
      rw [← Real.exp_add, show -(deBruijnG1GaussianConstant * v ^ 2) + |v| = |v| - deBruijnG1GaussianConstant * v ^ 2 by ring]
      ring
    _ ≤ 2 * Real.exp (2 / deBruijnG1GaussianConstant - (deBruijnG1GaussianConstant / 2) * v ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : Real) ≤ 2)
      apply Real.exp_le_exp.mpr
      linarith [deBruijnG1_abs_quadratic_bound v]
    _ = _ := by
      unfold deBruijnG1GaussianMajorant
      rw [show 2 / deBruijnG1GaussianConstant - deBruijnG1GaussianConstant / 2 * v ^ 2 =
        2 / deBruijnG1GaussianConstant + (-(deBruijnG1GaussianConstant / 2) * v ^ 2) by ring, Real.exp_add]
      ring

end

end Erdos1212Kernel
