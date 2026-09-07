import Erdos1212Kernel.DeBruijnG1Normalization
import Erdos1212Kernel.DeBruijnG1Concentration

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijn_left_exponential_integral {m : Real} (hm : 0 < m) (a : Real) :
    (∫ x in (1 : Real)..a, Real.exp (-m * (a - x))) = (1 - Real.exp (-m * (a - 1))) / m := by
  have hd (x : Real) : HasDerivAt (fun t : Real => Real.exp (-m * (a - t)) / m)
      (Real.exp (-m * (a - x))) x := by
    have h := ((((hasDerivAt_const x a).sub (hasDerivAt_id x)).const_mul (-m)).exp).div_const m
    apply h.congr_deriv
    simp only [zero_sub, mul_neg_one, neg_neg]
    field_simp
    rfl
  have hi : IntervalIntegrable (fun x : Real => Real.exp (-m * (a - x))) volume 1 a :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable 1 a
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _hx => hd x) hi
  simpa only [sub_self, mul_zero, Real.exp_zero, sub_div] using h

theorem deBruijn_left_exponential_integral_le {m : Real} (hm : 0 < m) (a : Real) :
    (∫ x in (1 : Real)..a, Real.exp (-m * (a - x))) ≤ 1 / m := by
  rw [deBruijn_left_exponential_integral hm]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-m * (a - 1))]) hm.le

theorem deBruijnG1_normalized_left_density_bound {u b x : Real} (hu : 1 < u)
    (hb : 0 ≤ b) (hx1 : 1 ≤ x) (hx : x ≤ deBruijnSaddle u - 1) :
    deBruijnG1Normalizer u b * deBruijnG1LaplaceDensity u b x ≤
      (Real.sqrt (deBruijnSaddleCurvature u) * deBruijnSaddle u * Real.exp (-deBruijnG1CurvatureFloor u / 2)) *
        Real.exp (-deBruijnG1CurvatureFloor u * (deBruijnSaddle u - 1 - x)) := by
  have hξ := deBruijnSaddle_pos hu
  have hx0 : 0 < x := by linarith
  have hs := Real.sqrt_nonneg (deBruijnSaddleCurvature u)
  have hP := deBruijnRealSaddlePhase_left_linear_lower hu hx
  have hE : Real.exp (-(deBruijnRealSaddlePhase u x - deBruijnRealSaddlePhase u (deBruijnSaddle u))) ≤
      Real.exp (-deBruijnG1CurvatureFloor u / 2) * Real.exp (-deBruijnG1CurvatureFloor u * (deBruijnSaddle u - 1 - x)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hbE : Real.exp (b * (x - deBruijnSaddle u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hb (by linarith))
  have hr : deBruijnSaddle u / x ≤ deBruijnSaddle u := by
    rw [div_le_iff₀ hx0]
    nlinarith
  have hprod := mul_le_mul hE hbE (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hall := mul_le_mul hprod hr (div_nonneg hξ.le hx0.le) (by positivity)
  calc
    _ = Real.sqrt (deBruijnSaddleCurvature u) *
        ((deBruijnSaddleHeight u * deBruijnSaddle u * Real.exp (-b * deBruijnSaddle u)) * deBruijnG1LaplaceDensity u b x) := by
      unfold deBruijnG1Normalizer
      ring
    _ = Real.sqrt (deBruijnSaddleCurvature u) *
        ((Real.exp (-(deBruijnRealSaddlePhase u x - deBruijnRealSaddlePhase u (deBruijnSaddle u))) *
          Real.exp (b * (x - deBruijnSaddle u))) * (deBruijnSaddle u / x)) := by
      rw [deBruijnG1LaplaceDensity_normalized]
      ring
    _ ≤ Real.sqrt (deBruijnSaddleCurvature u) *
        (((Real.exp (-deBruijnG1CurvatureFloor u / 2) * Real.exp (-deBruijnG1CurvatureFloor u * (deBruijnSaddle u - 1 - x))) * 1) *
          deBruijnSaddle u) := mul_le_mul_of_nonneg_left hall hs
    _ = _ := by ring

def deBruijnG1LeftTail (u b : Real) : Real :=
  ∫ x in (1 : Real)..(deBruijnSaddle u - 1), deBruijnG1LaplaceDensity u b x

theorem deBruijnG1LeftTail_integrable {u : Real} (hξ : 2 ≤ deBruijnSaddle u) (b : Real) :
    IntervalIntegrable (deBruijnG1LaplaceDensity u b) volume 1 (deBruijnSaddle u - 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : 1 ≤ deBruijnSaddle u - 1)).mpr
  exact (deBruijnG1LaplaceDensity_integrable u b (by norm_num : (0 : Real) < 1)).mono_set Set.Ioc_subset_Ioi_self

theorem deBruijnG1LeftTail_nonneg {u : Real} (hξ : 2 ≤ deBruijnSaddle u) (b : Real) :
    0 ≤ deBruijnG1LeftTail u b := by
  apply intervalIntegral.integral_nonneg (by linarith : 1 ≤ deBruijnSaddle u - 1)
  intro x hx
  exact (deBruijnG1LaplaceDensity_pos u b (by linarith [hx.1] : 0 < x)).le

theorem deBruijnG1_normalized_left_bound {u b : Real} (hu : 1 < u) (hξ : 2 ≤ deBruijnSaddle u) (hb : 0 ≤ b) :
    |deBruijnG1Normalizer u b * deBruijnG1LeftTail u b| ≤
      (Real.sqrt (deBruijnSaddleCurvature u) * deBruijnSaddle u * Real.exp (-deBruijnG1CurvatureFloor u / 2)) /
        deBruijnG1CurvatureFloor u := by
  let K := Real.sqrt (deBruijnSaddleCurvature u) * deBruijnSaddle u * Real.exp (-deBruijnG1CurvatureFloor u / 2)
  have hK : 0 ≤ K := by have h := deBruijnSaddle_pos hu; dsimp [K]; positivity
  have hi := deBruijnG1LeftTail_integrable hξ b
  have he : IntervalIntegrable (fun x : Real => Real.exp (-deBruijnG1CurvatureFloor u * (deBruijnSaddle u - 1 - x)))
      volume 1 (deBruijnSaddle u - 1) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : 1 ≤ deBruijnSaddle u - 1)
    (hi.const_mul (deBruijnG1Normalizer u b)) (he.const_mul K) (by
      intro x hx
      exact deBruijnG1_normalized_left_density_bound hu hb hx.1 hx.2)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  rw [abs_of_nonneg (mul_nonneg (deBruijnG1Normalizer_pos hu b).le (deBruijnG1LeftTail_nonneg hξ b))]
  calc
    _ ≤ K * ∫ x in (1 : Real)..(deBruijnSaddle u - 1), Real.exp (-deBruijnG1CurvatureFloor u * (deBruijnSaddle u - 1 - x)) := hmono
    _ ≤ K * (1 / deBruijnG1CurvatureFloor u) :=
      mul_le_mul_of_nonneg_left (deBruijn_left_exponential_integral_le (deBruijnG1CurvatureFloor_pos u) _) hK
    _ = _ := by dsimp [K]; ring

end

end Erdos1212Kernel
