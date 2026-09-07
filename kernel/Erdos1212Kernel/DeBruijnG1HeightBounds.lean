import Erdos1212Kernel.DeBruijnG1RealPhase

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnExpIntegral_eq_average_integral (x : Real) :
    deBruijn1951ExpIntegral x = ∫ t in (0 : Real)..x, deBruijnSaddleAverage t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ht => deBruijnExpIntegral_hasDerivAt_average t)
    (deBruijnSaddleAverage_continuous.intervalIntegrable 0 x)
  have h0 : deBruijn1951ExpIntegral 0 = 0 := by simp [deBruijn1951ExpIntegral]
  rw [h0, sub_zero] at h
  exact h.symm

theorem deBruijnSaddle_le_two_mul {u : Real} (hu : 1 < u) : deBruijnSaddle u ≤ 2 * u := by
  have h := deBruijnSaddleAverage_lower (deBruijnSaddle u)
  rw [deBruijnSaddle_average hu] at h
  linarith

theorem deBruijnSaddleAverage_half_factor {x : Real} (hx : 0 < x) :
    deBruijnSaddleAverage x = deBruijnSaddleAverage (x / 2) * (Real.exp (x / 2) + 1) / 2 := by
  rw [deBruijnSaddleAverage_eq_quot hx.ne', deBruijnSaddleAverage_eq_quot (half_pos hx).ne']
  have he : Real.exp x = Real.exp (x / 2) ^ 2 := by
    calc
      _ = Real.exp (x / 2 + x / 2) := by congr 1; ring
      _ = Real.exp (x / 2) * Real.exp (x / 2) := Real.exp_add _ _
      _ = _ := by ring
  rw [he]
  field_simp
  <;> ring

theorem deBruijnSaddleAverage_half_le {x : Real} (hx : 4 ≤ x) :
    deBruijnSaddleAverage (x / 2) ≤ deBruijnSaddleAverage x / 2 := by
  have he : 3 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have hp : 0 ≤ deBruijnSaddleAverage (x / 2) := by linarith [deBruijnSaddleAverage_lower (x / 2)]
  have hmul := mul_nonneg hp (sub_nonneg.mpr he)
  rw [deBruijnSaddleAverage_half_factor (by linarith : 0 < x)]
  nlinarith

theorem deBruijnExpIntegral_saddle_upper {u : Real} (hu : 1 < u) (hξ : 4 ≤ deBruijnSaddle u) :
    deBruijn1951ExpIntegral (deBruijnSaddle u) ≤ (3 / 4 : Real) * u * deBruijnSaddle u := by
  have hξ0 := (deBruijnSaddle_pos hu).le
  have hhalf := deBruijnSaddleAverage_half_le hξ
  rw [deBruijnSaddle_average hu] at hhalf
  have hi0 : IntervalIntegrable deBruijnSaddleAverage volume 0 (deBruijnSaddle u / 2) :=
    deBruijnSaddleAverage_continuous.intervalIntegrable 0 (deBruijnSaddle u / 2)
  have hi1 : IntervalIntegrable deBruijnSaddleAverage volume (deBruijnSaddle u / 2) (deBruijnSaddle u) :=
    deBruijnSaddleAverage_continuous.intervalIntegrable (deBruijnSaddle u / 2) (deBruijnSaddle u)
  have hlow := intervalIntegral.integral_mono_on (by positivity : (0 : Real) ≤ deBruijnSaddle u / 2)
    hi0 (_root_.intervalIntegrable_const (c := u / 2)) (by
      intro t ht
      exact (deBruijnSaddleAverage_strictMono.monotone ht.2).trans hhalf)
  have hhigh := intervalIntegral.integral_mono_on (by linarith : deBruijnSaddle u / 2 ≤ deBruijnSaddle u)
    hi1 (_root_.intervalIntegrable_const (c := u)) (by
      intro t ht
      have h := deBruijnSaddleAverage_strictMono.monotone ht.2
      rw [deBruijnSaddle_average hu] at h
      exact h)
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hlow hhigh
  rw [deBruijnExpIntegral_eq_average_integral, ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
  nlinarith

theorem deBruijnSaddleHeight_exponential_bound {u : Real} (hu : 1 < u) (hξ : 4 ≤ deBruijnSaddle u) :
    deBruijnSaddleHeight u ≤ Real.exp (-u * deBruijnSaddle u / 4) := by
  unfold deBruijnSaddleHeight
  apply Real.exp_le_exp.mpr
  linarith [deBruijnExpIntegral_saddle_upper hu hξ]

theorem eventually_deBruijnSaddleHeight_small :
    ∀ᶠ u : Real in atTop, deBruijnSaddleHeight u ≤ Real.exp (-4 * u) := by
  filter_upwards [eventually_gt_atTop (1 : Real), tendsto_deBruijnSaddle.eventually_ge_atTop 16] with u hu hξ
  apply (deBruijnSaddleHeight_exponential_bound hu (by linarith)).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hξ (show 0 ≤ u by linarith)
  nlinarith

theorem deBruijnSaddleCurvature_lower_half {u : Real} (hu : 1 < u) (hξ : 2 ≤ deBruijnSaddle u) :
    u / 2 ≤ deBruijnSaddleCurvature u := by
  have hd : (u - 1) / deBruijnSaddle u ≤ u / 2 := by
    rw [div_le_iff₀ (deBruijnSaddle_pos hu)]
    have h := mul_le_mul_of_nonneg_left hξ (show 0 ≤ u by linarith)
    nlinarith
  rw [deBruijnSaddleCurvature_formula hu]
  linarith

theorem deBruijnSaddle_sqrt_le_parameter {u : Real} (hu : 1 < u) :
    Real.sqrt (deBruijnSaddleCurvature u) ≤ u := by
  have hsq := Real.sq_sqrt (deBruijnSaddleCurvature_pos u).le
  have hC := deBruijnSaddleCurvature_le hu
  nlinarith [Real.sqrt_nonneg (deBruijnSaddleCurvature u)]

end

end Erdos1212Kernel
