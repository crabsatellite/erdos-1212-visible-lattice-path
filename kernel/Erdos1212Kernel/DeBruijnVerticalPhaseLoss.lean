import Erdos1212Kernel.DeBruijnSaddleGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnVerticalLossDensity (x y t : Real) : Real := Real.exp (t * x) * (Real.cos (t * y) - 1) / t

theorem deBruijnVerticalLossDensity_eq_re (x y t : Real) :
    (deBruijnComplexPhaseIntegrand ((x : Complex) + (y : Complex) * Complex.I) t -
      deBruijnComplexPhaseIntegrand (x : Complex) t).re = deBruijnVerticalLossDensity x y t := by
  unfold deBruijnComplexPhaseIntegrand deBruijnVerticalLossDensity
  simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.exp_re, Complex.one_re,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    zero_add, mul_one, Real.cos_zero]
  ring

theorem deBruijnVerticalLossDensity_intervalIntegrable (x y : Real) :
    IntervalIntegrable (deBruijnVerticalLossDensity x y) volume 0 1 := by
  have hi := (deBruijnComplexPhaseIntegrand_intervalIntegrable ((x : Complex) + (y : Complex) * Complex.I)).sub
    (deBruijnComplexPhaseIntegrand_intervalIntegrable (x : Complex))
  have hr : IntervalIntegrable (fun t : Real =>
      (deBruijnComplexPhaseIntegrand ((x : Complex) + (y : Complex) * Complex.I) t -
        deBruijnComplexPhaseIntegrand (x : Complex) t).re) volume 0 1 :=
    ⟨Complex.reCLM.integrable_comp hi.1, Complex.reCLM.integrable_comp hi.2⟩
  apply hr.congr
  intro t _ht
  exact deBruijnVerticalLossDensity_eq_re x y t

theorem deBruijnSaddlePhase_vertical_loss (u x y : Real) :
    (deBruijnSaddlePhase u ((x : Complex) + (y : Complex) * Complex.I) -
      deBruijnSaddlePhase u (x : Complex)).re = ∫ t in (0 : Real)..1, deBruijnVerticalLossDensity x y t := by
  have h1 := deBruijnComplexPhaseIntegrand_intervalIntegrable ((x : Complex) + (y : Complex) * Complex.I)
  have h0 := deBruijnComplexPhaseIntegrand_intervalIntegrable (x : Complex)
  have hi : IntervalIntegrable (fun t : Real =>
      deBruijnComplexPhaseIntegrand ((x : Complex) + (y : Complex) * Complex.I) t -
        deBruijnComplexPhaseIntegrand (x : Complex) t) volume 0 1 := h1.sub h0
  have hp : (deBruijnSaddlePhase u ((x : Complex) + (y : Complex) * Complex.I) - deBruijnSaddlePhase u (x : Complex)).re =
      (deBruijnComplexExpIntegral ((x : Complex) + (y : Complex) * Complex.I) - deBruijnComplexExpIntegral (x : Complex)).re := by
    unfold deBruijnSaddlePhase
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      neg_zero, sub_zero, add_zero]
    ring
  rw [hp, deBruijnComplexExpIntegral_eq_parametric, deBruijnComplexExpIntegral_eq_parametric,
    ← intervalIntegral.integral_sub h1 h0]
  have hr : (∫ t in (0 : Real)..1,
      deBruijnComplexPhaseIntegrand ((x : Complex) + (y : Complex) * Complex.I) t -
        deBruijnComplexPhaseIntegrand (x : Complex) t).re =
      ∫ t in (0 : Real)..1, (deBruijnComplexPhaseIntegrand ((x : Complex) + (y : Complex) * Complex.I) t -
        deBruijnComplexPhaseIntegrand (x : Complex) t).re := by
    simpa only [Complex.reCLM_apply] using (Complex.reCLM.intervalIntegral_comp_comm hi).symm
  rw [hr]
  apply intervalIntegral.integral_congr
  intro t _ht
  exact deBruijnVerticalLossDensity_eq_re x y t

theorem deBruijnVerticalLossDensity_upper (x : Real) {y t : Real} (hy : |y| ≤ Real.pi) (ht : t ∈ Set.Icc (0 : Real) 1) :
    deBruijnVerticalLossDensity x y t ≤ (-(2 / Real.pi ^ 2) * y ^ 2) * (t * Real.exp (t * x)) := by
  rcases ht.1.eq_or_lt with rfl | htPos
  · simp [deBruijnVerticalLossDensity]
  · have hty : |t * y| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos htPos]
      have h := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg y)
      simp only [one_mul] at h
      exact h.trans hy
    have hc := Real.cos_le_one_sub_mul_cos_sq hty
    have hc' : Real.cos (t * y) - 1 ≤ -(2 / Real.pi ^ 2) * (t * y) ^ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hc' (Real.exp_pos (t * x)).le
    unfold deBruijnVerticalLossDensity
    apply (div_le_iff₀ htPos).mpr
    calc
      _ ≤ Real.exp (t * x) * (-(2 / Real.pi ^ 2) * (t * y) ^ 2) := hm
      _ = _ := by ring

theorem deBruijnVerticalLoss_integral_upper (x : Real) {y : Real} (hy : |y| ≤ Real.pi) :
    (∫ t in (0 : Real)..1, deBruijnVerticalLossDensity x y t) ≤
      (-(2 / Real.pi ^ 2) * y ^ 2) * deBruijnSaddleMoment x := by
  have hb := (deBruijnSaddleMoment_intervalIntegrable x).const_mul (-(2 / Real.pi ^ 2) * y ^ 2)
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : Real) ≤ 1)
    (deBruijnVerticalLossDensity_intervalIntegrable x y) hb (fun t ht => deBruijnVerticalLossDensity_upper x hy ht)
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi

theorem deBruijnSaddlePhase_vertical_upper (u : Real) {y : Real} (hy : |y| ≤ Real.pi) :
    (deBruijnSaddlePhase u ((deBruijnSaddle u : Complex) + (y : Complex) * Complex.I) -
      deBruijnSaddlePhase u (deBruijnSaddle u : Complex)).re ≤
        (-(2 / Real.pi ^ 2) * y ^ 2) * deBruijnSaddleCurvature u := by
  rw [deBruijnSaddlePhase_vertical_loss]
  exact deBruijnVerticalLoss_integral_upper (deBruijnSaddle u) hy

theorem deBruijnF1_vertical_ratio_bound (u : Real) {y : Real} (hy : |y| ≤ Real.pi) :
    ‖deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) + (y : Complex) * Complex.I) /
      deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)‖ ≤
      Real.exp ((-(2 / Real.pi ^ 2) * y ^ 2) * deBruijnSaddleCurvature u) := by
  rw [deBruijnF1Integrand_eq_saddlePhase, deBruijnF1Integrand_eq_saddlePhase, ← Complex.exp_sub, Complex.norm_exp]
  exact Real.exp_le_exp.mpr (deBruijnSaddlePhase_vertical_upper u hy)

end

end Erdos1212Kernel
