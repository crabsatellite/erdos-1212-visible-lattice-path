import Erdos1212Kernel.DeBruijnComplexPhaseDefinitions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijnComplexExpIntegral_eq_parametric (z : Complex) :
    deBruijnComplexExpIntegral z = ∫ t in (0 : Real)..1, deBruijnComplexPhaseIntegrand z t := by
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [deBruijnComplexPhaseIntegrand]
  by_cases hz : z = 0
  · simp [hz]
  · by_cases ht : (t : Complex) = 0
    · simp [ht]
    · field_simp

theorem deBruijnComplexPhaseIntegrand_measurable (z : Complex) : Measurable (deBruijnComplexPhaseIntegrand z) :=
  ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const z)).measurable.sub_const 1).div
    Complex.continuous_ofReal.measurable

theorem deBruijn_complex_exp_sub_one_norm (z : Complex) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp z 1

theorem deBruijnComplexPhaseIntegrand_norm {z : Complex} {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    ‖deBruijnComplexPhaseIntegrand z t‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  rcases ht.1.eq_or_lt with rfl | htPos
  · simp only [deBruijnComplexPhaseIntegrand, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      sub_self, zero_div, norm_zero]
    exact mul_nonneg (norm_nonneg z) (Real.exp_pos _).le
  · have hnorm : ‖(t : Complex)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htPos]
    have hExp := deBruijn_complex_exp_sub_one_norm ((t : Complex) * z)
    rw [norm_mul, hnorm] at hExp
    have hscale : t * ‖z‖ ≤ ‖z‖ := by nlinarith [norm_nonneg z, ht.2]
    calc
      _ = ‖Complex.exp ((t : Complex) * z) - 1‖ / t := by
        rw [deBruijnComplexPhaseIntegrand, norm_div, hnorm]
      _ ≤ (t * ‖z‖ * Real.exp (t * ‖z‖)) / t := div_le_div_of_nonneg_right hExp htPos.le
      _ = ‖z‖ * Real.exp (t * ‖z‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscale) (norm_nonneg z)

theorem deBruijnComplexPhaseIntegrand_intervalIntegrable (z : Complex) :
    IntervalIntegrable (deBruijnComplexPhaseIntegrand z) volume 0 1 := by
  have hi : IntervalIntegrable (fun _t : Real => ‖z‖ * Real.exp ‖z‖) volume 0 1 := _root_.intervalIntegrable_const
  apply hi.mono_fun' (deBruijnComplexPhaseIntegrand_measurable z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
  exact deBruijnComplexPhaseIntegrand_norm ⟨ht.1.le, ht.2⟩

theorem deBruijnComplexExpIntegral_norm (z : Complex) :
    ‖deBruijnComplexExpIntegral z‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  rw [deBruijnComplexExpIntegral_eq_parametric]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : Real)) (b := 1)
    (f := deBruijnComplexPhaseIntegrand z) (C := ‖z‖ * Real.exp ‖z‖) (by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
      exact deBruijnComplexPhaseIntegrand_norm ⟨ht.1.le, ht.2⟩)
  simpa only [sub_zero, abs_one, mul_one] using h

theorem deBruijnComplexExpIntegral_zero : deBruijnComplexExpIntegral 0 = 0 := by
  simp [deBruijnComplexExpIntegral]

end

end Erdos1212Kernel
