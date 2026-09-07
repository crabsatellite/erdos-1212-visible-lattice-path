import Erdos1212Kernel.DeBruijnSaddleMoment

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnExpThirdRemainder (w : Complex) : Complex := Complex.exp w - 1 - w - w ^ 2 / 2

def deBruijnPhaseThirdRemainder (x : Real) (h : Complex) (t : Real) : Complex :=
  Complex.exp ((t : Complex) * (x : Complex)) * deBruijnExpThirdRemainder ((t : Complex) * h) / (t : Complex)

theorem deBruijnExpThirdRemainder_norm (w : Complex) :
    ‖deBruijnExpThirdRemainder w‖ ≤ ‖w‖ ^ 3 * Real.exp ‖w‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp w 3
  have he : Complex.exp w - (∑ k ∈ Finset.range 3, w ^ k / (k.factorial : Complex)) = deBruijnExpThirdRemainder w := by
    norm_num [Finset.sum_range_succ, deBruijnExpThirdRemainder] <;> ring
  rw [he] at h
  exact h

theorem deBruijnPhaseThirdRemainder_norm {x t : Real} (h : Complex) (ht : t ∈ Set.Icc (0 : Real) 1) :
    ‖deBruijnPhaseThirdRemainder x h t‖ ≤ (‖h‖ ^ 3 * Real.exp ‖h‖) * (t ^ 2 * Real.exp (t * x)) := by
  rcases ht.1.eq_or_lt with rfl | htPos
  · simp [deBruijnPhaseThirdRemainder, deBruijnExpThirdRemainder]
  · have htN : ‖(t : Complex)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htPos]
    have heN : ‖Complex.exp ((t : Complex) * (x : Complex))‖ = Real.exp (t * x) := by
      rw [← Complex.ofReal_mul, Complex.norm_exp, Complex.ofReal_re]
    have he : Real.exp (t * ‖h‖) ≤ Real.exp ‖h‖ := by
      apply Real.exp_le_exp.mpr
      nlinarith [norm_nonneg h, ht.2]
    have hR := deBruijnExpThirdRemainder_norm ((t : Complex) * h)
    rw [norm_mul, htN] at hR
    have hR' := hR.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (t * ‖h‖) ^ 3))
    have hm := mul_le_mul_of_nonneg_left hR' (Real.exp_pos (t * x)).le
    calc
      _ = Real.exp (t * x) * ‖deBruijnExpThirdRemainder ((t : Complex) * h)‖ / t := by
        rw [deBruijnPhaseThirdRemainder, norm_div, norm_mul, heN, htN]
      _ ≤ Real.exp (t * x) * ((t * ‖h‖) ^ 3 * Real.exp ‖h‖) / t := div_le_div_of_nonneg_right hm htPos.le
      _ = _ := by field_simp

theorem deBruijnPhaseThirdRemainder_point_identity (x : Real) (h : Complex) {t : Real} (ht : t ≠ 0) :
    deBruijnComplexPhaseIntegrand ((x : Complex) + h) t - deBruijnComplexPhaseIntegrand (x : Complex) t -
      h * Complex.exp ((t : Complex) * (x : Complex)) -
      (h ^ 2 / 2) * ((t : Complex) * Complex.exp ((t : Complex) * (x : Complex))) =
        deBruijnPhaseThirdRemainder x h t := by
  have htC : (t : Complex) ≠ 0 := by exact_mod_cast ht
  have he : Complex.exp ((t : Complex) * ((x : Complex) + h)) =
      Complex.exp ((t : Complex) * (x : Complex)) * Complex.exp ((t : Complex) * h) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold deBruijnComplexPhaseIntegrand deBruijnPhaseThirdRemainder deBruijnExpThirdRemainder
  rw [he]
  field_simp
  <;> ring

theorem deBruijnSaddle_second_moment_nonneg (x : Real) :
    0 ≤ ∫ t in (0 : Real)..1, t ^ 2 * Real.exp (t * x) := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : Real) ≤ 1)
  intro t _ht
  positivity

theorem deBruijnSaddle_second_moment_le (x : Real) :
    (∫ t in (0 : Real)..1, t ^ 2 * Real.exp (t * x)) ≤ deBruijnSaddleMoment x := by
  have hi : IntervalIntegrable (fun t : Real => t ^ 2 * Real.exp (t * x)) volume 0 1 :=
    ((continuous_id.pow 2).mul (Real.continuous_exp.comp (continuous_id.mul_const x))).intervalIntegrable 0 1
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : Real) ≤ 1) hi (deBruijnSaddleMoment_intervalIntegrable x)
  intro t ht
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  nlinarith [ht.1, ht.2]

theorem deBruijnPhaseThirdRemainder_integral_norm (x : Real) (h : Complex) :
    ‖∫ t in (0 : Real)..1, deBruijnPhaseThirdRemainder x h t‖ ≤
      (‖h‖ ^ 3 * Real.exp ‖h‖) * deBruijnSaddleMoment x := by
  have hb : IntervalIntegrable (fun t : Real => (‖h‖ ^ 3 * Real.exp ‖h‖) * (t ^ 2 * Real.exp (t * x))) volume 0 1 :=
    (((continuous_id.pow 2).mul (Real.continuous_exp.comp (continuous_id.mul_const x))).const_mul _).intervalIntegrable 0 1
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le (f := deBruijnPhaseThirdRemainder x h) (by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
    exact deBruijnPhaseThirdRemainder_norm h ⟨ht.1.le, ht.2⟩) hb
  rw [intervalIntegral.integral_const_mul] at hnorm
  have hk : 0 ≤ ‖h‖ ^ 3 * Real.exp ‖h‖ := by positivity
  rw [abs_of_nonneg (mul_nonneg hk (deBruijnSaddle_second_moment_nonneg x))] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left (deBruijnSaddle_second_moment_le x) hk)

end

end Erdos1212Kernel
