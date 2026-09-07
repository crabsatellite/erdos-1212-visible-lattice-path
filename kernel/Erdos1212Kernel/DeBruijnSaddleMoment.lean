import Erdos1212Kernel.DeBruijnSaddleAverage

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnComplexSaddleMoment (z : Complex) : Complex :=
  ∫ t in (0 : Real)..1, (t : Complex) * Complex.exp ((t : Complex) * z)

def deBruijnSaddleMoment (x : Real) : Real := ∫ t in (0 : Real)..1, t * Real.exp (t * x)

theorem deBruijnComplexExpAverage_hasDerivAt (z : Complex) :
    HasDerivAt deBruijnComplexExpAverage (deBruijnComplexSaddleMoment z) z := by
  let F := fun w : Complex => fun t : Real => Complex.exp ((t : Complex) * w)
  let F' := fun w : Complex => fun t : Real => (t : Complex) * Complex.exp ((t : Complex) * w)
  have hc (w : Complex) : Continuous (F w) := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const w)
  have hmeas : ∀ᶠ w in nhds z, AEStronglyMeasurable (F w) (volume.restrict (Set.Ioc (0 : Real) 1)) := by
    filter_upwards with w
    exact (hc w).aestronglyMeasurable
  have hi : IntegrableOn (F z) (Set.Ioc (0 : Real) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp ((hc z).intervalIntegrable 0 1)
  have hF'c : Continuous (F' z) := Complex.continuous_ofReal.mul (hc z)
  have hbi : IntegrableOn (fun _t : Real => Real.exp (‖z‖ + 1)) (Set.Ioc (0 : Real) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp _root_.intervalIntegrable_const
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) 1)), ∀ w ∈ Metric.ball z 1,
      ‖F' w t‖ ≤ Real.exp (‖z‖ + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w hw
    have hwN := deBruijn_complex_norm_of_mem_ball_one hw
    have htN : ‖(t : Complex)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    have htw : ‖(t : Complex) * w‖ ≤ ‖z‖ + 1 := by
      rw [norm_mul, htN]
      have h := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)
      simp only [one_mul] at h
      exact h.trans hwN
    have he := (Complex.norm_exp_le_exp_norm ((t : Complex) * w)).trans (Real.exp_le_exp.mpr htw)
    change ‖(t : Complex) * Complex.exp ((t : Complex) * w)‖ ≤ _
    rw [norm_mul, htN]
    exact (mul_le_mul_of_nonneg_left he ht.1.le).trans (by nlinarith [Real.exp_pos (‖z‖ + 1), ht.2])
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) 1)), ∀ w ∈ Metric.ball z 1,
      HasDerivAt (fun v : Complex => F v t) (F' w t) w := by
    filter_upwards with t
    intro w _hw
    have h := ((hasDerivAt_id w).const_mul (t : Complex)).cexp
    apply h.congr_deriv
    dsimp [F']
    ring
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : Real) 1)) (F := F) (F' := F')
    (bound := fun _t : Real => Real.exp (‖z‖ + 1)) (Metric.ball_mem_nhds z (by norm_num))
    hmeas hi hF'c.aestronglyMeasurable hbound hbi hdiff).2
  change HasDerivAt (fun w : Complex => ∫ t in (0 : Real)..1, Complex.exp ((t : Complex) * w)) _ z
  simpa only [deBruijnComplexSaddleMoment, intervalIntegral.integral_of_le (show (0 : Real) ≤ 1 by norm_num), F, F'] using h

theorem deBruijnSaddleMoment_ofReal (x : Real) :
    (deBruijnSaddleMoment x : Complex) = deBruijnComplexSaddleMoment (x : Complex) := by
  unfold deBruijnSaddleMoment deBruijnComplexSaddleMoment
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]

theorem deBruijnSaddleAverage_hasDerivAt (x : Real) :
    HasDerivAt deBruijnSaddleAverage (deBruijnSaddleMoment x) x := by
  have h := (deBruijnComplexExpAverage_hasDerivAt (x : Complex)).real_of_complex
  simpa only [← deBruijnSaddleAverage_ofReal, ← deBruijnSaddleMoment_ofReal, Complex.ofReal_re] using h

theorem deBruijnSaddleMoment_intervalIntegrable (x : Real) :
    IntervalIntegrable (fun t : Real => t * Real.exp (t * x)) volume 0 1 :=
  (continuous_id.mul (Real.continuous_exp.comp (continuous_id.mul_const x))).intervalIntegrable 0 1

theorem deBruijnSaddleMoment_pos (x : Real) : 0 < deBruijnSaddleMoment x := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (deBruijnSaddleMoment_intervalIntegrable x)
    (fun t ht => mul_pos ht.1 (Real.exp_pos _)) (by norm_num)

theorem deBruijnSaddleMoment_le_average (x : Real) : deBruijnSaddleMoment x ≤ deBruijnSaddleAverage x := by
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : Real) ≤ 1)
    (deBruijnSaddleMoment_intervalIntegrable x) (deBruijnSaddleAverage_integrand_intervalIntegrable x 0 1)
  intro t ht
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (Real.exp_pos (t * x)).le

theorem deBruijnSaddleMoment_eq_quot {x : Real} (hx : x ≠ 0) :
    deBruijnSaddleMoment x = ((x - 1) * Real.exp x + 1) / x ^ 2 := by
  have h := ((Real.hasDerivAt_exp x).sub_const 1).div (hasDerivAt_id x) hx
  have hq : HasDerivAt (fun y : Real => (Real.exp y - 1) / y) (((x - 1) * Real.exp x + 1) / x ^ 2) x := by
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  have hA : HasDerivAt deBruijnSaddleAverage (((x - 1) * Real.exp x + 1) / x ^ 2) x := by
    apply hq.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact deBruijnSaddleAverage_eq_quot hy
  exact (deBruijnSaddleAverage_hasDerivAt x).unique hA

end

end Erdos1212Kernel
