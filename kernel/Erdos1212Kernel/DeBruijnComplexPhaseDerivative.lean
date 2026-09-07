import Erdos1212Kernel.DeBruijnComplexPhaseBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnComplexPhaseIntegrand_hasDerivAt (z : Complex) {t : Real} (ht : t ≠ 0) :
    HasDerivAt (fun w : Complex => deBruijnComplexPhaseIntegrand w t) (Complex.exp ((t : Complex) * z)) z := by
  have htC : (t : Complex) ≠ 0 := by exact_mod_cast ht
  have h := (((hasDerivAt_id z).const_mul (t : Complex)).cexp.sub_const 1).div_const (t : Complex)
  simpa only [deBruijnComplexPhaseIntegrand, mul_one, mul_div_cancel_right₀ _ htC] using h

theorem deBruijnComplexExpIntegral_hasDerivAt (z : Complex) :
    HasDerivAt deBruijnComplexExpIntegral (deBruijnComplexExpAverage z) z := by
  let s := Metric.ball z 1
  let bound := fun _t : Real => Real.exp (‖z‖ + 1)
  let F' := fun w : Complex => fun t : Real => Complex.exp ((t : Complex) * w)
  have hs : s ∈ nhds z := Metric.ball_mem_nhds z (by norm_num)
  have hmeas : ∀ᶠ w in nhds z,
      AEStronglyMeasurable (deBruijnComplexPhaseIntegrand w) (volume.restrict (Set.Ioc (0 : Real) 1)) := by
    filter_upwards with w
    exact (deBruijnComplexPhaseIntegrand_measurable w).aestronglyMeasurable
  have hi : IntegrableOn (deBruijnComplexPhaseIntegrand z) (Set.Ioc (0 : Real) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp (deBruijnComplexPhaseIntegrand_intervalIntegrable z)
  have hF'cont : Continuous (F' z) := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const z)
  have hbi : IntegrableOn bound (Set.Ioc (0 : Real) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp _root_.intervalIntegrable_const
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) 1)), ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w hw
    have hw' : ‖w - z‖ < 1 := by simpa only [s, Metric.mem_ball, dist_eq_norm] using hw
    have hwNorm : ‖w‖ ≤ ‖z‖ + 1 := by
      have htri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith
    have htnorm : ‖(t : Complex)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    have hmul : ‖(t : Complex) * w‖ ≤ ‖z‖ + 1 := by
      rw [norm_mul, htnorm]
      have htw : t * ‖w‖ ≤ ‖w‖ := by nlinarith [norm_nonneg w, ht.2]
      exact htw.trans hwNorm
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hmul)
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) 1)), ∀ w ∈ s,
      HasDerivAt (fun v : Complex => deBruijnComplexPhaseIntegrand v t) (F' w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w _hw
    exact deBruijnComplexPhaseIntegrand_hasDerivAt w ht.1.ne'
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : Real) 1)) (F := deBruijnComplexPhaseIntegrand) (F' := F')
    (bound := bound) hs hmeas hi hF'cont.aestronglyMeasurable hbound hbi hdiff).2
  have hd : HasDerivAt (fun w : Complex => ∫ t in (0 : Real)..1, deBruijnComplexPhaseIntegrand w t)
      (deBruijnComplexExpAverage z) z := by
    simpa only [deBruijnComplexExpAverage, intervalIntegral.integral_of_le (show (0 : Real) ≤ 1 by norm_num), F'] using h
  apply hd.congr_of_eventuallyEq
  filter_upwards with w
  exact deBruijnComplexExpIntegral_eq_parametric w

theorem deBruijnComplexExpIntegral_differentiable : Differentiable Complex deBruijnComplexExpIntegral :=
  fun z => (deBruijnComplexExpIntegral_hasDerivAt z).differentiableAt

theorem deBruijnComplexExpIntegral_continuous : Continuous deBruijnComplexExpIntegral :=
  deBruijnComplexExpIntegral_differentiable.continuous

theorem deBruijnComplexExpAverage_mul (z : Complex) :
    z * deBruijnComplexExpAverage z = Complex.exp z - 1 := by
  have hc : Continuous (fun t : Real => Complex.exp ((t : Complex) * z)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const z)
  have hd (t : Real) : HasDerivAt (fun s : Real => Complex.exp ((s : Complex) * z))
      (z * Complex.exp ((t : Complex) * z)) t := by
    have hi : HasDerivAt (fun s : Real => (s : Complex) * z) z t := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    exact hi.cexp.congr_deriv (by ring)
  have hi : IntervalIntegrable (fun t : Real => z * Complex.exp ((t : Complex) * z)) volume 0 1 :=
    (hc.const_mul z).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ht => hd t) hi
  simpa only [intervalIntegral.integral_const_mul, deBruijnComplexExpAverage, Complex.ofReal_zero,
    Complex.ofReal_one, zero_mul, one_mul, Complex.exp_zero] using h

theorem deBruijnComplexExpAverage_eq_quot {z : Complex} (hz : z ≠ 0) :
    deBruijnComplexExpAverage z = (Complex.exp z - 1) / z := by
  apply (eq_div_iff hz).mpr
  simpa only [mul_comm] using deBruijnComplexExpAverage_mul z

theorem deBruijnComplexExpIntegral_hasDerivAt_quot {z : Complex} (hz : z ≠ 0) :
    HasDerivAt deBruijnComplexExpIntegral ((Complex.exp z - 1) / z) z := by
  rw [← deBruijnComplexExpAverage_eq_quot hz]
  exact deBruijnComplexExpIntegral_hasDerivAt z

end

end Erdos1212Kernel
