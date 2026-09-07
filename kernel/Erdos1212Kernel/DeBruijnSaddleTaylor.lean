import Erdos1212Kernel.DeBruijnSaddleRemainderBounds
import Erdos1212Kernel.DeBruijnSaddleGeometry

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

def deBruijnComplexTaylorDifference (x : Real) (h : Complex) (t : Real) : Complex :=
  deBruijnComplexPhaseIntegrand ((x : Complex) + h) t - deBruijnComplexPhaseIntegrand (x : Complex) t -
    h * Complex.exp ((t : Complex) * (x : Complex)) -
    (h ^ 2 / 2) * ((t : Complex) * Complex.exp ((t : Complex) * (x : Complex)))

theorem deBruijnComplexTaylorDifference_intervalIntegrable (x : Real) (h : Complex) :
    IntervalIntegrable (deBruijnComplexTaylorDifference x h) volume 0 1 := by
  have hc : Continuous (fun t : Real => Complex.exp ((t : Complex) * (x : Complex))) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const (x : Complex))
  have hiExp : IntervalIntegrable (fun t : Real => Complex.exp ((t : Complex) * (x : Complex))) volume 0 1 := hc.intervalIntegrable 0 1
  have hiMom : IntervalIntegrable (fun t : Real => (t : Complex) * Complex.exp ((t : Complex) * (x : Complex))) volume 0 1 :=
    (Complex.continuous_ofReal.mul hc).intervalIntegrable 0 1
  exact (((deBruijnComplexPhaseIntegrand_intervalIntegrable ((x : Complex) + h)).sub
    (deBruijnComplexPhaseIntegrand_intervalIntegrable (x : Complex))).sub (hiExp.const_mul h)).sub (hiMom.const_mul (h ^ 2 / 2))

theorem deBruijnPhaseThirdRemainder_intervalIntegrable (x : Real) (h : Complex) :
    IntervalIntegrable (deBruijnPhaseThirdRemainder x h) volume 0 1 := by
  have hi := (deBruijnComplexTaylorDifference_intervalIntegrable x h).1
  have hR : IntegrableOn (deBruijnPhaseThirdRemainder x h) (Set.Ioc (0 : Real) 1) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact deBruijnPhaseThirdRemainder_point_identity x h ht.1.ne'
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : Real) ≤ 1)).mpr hR

theorem deBruijnComplexExpIntegral_taylor_integral (x : Real) (h : Complex) :
    deBruijnComplexExpIntegral ((x : Complex) + h) - deBruijnComplexExpIntegral (x : Complex) -
      h * deBruijnComplexExpAverage (x : Complex) - (h ^ 2 / 2) * deBruijnComplexSaddleMoment (x : Complex) =
        ∫ t in (0 : Real)..1, deBruijnPhaseThirdRemainder x h t := by
  have hc : Continuous (fun t : Real => Complex.exp ((t : Complex) * (x : Complex))) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const (x : Complex))
  have hiE : IntervalIntegrable (fun t : Real => Complex.exp ((t : Complex) * (x : Complex))) volume 0 1 :=
    hc.intervalIntegrable 0 1
  have hiM : IntervalIntegrable (fun t : Real => (t : Complex) * Complex.exp ((t : Complex) * (x : Complex))) volume 0 1 :=
    (Complex.continuous_ofReal.mul hc).intervalIntegrable 0 1
  have hi1 := deBruijnComplexPhaseIntegrand_intervalIntegrable ((x : Complex) + h)
  have hi0 := deBruijnComplexPhaseIntegrand_intervalIntegrable (x : Complex)
  have hp1 : IntervalIntegrable (fun t : Real => deBruijnComplexPhaseIntegrand ((x : Complex) + h) t -
      deBruijnComplexPhaseIntegrand (x : Complex) t) volume 0 1 := hi1.sub hi0
  have hp2 : IntervalIntegrable (fun t : Real => deBruijnComplexPhaseIntegrand ((x : Complex) + h) t -
      deBruijnComplexPhaseIntegrand (x : Complex) t - h * Complex.exp ((t : Complex) * (x : Complex))) volume 0 1 := hp1.sub (hiE.const_mul h)
  calc
    _ = ∫ t in (0 : Real)..1, deBruijnComplexTaylorDifference x h t := by
      unfold deBruijnComplexTaylorDifference
      rw [intervalIntegral.integral_sub hp2 (hiM.const_mul (h ^ 2 / 2)),
        intervalIntegral.integral_sub hp1 (hiE.const_mul h), intervalIntegral.integral_sub hi1 hi0,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        ← deBruijnComplexExpIntegral_eq_parametric, ← deBruijnComplexExpIntegral_eq_parametric]
      rfl
    _ = _ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
      exact deBruijnPhaseThirdRemainder_point_identity x h ht.1.ne'

theorem deBruijnComplexExpIntegral_taylor_bound (x : Real) (h : Complex) :
    ‖deBruijnComplexExpIntegral ((x : Complex) + h) - deBruijnComplexExpIntegral (x : Complex) -
      h * deBruijnComplexExpAverage (x : Complex) - (h ^ 2 / 2) * deBruijnComplexSaddleMoment (x : Complex)‖ ≤
      (‖h‖ ^ 3 * Real.exp ‖h‖) * deBruijnSaddleMoment x := by
  rw [deBruijnComplexExpIntegral_taylor_integral]
  exact deBruijnPhaseThirdRemainder_integral_norm x h

/-- The Taylor bound is for the original psi at its actual saddle;
its linear term vanishes by the proved saddle equation. -/
theorem deBruijnSaddlePhase_taylor_bound {u : Real} (hu : 1 < u) (h : Complex) :
    ‖deBruijnSaddlePhase u ((deBruijnSaddle u : Complex) + h) - deBruijnSaddlePhase u (deBruijnSaddle u : Complex) -
      (h ^ 2 / 2) * (deBruijnSaddleCurvature u : Complex)‖ ≤
      (‖h‖ ^ 3 * Real.exp ‖h‖) * deBruijnSaddleCurvature u := by
  have hA : deBruijnComplexExpAverage (deBruijnSaddle u : Complex) = (u : Complex) := by
    rw [← deBruijnSaddleAverage_ofReal, deBruijnSaddle_average hu]
  have hM : deBruijnComplexSaddleMoment (deBruijnSaddle u : Complex) = (deBruijnSaddleCurvature u : Complex) := by
    rw [← deBruijnSaddleMoment_ofReal]
    rfl
  have ht := deBruijnComplexExpIntegral_taylor_bound (deBruijnSaddle u) h
  rw [hA, hM] at ht
  have he : deBruijnSaddlePhase u ((deBruijnSaddle u : Complex) + h) - deBruijnSaddlePhase u (deBruijnSaddle u : Complex) -
      (h ^ 2 / 2) * (deBruijnSaddleCurvature u : Complex) =
      deBruijnComplexExpIntegral ((deBruijnSaddle u : Complex) + h) - deBruijnComplexExpIntegral (deBruijnSaddle u : Complex) -
        h * (u : Complex) - (h ^ 2 / 2) * (deBruijnSaddleCurvature u : Complex) := by
    unfold deBruijnSaddlePhase
    ring
  rw [he]
  exact ht

end

end Erdos1212Kernel
