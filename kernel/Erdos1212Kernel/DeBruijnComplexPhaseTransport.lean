import Erdos1212Kernel.DeBruijnComplexPhaseBounds
import Erdos1212Kernel.DeBruijn1951RealDefinitions

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijnComplexPhaseIntegrand_conj (z : Complex) (t : Real) :
    deBruijnComplexPhaseIntegrand (starRingEnd Complex z) t =
      starRingEnd Complex (deBruijnComplexPhaseIntegrand z t) := by
  unfold deBruijnComplexPhaseIntegrand
  simp only [map_div₀, map_sub, map_one, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

theorem deBruijnComplexExpIntegral_conj (z : Complex) :
    deBruijnComplexExpIntegral (starRingEnd Complex z) = starRingEnd Complex (deBruijnComplexExpIntegral z) := by
  rw [deBruijnComplexExpIntegral_eq_parametric, deBruijnComplexExpIntegral_eq_parametric]
  calc
    _ = ∫ t in (0 : Real)..1, starRingEnd Complex (deBruijnComplexPhaseIntegrand z t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact deBruijnComplexPhaseIntegrand_conj z t
    _ = _ := by
      simpa only [Complex.conjCLE_apply] using
        Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm (deBruijnComplexPhaseIntegrand_intervalIntegrable z)

/-- Restriction of the exact segment primitive to the real axis. The
linear change of variables includes its differential and works for
negative x and the degenerate x=0 as well. -/
theorem deBruijnComplexExpIntegral_ofReal (x : Real) :
    deBruijnComplexExpIntegral (x : Complex) = (deBruijn1951ExpIntegral x : Complex) := by
  unfold deBruijnComplexExpIntegral
  have hpoint (t : Real) :
      (x : Complex) * ((Complex.exp ((t : Complex) * (x : Complex)) - 1) / ((t : Complex) * (x : Complex))) =
        ((x * ((Real.exp (t * x) - 1) / (t * x)) : Real) : Complex) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]
  calc
    _ = ∫ t in (0 : Real)..1, ((x * ((Real.exp (t * x) - 1) / (t * x)) : Real) : Complex) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact hpoint t
    _ = ((∫ t in (0 : Real)..1, x * ((Real.exp (t * x) - 1) / (t * x)) : Real) : Complex) := intervalIntegral.integral_ofReal
    _ = (deBruijn1951ExpIntegral x : Complex) := by
      congr 1
      rw [intervalIntegral.integral_const_mul]
      have h := intervalIntegral.smul_integral_comp_mul_right
        (a := (0 : Real)) (b := 1) (f := fun s : Real => (Real.exp s - 1) / s) x
      simpa only [smul_eq_mul, zero_mul, one_mul, deBruijn1951ExpIntegral] using h

end

end Erdos1212Kernel
