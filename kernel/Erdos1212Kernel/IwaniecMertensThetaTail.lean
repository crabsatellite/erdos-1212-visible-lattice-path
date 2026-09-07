import Erdos1212Kernel.IwaniecMertensThetaBoundaryLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- The actual theta-error improper tail exists and has its fully
identified value. This does not assert absolute integrability or a rate. -/
theorem iwaniecMertensTheta_tail_limit {x : Real} (hx : 2 ≤ x) :
    Tendsto (fun y : Real => ∫ t in x..y, iwaniecMertensThetaErrorDensity t) atTop
      (nhds (iwaniecMertensThetaBoundary x - iwaniecMertensRealRemainder x)) := by
  have h := tendsto_iwaniecMertensThetaErrorDensity_primitive.sub_const
    (∫ t in (2 : Real)..x, iwaniecMertensThetaErrorDensity t)
  have he : (Erdos696.Mertens.meisselMertensConstant - iwaniecMertensThetaBase) -
      (∫ t in (2 : Real)..x, iwaniecMertensThetaErrorDensity t) =
      iwaniecMertensThetaBoundary x - iwaniecMertensRealRemainder x := by
    rw [iwaniecMertensRealRemainder_theta_finite hx]
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop x] with y hy
  exact intervalIntegral.integral_interval_sub_left
    (iwaniecMertensThetaErrorDensity_intervalIntegrable le_rfl (hx.trans hy))
    (iwaniecMertensThetaErrorDensity_intervalIntegrable le_rfl hx)

/-- The original natural-cutoff Mertens remainder, not a redefined
constant or error interface, is the endpoint term minus the actual tail. -/
theorem iwaniecPrimeReciprocalRemainder_theta_tail {N : Nat} (hN : 2 ≤ N) :
    Tendsto (fun y : Real =>
      (Chebyshev.theta N - (N : Real)) / ((N : Real) * Real.log N) -
        ∫ t in (N : Real)..y, (Chebyshev.theta t - t) * (1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))
      atTop (nhds (iwaniecPrimeReciprocalRemainder N)) := by
  have h := (tendsto_const_nhds (x := iwaniecMertensThetaBoundary (N : Real))).sub
    (iwaniecMertensTheta_tail_limit (x := (N : Real)) (by exact_mod_cast hN))
  rw [sub_sub_cancel, iwaniecMertensRealRemainder_nat] at h
  apply h.congr'
  filter_upwards with y
  unfold iwaniecMertensThetaBoundary
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  unfold iwaniecMertensThetaErrorDensity iwaniecMertensThetaKernel
  ring

/-- Literal RS 1962 (4.20), with the source improper integral expressed
by its defining cutoff limit and the lower tail endpoint x retained. -/
theorem iwaniecMertens_RS420_improper {x : Real} (hx : 2 ≤ x) :
    Tendsto (fun y : Real => Real.log (Real.log x) + Erdos696.Mertens.meisselMertensConstant +
      (Chebyshev.theta x - x) / (x * Real.log x) -
      ∫ t in x..y, (Chebyshev.theta t - t) * (1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))
      atTop (nhds (iwaniecPrimeReciprocalReal x)) := by
  have h := (tendsto_const_nhds (x := Real.log (Real.log x) + Erdos696.Mertens.meisselMertensConstant +
    iwaniecMertensThetaBoundary x)).sub (iwaniecMertensTheta_tail_limit hx)
  have he : Real.log (Real.log x) + Erdos696.Mertens.meisselMertensConstant + iwaniecMertensThetaBoundary x -
      (iwaniecMertensThetaBoundary x - iwaniecMertensRealRemainder x) = iwaniecPrimeReciprocalReal x := by
    unfold iwaniecMertensRealRemainder
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards with y
  unfold iwaniecMertensThetaBoundary
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  unfold iwaniecMertensThetaErrorDensity iwaniecMertensThetaKernel
  ring

end

end Erdos1212Kernel
