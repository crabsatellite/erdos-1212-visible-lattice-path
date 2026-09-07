import Erdos1212Kernel.DeBruijnF1Convolution
import Erdos1212Kernel.DeBruijnVolterraSolutionLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def deBruijnF1Primitive (u : Real) : Real := ∫ x in (0 : Real)..u, deBruijnF1 x

theorem deBruijnF1Primitive_hasDerivAt (u : Real) :
    HasDerivAt deBruijnF1Primitive (deBruijnF1 u) u :=
  intervalIntegral.integral_hasDerivAt_right (deBruijnF1_continuous.intervalIntegrable 0 u)
    deBruijnF1_continuous.stronglyMeasurable.stronglyMeasurableAtFilter deBruijnF1_continuous.continuousAt

theorem deBruijnF1Primitive_window (u : Real) :
    deBruijnF1Primitive u - deBruijnF1Primitive (u - 1) = ∫ x in (u - 1)..u, deBruijnF1 x :=
  intervalIntegral.integral_interval_sub_left (deBruijnF1_continuous.intervalIntegrable 0 u)
    (deBruijnF1_continuous.intervalIntegrable 0 (u - 1))

theorem deBruijnF1_window (u : Real) :
    u * deBruijnF1 u = ∫ x in (u - 1)..u, deBruijnF1 x := by
  have h := deBruijnF1_convolution u
  rw [intervalIntegral.integral_comp_sub_left, sub_zero] at h
  exact h

theorem deBruijnF1_delay_equation (u : Real) :
    u * deriv deBruijnF1 u = -deBruijnF1 (u - 1) := by
  have hF := deBruijnF1_hasDerivAt u
  have hleft := (hasDerivAt_id u).mul hF
  have hshift : HasDerivAt (fun x : Real => x - 1) 1 u := (hasDerivAt_id u).sub_const 1
  have hraw := (deBruijnF1Primitive_hasDerivAt u).sub ((deBruijnF1Primitive_hasDerivAt (u - 1)).comp u hshift)
  simp only [mul_one] at hraw
  have hright : HasDerivAt (fun x : Real => x * deBruijnF1 x) (deBruijnF1 u - deBruijnF1 (u - 1)) u := by
    apply hraw.congr_of_eventuallyEq
    filter_upwards with x
    exact (deBruijnF1_window x).trans (deBruijnF1Primitive_window x).symm
  have h := hleft.unique hright
  simp only [id_eq, one_mul] at h
  rw [hF.deriv]
  linarith

/-- The actual constructed F1 now satisfies every premise of the proved
qualitative Volterra comparison. No convolution or convergence premise
is left in this endpoint. -/
theorem deBruijnF1_ratio_has_limit :
    ∃ C : Real, Tendsto (fun x : Real => deBruijnF1 x / deBruijnRho x) atTop (nhds C) :=
  deBruijnRhoSolutionRatio_has_limit deBruijnF1_continuous.continuousOn (fun x _hx => deBruijnF1_convolution x)

end

end Erdos1212Kernel
