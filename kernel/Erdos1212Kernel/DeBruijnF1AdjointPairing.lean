import Erdos1212Kernel.DeBruijnF1Comparison
import Erdos1212Kernel.DeBruijnAdjointEquation

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnF1G1Integrand (u : Real) : Real := deBruijnF1 u * deBruijn1951G1 u

def deBruijnF1G1Primitive (u : Real) : Real := ∫ x in (0 : Real)..u, deBruijnF1G1Integrand x

def deBruijnF1G1Pairing (a : Real) : Real :=
  (∫ u in (a - 1)..a, deBruijnF1 u * deBruijn1951G1 u) - a * deBruijnF1 a * deBruijn1951G1 (a - 1)

theorem deBruijnF1G1Integrand_continuousOn : ContinuousOn deBruijnF1G1Integrand (Set.Ioi (-1 : Real)) :=
  deBruijnF1_continuous.continuousOn.mul deBruijn1951G1_continuousOn

theorem deBruijnF1G1Integrand_intervalIntegrable {a b : Real} (ha : -1 < a) (hb : -1 < b) :
    IntervalIntegrable deBruijnF1G1Integrand volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact deBruijnF1G1Integrand_continuousOn.mono (fun x hx => (lt_min ha hb).trans_le hx.1)

theorem deBruijnF1G1Primitive_hasDerivAt {u : Real} (hu : -1 < u) :
    HasDerivAt deBruijnF1G1Primitive (deBruijnF1G1Integrand u) u :=
  intervalIntegral.integral_hasDerivAt_right (deBruijnF1G1Integrand_intervalIntegrable (by norm_num) hu)
    (deBruijnF1G1Integrand_continuousOn.stronglyMeasurableAtFilter isOpen_Ioi u hu)
    (deBruijnF1G1Integrand_continuousOn.continuousAt (Ioi_mem_nhds hu))

theorem deBruijnF1G1Pairing_eq_primitive {a : Real} (ha : 0 < a) :
    deBruijnF1G1Pairing a = deBruijnF1G1Primitive a - deBruijnF1G1Primitive (a - 1) -
      a * deBruijnF1 a * deBruijn1951G1 (a - 1) := by
  have hw := intervalIntegral.integral_interval_sub_left
    (deBruijnF1G1Integrand_intervalIntegrable (a := (0 : Real)) (by norm_num) (by linarith : -1 < a))
    (deBruijnF1G1Integrand_intervalIntegrable (a := (0 : Real)) (by norm_num) (by linarith : -1 < a - 1))
  change deBruijnF1G1Primitive a - deBruijnF1G1Primitive (a - 1) =
    ∫ u in (a - 1)..a, deBruijnF1G1Integrand u at hw
  rw [hw]
  rfl

theorem deBruijnF1G1Pairing_hasDerivAt {a : Real} (ha : 0 < a) : HasDerivAt deBruijnF1G1Pairing 0 a := by
  have hshift : HasDerivAt (fun x : Real => x - 1) 1 a := (hasDerivAt_id a).sub_const 1
  have hp := deBruijnF1G1Primitive_hasDerivAt (by linarith : -1 < a)
  have hn := (deBruijnF1G1Primitive_hasDerivAt (by linarith : -1 < a - 1)).comp a hshift
  have hF := deBruijnF1_hasDerivAt a
  have hG := (deBruijn1951G1_hasDerivAt (by linarith : -1 < a - 1)).comp a hshift
  have hraw := (hp.sub hn).sub (((hasDerivAt_id a).mul hF).mul hG)
  have hmodel : HasDerivAt (fun x : Real => deBruijnF1G1Primitive x - deBruijnF1G1Primitive (x - 1) -
      x * deBruijnF1 x * deBruijn1951G1 (x - 1)) 0 a := by
    apply hraw.congr_deriv
    simp only [Function.comp_apply, Pi.mul_apply, id_eq, one_mul, mul_one]
    have hd := deBruijnF1_delay_equation a
    rw [hF.deriv] at hd
    rw [hd]
    unfold deBruijnF1G1Integrand
    have hb := congrArg (fun y : Real => deBruijnF1 a * y) (deBruijn1951Adjoint_mass_balance ha)
    dsimp only at hb
    nlinarith
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with x hx
  exact deBruijnF1G1Pairing_eq_primitive hx

/-- Constancy of the original pairing for the actual F1 and G1. Its
value is not yet identified with 1; that requires the source saddle estimates. -/
theorem deBruijnF1G1Pairing_constant {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    deBruijnF1G1Pairing a = deBruijnF1G1Pairing b := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro x hx
    exact (deBruijnF1G1Pairing_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (deBruijnF1G1Pairing_hasDerivAt hx).deriv
  · exact ha
  · exact hb

end

end Erdos1212Kernel
