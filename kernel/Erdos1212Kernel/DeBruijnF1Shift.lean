import Erdos1212Kernel.DeBruijnF1FamilyBounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnComplexExpAverage_continuous : Continuous deBruijnComplexExpAverage := by
  have hc : Continuous (fun p : Complex × Real => Complex.exp ((p.2 : Complex) * p.1)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst)
  have h : Continuous (fun z : Complex => ∫ t in Set.Icc (0 : Real) 1, Complex.exp ((t : Complex) * z)) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  have hfun : (fun z : Complex => ∫ t in Set.Icc (0 : Real) 1, Complex.exp ((t : Complex) * z)) =
      deBruijnComplexExpAverage := by
    funext z
    rw [deBruijnComplexExpAverage, intervalIntegral.integral_of_le (show (0 : Real) ≤ 1 by norm_num)]
    exact integral_Icc_eq_integral_Ioc
  rw [hfun] at h
  exact h

theorem deBruijnF1Integrand_joint_continuous :
    Continuous (fun p : Complex × Complex => deBruijnF1Integrand p.1 p.2) :=
  Complex.continuous_exp.comp ((continuous_fst.neg.mul continuous_snd).add
    (deBruijnComplexExpIntegral_continuous.comp continuous_snd))

theorem deBruijnF1_shift_joint_continuous (u : Complex) {r : Real → Complex} (hr : Continuous r) :
    Continuous (fun p : Real × Real => deBruijnF1Integrand (u - (p.1 : Complex)) (r p.2)) :=
  deBruijnF1Integrand_joint_continuous.comp
    ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).prodMk (hr.comp continuous_snd))

theorem deBruijnF1_shift_parameter_norm (u : Complex) {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    ‖u - (t : Complex)‖ ≤ ‖u‖ + 1 := by
  have hnorm : ‖(t : Complex)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have h := norm_sub_le u (t : Complex)
  rw [hnorm] at h
  linarith [ht.2]

theorem deBruijnF1Integrand_shift (u z : Complex) (t : Real) :
    deBruijnF1Integrand (u - (t : Complex)) z = Complex.exp ((t : Complex) * z) * deBruijnF1Integrand u z := by
  unfold deBruijnF1Integrand
  rw [← Complex.exp_add]
  congr 1
  ring

def deBruijnF1ShiftAverage (u z : Complex) : Complex := deBruijnComplexExpAverage z * deBruijnF1Integrand u z

theorem deBruijnF1ShiftAverage_eq_integral (u z : Complex) :
    deBruijnF1ShiftAverage u z = ∫ t in (0 : Real)..1, deBruijnF1Integrand (u - (t : Complex)) z := by
  calc
    _ = ∫ t in (0 : Real)..1, Complex.exp ((t : Complex) * z) * deBruijnF1Integrand u z := by
      rw [intervalIntegral.integral_mul_const]
      rfl
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact (deBruijnF1Integrand_shift u z t).symm

theorem deBruijnF1ShiftAverage_continuous (u : Complex) : Continuous (deBruijnF1ShiftAverage u) :=
  deBruijnComplexExpAverage_continuous.mul (deBruijnF1Integrand_continuous u)

def deBruijnF1SpatialFlux (u z : Complex) : Complex := (-u + deBruijnComplexExpAverage z) * deBruijnF1Integrand u z

theorem deBruijnF1SpatialFlux_eq (u z : Complex) :
    deBruijnF1SpatialFlux u z = -u * deBruijnF1Integrand u z + deBruijnF1ShiftAverage u z := by
  unfold deBruijnF1SpatialFlux deBruijnF1ShiftAverage
  ring

theorem deBruijnF1SpatialFlux_continuous (u : Complex) : Continuous (deBruijnF1SpatialFlux u) :=
  (continuous_const.add deBruijnComplexExpAverage_continuous).mul (deBruijnF1Integrand_continuous u)

end

end Erdos1212Kernel
