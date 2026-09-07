import Erdos1212Kernel.IwaniecMertensThetaKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem iwaniecMertensThetaKernel_intervalIntegrable {a b : Real} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable iwaniecMertensThetaKernel volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact iwaniecMertensThetaKernel_continuousOn.mono (fun x hx => (lt_min ha hb).trans_le hx.1)

theorem iwaniecLogKernel_deriv_integrableOn {x : Real} (hx : 2 ≤ x) :
    IntegrableOn (deriv iwaniecLogKernel) (Set.Icc (2 : Real) x) := by
  have hc : ContinuousOn (fun t => -iwaniecMertensThetaKernel t) (Set.Icc (2 : Real) x) :=
    (iwaniecMertensThetaKernel_continuousOn.mono (fun t ht => by change 1 < t; linarith [ht.1])).neg
  apply hc.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (iwaniecLogKernel_hasDerivAt (by linarith [ht.1] : 1 < t)).deriv.symm

theorem iwaniecTheta_weight_intervalIntegrable {a b : Real} (ha : 2 ≤ a) (hb : a ≤ b) :
    IntervalIntegrable (fun t => Chebyshev.theta t * iwaniecMertensThetaKernel t) volume a b := by
  have hwi : IntegrableOn iwaniecMertensThetaKernel (Set.Icc a b) :=
    (iwaniecMertensThetaKernel_continuousOn.mono (fun t ht => by change 1 < t; linarith [ht.1])).integrableOn_Icc
  have h := integrableOn_mul_sum_Icc iwaniecThetaPrimeCoefficient (m := 0) (show 0 ≤ a by linarith) hwi
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr
  apply h.congr_fun _ measurableSet_Icc
  intro t _ht
  dsimp only
  rw [iwaniecThetaPrimeCoefficient_sum]
  ring

/-- Literal RS 1962 (4.18), on the actual real prime cutoff and theta.
The proof is the source Abel substitution f(t)=1/t. -/
theorem iwaniecPrimeReciprocalReal_theta_formula {x : Real} (hx : 2 ≤ x) :
    iwaniecPrimeReciprocalReal x = Chebyshev.theta x / (x * Real.log x) +
      ∫ t in (2 : Real)..x, Chebyshev.theta t * iwaniecMertensThetaKernel t := by
  have h := sum_mul_eq_sub_integral_mul₁ iwaniecThetaPrimeCoefficient
    iwaniecThetaPrimeCoefficient_zero iwaniecThetaPrimeCoefficient_one x
    (fun t ht => (iwaniecLogKernel_hasDerivAt (by linarith [ht.1] : 1 < t)).differentiableAt)
    (iwaniecLogKernel_deriv_integrableOn hx)
  rw [← iwaniecPrimeReciprocalReal_weighted_theta, iwaniecThetaPrimeCoefficient_sum] at h
  have hi : (∫ t in Set.Ioc (2 : Real) x, deriv iwaniecLogKernel t *
      ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, iwaniecThetaPrimeCoefficient n) =
      -(∫ t in (2 : Real)..x, Chebyshev.theta t * iwaniecMertensThetaKernel t) := by
    rw [← intervalIntegral.integral_of_le hx, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    dsimp only
    rw [(iwaniecLogKernel_hasDerivAt (by linarith [ht.1] : 1 < t)).deriv, iwaniecThetaPrimeCoefficient_sum]
    ring
  rw [hi] at h
  rw [h]
  unfold iwaniecLogKernel
  ring

theorem iwaniecPrimeReciprocalSum_theta_formula {N : Nat} (hN : 2 ≤ N) :
    Erdos696.Mertens.primeReciprocalSum N = Chebyshev.theta N / ((N : Real) * Real.log N) +
      ∫ t in (2 : Real)..(N : Real), Chebyshev.theta t * iwaniecMertensThetaKernel t := by
  have h := iwaniecPrimeReciprocalReal_theta_formula (x := (N : Real)) (by exact_mod_cast hN)
  simpa only [iwaniecPrimeReciprocalReal_nat] using h

end

end Erdos1212Kernel
