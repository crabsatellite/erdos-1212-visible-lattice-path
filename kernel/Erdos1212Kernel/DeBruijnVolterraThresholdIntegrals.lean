import Erdos1212Kernel.DeBruijnVolterraWindowMean

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijnVolterra_subinterval_integrable {g : Real → Real}
    (hg : ContinuousOn g (Set.Icc (0 : Real) 1)) {a b : Real}
    (ha : a ∈ Set.Icc (0 : Real) 1) (hb : b ∈ Set.Icc (0 : Real) 1) :
    IntervalIntegrable g volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hg.mono
  intro t ht
  exact ⟨(le_min ha.1 hb.1).trans ht.1, ht.2.trans (max_le ha.2 hb.2)⟩

def deBruijnRhoVolterraPrefix (x q : Real) : Real := ∫ t in (0 : Real)..q, deBruijnRhoVolterraKernel x t

theorem deBruijnRhoVolterraPrefix_lower {x q : Real} (hx : 1 ≤ x) (hq : q ∈ Set.Icc (0 : Real) 1) :
    q / x ≤ deBruijnRhoVolterraPrefix x q := by
  have hi := deBruijnVolterra_subinterval_integrable (deBruijnRhoVolterraKernel_continuousOn hx)
    (show (0 : Real) ∈ Set.Icc 0 1 by norm_num) hq
  have h := intervalIntegral.integral_mono_on hq.1 (_root_.intervalIntegrable_const (c := 1 / x)) hi
    (fun t ht => deBruijnRhoVolterraKernel_lower hx ⟨ht.1, ht.2.trans hq.2⟩)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, div_eq_mul_inv, one_mul] using h

theorem deBruijnVolterra_plain_gap_integral {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x a b : Real} (hx : 1 ≤ x)
    (ha : a ∈ Set.Icc (0 : Real) 1) (hb : b ∈ Set.Icc (0 : Real) 1) (c : Real) :
    (∫ t in a..b, c - f (x - t)) = c * (b - a) - ∫ t in a..b, f (x - t) := by
  rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const
    (deBruijnVolterra_subinterval_integrable (deBruijnRhoVolterra_lag_continuousOn hf hx) ha hb),
    intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem deBruijnVolterra_weighted_gap_integral {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x a b : Real} (hx : 1 ≤ x)
    (ha : a ∈ Set.Icc (0 : Real) 1) (hb : b ∈ Set.Icc (0 : Real) 1) (c : Real) :
    (∫ t in a..b, deBruijnRhoVolterraKernel x t * (c - f (x - t))) =
      c * (∫ t in a..b, deBruijnRhoVolterraKernel x t) - ∫ t in a..b, deBruijnRhoVolterraKernel x t * f (x - t) := by
  have hK := deBruijnRhoVolterraKernel_continuousOn hx
  have hF := deBruijnRhoVolterra_lag_continuousOn hf hx
  have hiK := deBruijnVolterra_subinterval_integrable hK ha hb
  have hiKF := deBruijnVolterra_subinterval_integrable (hK.mul hF) ha hb
  calc
    _ = ∫ t in a..b, deBruijnRhoVolterraKernel x t * c - deBruijnRhoVolterraKernel x t * f (x - t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = (∫ t in a..b, deBruijnRhoVolterraKernel x t * c) -
        ∫ t in a..b, deBruijnRhoVolterraKernel x t * f (x - t) := intervalIntegral.integral_sub (hiK.mul_const c) hiKF
    _ = _ := by rw [intervalIntegral.integral_mul_const]; ring

end

end Erdos1212Kernel
