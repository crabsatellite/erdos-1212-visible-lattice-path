import Erdos1212Kernel.IwaniecMertensThetaKernel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

def iwaniecRootLogDecay (a x : Real) : Real := Real.exp (-a * Real.sqrt (Real.log x))

def iwaniecRootLogDensity (a x : Real) : Real :=
  iwaniecRootLogDecay a x / (x * Real.sqrt (Real.log x))

theorem iwaniecRootLogDecay_pos (a x : Real) : 0 < iwaniecRootLogDecay a x := Real.exp_pos _

theorem iwaniecRootLogDensity_pos (a : Real) {x : Real} (hx : 1 < x) : 0 < iwaniecRootLogDensity a x := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  unfold iwaniecRootLogDensity
  exact div_pos (iwaniecRootLogDecay_pos a x) (mul_pos hx0 (Real.sqrt_pos.mpr hlog))

theorem iwaniecRootLogDensity_measurable (a : Real) : Measurable (iwaniecRootLogDensity a) := by
  unfold iwaniecRootLogDensity iwaniecRootLogDecay
  fun_prop

theorem tendsto_iwaniecRootLogDecay {a : Real} (ha : 0 < a) :
    Tendsto (iwaniecRootLogDecay a) atTop (nhds 0) := by
  have hs : Tendsto (fun x : Real => Real.sqrt (Real.log x)) atTop atTop := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hs.const_mul_atTop ha)
  apply h.congr'
  filter_upwards with x
  change Real.exp (-(a * Real.sqrt (Real.log x))) = Real.exp (-a * Real.sqrt (Real.log x))
  congr 1
  ring

theorem iwaniecRootLogDensity_hasPrimitive {a x : Real} (ha : 0 < a) (hx : 1 < x) :
    HasDerivAt (fun t : Real => (-2 / a) * iwaniecRootLogDecay a t) (iwaniecRootLogDensity a x) x := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  have hs := Real.sqrt_pos.mpr hlog
  have h := (((((Real.hasDerivAt_log hx0.ne').sqrt hlog.ne').const_mul (-a)).exp).const_mul (-2 / a))
  apply h.congr_deriv
  simp only [iwaniecRootLogDecay, iwaniecRootLogDensity]
  field_simp [ha.ne', hx0.ne', hs.ne']
  <;> ring

theorem iwaniecRootLogDensity_integrable {a x : Real} (ha : 0 < a) (hx : 1 < x) :
    IntegrableOn (iwaniecRootLogDensity a) (Set.Ioi x) := by
  have hlim := (tendsto_iwaniecRootLogDecay ha).const_mul (-2 / a)
  simp only [mul_zero] at hlim
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => iwaniecRootLogDensity_hasPrimitive ha (hx.trans_le ht))
    (fun t ht => (iwaniecRootLogDensity_pos a (hx.trans ht)).le) hlim

/-- Exact exponential tail integral, keeping the exponent coefficient a. -/
theorem iwaniecRootLogDensity_integral {a x : Real} (ha : 0 < a) (hx : 1 < x) :
    (∫ t in Set.Ioi x, iwaniecRootLogDensity a t) = (2 / a) * iwaniecRootLogDecay a x := by
  have hlim := (tendsto_iwaniecRootLogDecay ha).const_mul (-2 / a)
  simp only [mul_zero] at hlim
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t ht => iwaniecRootLogDensity_hasPrimitive ha (hx.trans_le ht))
    (fun t ht => (iwaniecRootLogDensity_pos a (hx.trans ht)).le) hlim
  simpa only [zero_sub, neg_div, neg_mul, neg_neg] using h

end

end Erdos1212Kernel
