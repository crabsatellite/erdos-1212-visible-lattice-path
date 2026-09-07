import Erdos1212Kernel.TaoPhaseIncrementCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1500000

def taoShiftDifference (f : Real → Real) (h x : Real) : Real := f (x + h) - f x

theorem taoShiftDifference_subinterval {L U h x : Real} (hh : 0 ≤ h)
    (hx : x ∈ Set.Icc L (U - h)) : Set.Icc x (x + h) ⊆ Set.Icc L U := by
  intro t ht
  exact ⟨hx.1.trans ht.1, by linarith [hx.2, ht.2]⟩

theorem taoShiftDifference_hasDerivAt (f f' : Real → Real) {L U h x : Real} (hh : 0 ≤ h)
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t) (hx : x ∈ Set.Icc L (U - h)) :
    HasDerivAt (taoShiftDifference f h) (taoShiftDifference f' h x) x := by
  have hsub := taoShiftDifference_subinterval hh hx
  have hx0 := hsub (show x ∈ Set.Icc x (x + h) by constructor <;> linarith)
  have hx1 := hsub (show x + h ∈ Set.Icc x (x + h) by constructor <;> linarith)
  have hder := ((hf (x + h) hx1).comp x ((hasDerivAt_id x).add_const h)).sub (hf x hx0)
  simpa only [taoShiftDifference, Function.comp_apply, mul_one] using hder

/-- The literal fundamental-theorem identity used by Tao's differencing
step, on a subinterval of the original derivative domain. -/
theorem taoShiftDifference_eq_integral (f f' : Real → Real) {L U h x : Real} (hh : 0 ≤ h)
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Set.Icc L U)) (hx : x ∈ Set.Icc L (U - h)) :
    taoShiftDifference f h x = ∫ t in x..x + h, f' t := by
  have hsub := taoShiftDifference_subinterval hh hx
  have hle : x ≤ x + h := by linarith
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hf t (hsub ⟨ht.1.le, ht.2.le⟩))
    ((hc.mono hsub).intervalIntegrable_of_Icc hle)

/-- A continuous real derivative bounded away from zero cannot switch
sign inside the original connected interval. No sign is assumed. -/
theorem taoShiftDifference_derivative_sign (g : Real → Real) {L U δ : Real}
    (hδ : 0 < δ) (hc : ContinuousOn g (Set.Icc L U))
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |g t|) :
    (∀ t ∈ Set.Icc L U, δ ≤ g t) ∨ (∀ t ∈ Set.Icc L U, g t ≤ -δ) := by
  by_cases hp : ∀ t ∈ Set.Icc L U, 0 ≤ g t
  · left
    intro t ht
    simpa only [abs_of_nonneg (hp t ht)] using hlow t ht
  · push_neg at hp
    obtain ⟨y, hy, hyneg⟩ := hp
    right
    intro t ht
    have htneg : g t ≤ 0 := by
      by_contra htpos
      have htpos' : 0 < g t := lt_of_not_ge htpos
      obtain ⟨z, hz, hz0⟩ := isPreconnected_Icc.intermediate_value hy ht hc ⟨hyneg.le, htpos'.le⟩
      have hzlow := hlow z hz
      rw [hz0, abs_zero] at hzlow
      linarith
    have h := hlow t ht
    rw [abs_of_nonpos htneg] at h
    linarith

end

end Erdos1212Kernel
