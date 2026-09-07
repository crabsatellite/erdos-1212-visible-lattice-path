import Erdos1212Kernel.TaoInversePhaseDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

def taoPhaseIncrement (f : Real → Real) (x : Real) : Real := f (x + 1) - f x

def taoPhaseIncrementDerivative (f' : Real → Real) (x : Real) : Real := f' (x + 1) - f' x

theorem taoPhaseIncrement_subinterval {L U x : Real} (hx : x ∈ Set.Icc L (U - 1)) :
    Set.Icc x (x + 1) ⊆ Set.Icc L U := by
  intro t ht
  exact ⟨hx.1.trans ht.1, by linarith [hx.2, ht.2]⟩

/-- The mean-value point is inside the literal unit interval, so both
the upper and lower absolute derivative bounds apply without a sign choice. -/
theorem taoPhaseIncrement_derivative_value (f f' : Real → Real) {L U x : Real}
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t) (hx : x ∈ Set.Icc L (U - 1)) :
    ∃ c ∈ Set.Icc L U, f' c = taoPhaseIncrement f x := by
  have hsub := taoPhaseIncrement_subinterval hx
  have hc : ContinuousOn f (Set.Icc x (x + 1)) :=
    fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt
  obtain ⟨c, hcI, hcEq⟩ := exists_hasDerivAt_eq_slope f f' (by linarith : x < x + 1) hc
    (fun t ht => hf t (hsub ⟨ht.1.le, ht.2.le⟩))
  refine ⟨c, hsub ⟨hcI.1.le, hcI.2.le⟩, ?_⟩
  simpa only [show x + 1 - x = 1 by ring, div_one, taoPhaseIncrement] using hcEq

theorem taoPhaseIncrement_bounds (f f' : Real → Real) {L U x δ : Real}
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |f' t| ≤ 1 / 2) (hx : x ∈ Set.Icc L (U - 1)) :
    δ ≤ |taoPhaseIncrement f x| ∧ |taoPhaseIncrement f x| ≤ 1 / 2 := by
  obtain ⟨c, hc, hEq⟩ := taoPhaseIncrement_derivative_value f f' hf hx
  rw [← hEq]
  exact ⟨hlow c hc, hhigh c hc⟩

theorem taoPhaseIncrement_hasDerivAt (f f' : Real → Real) {L U x : Real}
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t) (hx : x ∈ Set.Icc L (U - 1)) :
    HasDerivAt (taoPhaseIncrement f) (taoPhaseIncrementDerivative f' x) x := by
  have hsub := taoPhaseIncrement_subinterval hx
  have hx0 := hsub (show x ∈ Set.Icc x (x + 1) by constructor <;> linarith)
  have hx1 := hsub (show x + 1 ∈ Set.Icc x (x + 1) by constructor <;> linarith)
  have h := ((hf (x + 1) hx1).comp x ((hasDerivAt_id x).add_const 1)).sub (hf x hx0)
  simpa only [taoPhaseIncrement, taoPhaseIncrementDerivative, Function.comp_apply, mul_one] using h

theorem taoPhaseIncrement_derivative_bound (f' f'' : Real → Real) {L U x D : Real}
    (hf' : ∀ t ∈ Set.Icc L U, HasDerivAt f' (f'' t) t)
    (hD : ∀ t ∈ Set.Icc L U, |f'' t| ≤ D) (hx : x ∈ Set.Icc L (U - 1)) :
    |taoPhaseIncrementDerivative f' x| ≤ D := by
  have hsub := taoPhaseIncrement_subinterval hx
  have hx0 := hsub (show x ∈ Set.Icc x (x + 1) by constructor <;> linarith)
  have hx1 := hsub (show x + 1 ∈ Set.Icc x (x + 1) by constructor <;> linarith)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hf' t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hD t ht)
    (convex_Icc L U) hx0 hx1
  simpa only [Real.norm_eq_abs, show x + 1 - x = 1 by ring, abs_one, mul_one, taoPhaseIncrementDerivative] using h

end

end Erdos1212Kernel
